use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::ffi::{c_uint, c_ulong};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::mpsc::Receiver;
use std::thread;
use std::time::{Duration, Instant};

use x11::keysym::XK_Escape;
use x11::xlib;
use x11::xrender;
use x11rb::connection::Connection;
use x11rb::properties::{WmSizeHints, WmSizeHintsSpecification};
use x11rb::protocol::Event;
use x11rb::protocol::randr;
use x11rb::protocol::shape::{ConnectionExt as ShapeConnectionExt, SK, SO};
use x11rb::protocol::xinput::{self, ConnectionExt as InputConnectionExt};
use x11rb::protocol::xkb::{self, ConnectionExt as _};
use x11rb::protocol::xproto::{
    AtomEnum, ButtonIndex, ButtonPressEvent, CONFIGURE_NOTIFY_EVENT, ChangeWindowAttributesAux,
    ClientMessageEvent, ClipOrdering, ColormapAlloc, ConfigWindow, ConfigureNotifyEvent,
    ConfigureWindowAux, ConnectionExt, CreateWindowAux, EnterNotifyEvent, EventMask, FocusInEvent,
    GrabMode, GrabStatus, Gravity, InputFocus, KeyPressEvent, LeaveNotifyEvent, ModMask,
    MotionNotifyEvent, PropMode, StackMode, Window, WindowClass,
};
use x11rb::rust_connection::RustConnection;
use x11rb::wrapper::ConnectionExt as _;
use x11rb::{CURRENT_TIME, NONE};

use crate::bar::{
    BAR_BACKGROUND_PIXEL, BAR_TRANSPARENT_PIXEL, BARGAP, CLIENT_ICON_LEFT_PAD, CLIENT_ICON_SIZE,
    CLIENT_ICON_SPACING, CLOCKPAD, CursorLoader, HORIZPADBAR, KBLAYOUTPAD, LAUNCHERS,
    LAYOUT_SYMBOL, Metrics, SYSTRAY_SPACING, TAG_LABEL, TAGS, TRAY_ICON_MAX, TRAY_ICON_MIN,
    VERTPADBAR,
};
use crate::config::{
    self, BORDERPX, FLOATBAR, TOPBAR, TRAY_MENUS_ABOVE_BAR,
};
use crate::drw::Drw;
use crate::finder::Finder;
use crate::keys::{self, Action, GapScope, Key, MOD_4, TAG_COUNT, TAGMASK};
use crate::tree::{self, Gaps, Node, Rect};

pub type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

const LOCK_MASK: u16 = 1 << 1;
const MOD2_MASK: u16 = 1 << 4;
/// dwm's CLEANMASK: every modifier except CapsLock and NumLock (Mod2 here).
const CLEAN_MASK: u16 = 0xFD & !MOD2_MASK;
/// ICCCM `WM_STATE` values. The atom is interned in `Atoms` (it is not one of
/// X11's predefined atoms); only these numbers are fixed by the spec.
const WM_STATE_WITHDRAWN: u32 = 0;
const WM_STATE_NORMAL: u32 = 1;
const WM_STATE_ICONIC: u32 = 3;

/// Pointer motion throttle during a drag, matching dwm's `1000 / 60`.
const DRAG_FRAME: Duration = Duration::from_millis(16);
/// The one cadence for every animated bar value. Clock levels and scrolling
/// titles advance on this same grid, so redraws never come from two timers
/// with different phases. 1000 / 60 rounded up to whole microseconds.
const BAR_TICK: Duration = Duration::from_micros(16_667);
/// `poll()` has millisecond resolution, so accept a wakeup up to 1 ms early.
/// Otherwise a 16 ms return skips the next 16.67 ms slot and halves the rate.
const TICK_GRACE: Duration = Duration::from_millis(1);
/// Slow fallback for wakeups that only background threads can cause (PipeWire
/// levels and MPRIS snapshots). Used when no bar animation is active.
const IDLE_POLL: Duration = Duration::from_millis(500);
/// While the pointer is on a fullscreen monitor the bar is not mapped, so none
/// of the 60 fps bar work is needed. Wake only this slowly to drain D-Bus
/// notifications (delivered over a channel, not an X event) before they can
/// pile up and pop up on resume.
const FULLSCREEN_IDLE_POLL: Duration = Duration::from_millis(500);
/// Scrolling title moves one pixel every two bar ticks (~33 ms). A separate
/// timer used to fire between ticks and produced uneven redraw gaps.
const SCROLL_TICKS: u32 = 2;
/// Don't repaint the MPRIS panel until the interpolated progress bar would
/// move by about a pixel. This replaces the old once-per-second Position poll.
const PROGRESS_EPSILON: f32 = 0.005;
/// Space left around a centered dialog so it does not touch the screen edges.
const FLOAT_MARGIN: i32 = 20;
/// Default outer size for a floating window that publishes no size hints.
const DEFAULT_FLOAT_W: i32 = 600;
const DEFAULT_FLOAT_H: i32 = 400;

/// The parts of `WM_NORMAL_HINTS` dwm's `updatesizehints()` keeps, plus the
/// position/size a client asked for. Zero means "not specified", as in the C
/// version. Sizes are client sizes, without the border, because that is what
/// `constrain_size()` operates on.
#[derive(Clone, Copy, Debug, Default)]
struct SizeHints {
    min_w: i32,
    min_h: i32,
    max_w: i32,
    max_h: i32,
    base_w: i32,
    base_h: i32,
    inc_w: i32,
    inc_h: i32,
    min_aspect: f64,
    max_aspect: f64,
    /// USPosition/PPosition: the requested position of the reference point
    /// selected by `gravity`.
    requested_pos: Option<(i32, i32)>,
    /// True for USPosition (an explicit user choice), false for PPosition.
    user_position: bool,
    /// USSize/PSize: the requested client size.
    requested_size: Option<(i32, i32)>,
    gravity: Option<Gravity>,
}

/// Offset from a hint's reference point to the top-left of the window, as
/// selected by `PWinGravity` (ICCCM 4.1.2.3). Most clients use NorthWest.
fn gravity_offset(gravity: Option<Gravity>, w: i32, h: i32) -> (i32, i32) {
    match gravity {
        Some(g) if g == Gravity::NORTH => (w / 2, 0),
        Some(g) if g == Gravity::NORTH_EAST => (w, 0),
        Some(g) if g == Gravity::WEST => (0, h / 2),
        Some(g) if g == Gravity::CENTER => (w / 2, h / 2),
        Some(g) if g == Gravity::EAST => (w, h / 2),
        Some(g) if g == Gravity::SOUTH_WEST => (0, h),
        Some(g) if g == Gravity::SOUTH => (w / 2, h),
        Some(g) if g == Gravity::SOUTH_EAST => (w, h),
        _ => (0, 0),
    }
}

/// Top-left corner that centers a `w`x`h` box in `area`, clamped so the whole
/// box stays inside it.
fn centered_in(area: Rect, w: i32, h: i32) -> (i32, i32) {
    let max_x = (area.x + area.w as i32 - w).max(area.x);
    let max_y = (area.y + area.h as i32 - h).max(area.y);
    (
        (area.x + (area.w as i32 - w) / 2).clamp(area.x, max_x),
        (area.y + (area.h as i32 - h) / 2).clamp(area.y, max_y),
    )
}

/// Pick one axis of the initial client size. A client may ask for a size, or
/// merely publish its base size; fall back to a modest dialog size otherwise.
fn hinted_axis(
    requested: Option<i32>,
    base: i32,
    min: i32,
    max: i32,
    inc: i32,
    fallback: i32,
) -> i32 {
    let mut v = requested.filter(|v| *v > 0).unwrap_or(base);
    if v <= 0 {
        v = fallback;
    }
    v = v.max(min).max(1);
    if max > 0 {
        v = v.min(max);
    }
    if inc > 0 {
        let anchor = base.clamp(1, v);
        v = anchor + ((v - anchor) / inc) * inc;
        v = v.max(min).max(1);
        if max > 0 {
            v = v.min(max);
        }
    }
    v
}

/// Initial outer geometry of a floating client. A client-requested position
/// that belongs to this monitor wins; a stale one from another monitor falls
/// back to centering on the transient parent or the monitor's work area.
fn floating_geometry(hints: &SizeHints, area: Rect, parent: Option<Rect>, border: i32) -> Rect {
    let avail_w = (area.w as i32 - 2 * FLOAT_MARGIN).max(1);
    let avail_h = (area.h as i32 - 2 * FLOAT_MARGIN).max(1);
    let cw = hinted_axis(
        hints.requested_size.map(|(w, _)| w),
        hints.base_w,
        hints.min_w,
        hints.max_w,
        hints.inc_w,
        DEFAULT_FLOAT_W.min(avail_w),
    );
    let ch = hinted_axis(
        hints.requested_size.map(|(_, h)| h),
        hints.base_h,
        hints.min_h,
        hints.max_h,
        hints.inc_h,
        DEFAULT_FLOAT_H.min(avail_h),
    );
    let mut rect = constrain_size(
        hints,
        Rect {
            x: 0,
            y: 0,
            w: (cw + 2 * border).max(1) as u32,
            h: (ch + 2 * border).max(1) as u32,
        },
        border,
        0,
    );
    rect.w = rect.w.min(avail_w.max(2 * border + 1) as u32);
    rect.h = rect.h.min(avail_h.max(2 * border + 1) as u32);

    // ICCCM distinguishes a weak PPosition ("program specified") from a strong
    // USPosition ("user specified"). Toolkits routinely publish PPosition=(0,0)
    // as a placeholder, and Electron-style clients may compute a real one for
    // a different monitor (or before the screens were arranged). Trust a user
    // position always, but only trust a program position that lands on this
    // monitor; anything else centers here instead of being clamped to an edge.
    let explicit_pos = hints.requested_pos.filter(|(x, y)| {
        if *x == 0 && *y == 0 && !hints.user_position {
            return false;
        }
        hints.user_position || area.contains(*x, *y)
    });
    let (x, y) = if let Some((hx, hy)) = explicit_pos {
        let (ox, oy) = gravity_offset(hints.gravity, rect.w as i32, rect.h as i32);
        (hx - ox, hy - oy)
    } else {
        centered_in(parent.unwrap_or(area), rect.w as i32, rect.h as i32)
    };
    let max_x = (area.x + area.w as i32 - rect.w as i32).max(area.x);
    let max_y = (area.y + area.h as i32 - rect.h as i32).max(area.y);
    Rect {
        x: x.clamp(area.x, max_x),
        y: y.clamp(area.y, max_y),
        w: rect.w,
        h: rect.h,
    }
}

/// The outer frame is the X border around a client. Fullscreen clients cover
/// the whole monitor, so they get no frame at all.
fn client_border(c: &Client) -> i32 {
    if c.fullscreen { 0 } else { BORDERPX }
}

/// dwm's `applysizehints()`: clamp a floating client's outer box to the hints
/// it published. Tiled clients keep the layout's size, as with dwm's
/// `resizehints = 0`.
fn constrain_size(hints: &SizeHints, rect: Rect, border: i32, min_bar_height: i32) -> Rect {
    let mut w = (rect.w as i32 - 2 * border).max(1);
    let mut h = (rect.h as i32 - 2 * border).max(1);
    w = w.max(min_bar_height);
    h = h.max(min_bar_height);

    let base_is_min = hints.base_w == hints.min_w && hints.base_h == hints.min_h;
    if !base_is_min {
        w -= hints.base_w;
        h -= hints.base_h;
    }
    if hints.min_aspect > 0.0 && hints.max_aspect > 0.0 {
        if hints.max_aspect < w as f64 / h as f64 {
            w = (h as f64 * hints.max_aspect + 0.5) as i32;
        } else if hints.min_aspect < h as f64 / w as f64 {
            h = (w as f64 * hints.min_aspect + 0.5) as i32;
        }
    }
    if base_is_min {
        w -= hints.base_w;
        h -= hints.base_h;
    }
    if hints.inc_w > 0 {
        w -= w % hints.inc_w;
    }
    if hints.inc_h > 0 {
        h -= h % hints.inc_h;
    }
    w = (w + hints.base_w).max(hints.min_w).max(1);
    h = (h + hints.base_h).max(hints.min_h).max(1);
    if hints.max_w > 0 {
        w = w.min(hints.max_w);
    }
    if hints.max_h > 0 {
        h = h.min(hints.max_h);
    }

    Rect {
        x: rect.x,
        y: rect.y,
        w: (w + 2 * border).max(2 * border + 1) as u32,
        h: (h + 2 * border).max(2 * border + 1) as u32,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WinType {
    Normal,
    Dialog,
    Utility,
    Toolbar,
    Menu,
    DropdownMenu,
    PopupMenu,
    Tooltip,
    Notification,
    Splash,
    Dock,
    Desktop,
    Combo,
    Dnd,
}

/// Menus, context popups and tooltips. These are the windows a tray app maps
/// when its icon is clicked; they are override-redirect far more often than
/// regular client windows.
fn is_popup_win_type(t: WinType) -> bool {
    matches!(
        t,
        WinType::Menu | WinType::DropdownMenu | WinType::PopupMenu | WinType::Tooltip
    )
}

/// ICCCM `WM_NORMAL_HINTS` with min == max on both axes leave the WM no legal
/// resize: tiling such a window would only fight its hints. Zero means "not
/// specified", so it is not a fixed size. This is deliberately app-agnostic:
/// any client publishing the same hints gets the same treatment.
fn has_fixed_size(hints: &SizeHints) -> bool {
    config::FLOAT_FIXED_SIZE
        && hints.min_w > 0
        && hints.min_h > 0
        && hints.max_w == hints.min_w
        && hints.max_h == hints.min_h
}

/// Floating policy shared by map time and later property updates. EWMH
/// dialog-like window types, transient/modal windows and fixed-size windows
/// stay outside the tiling tree. Fixed size is the fallback for clients that
/// never set `_NET_WM_WINDOW_TYPE`, as EWMH leaves the rest to the WM.
fn wants_floating(
    win_type: WinType,
    transient_for: Option<Window>,
    is_modal: bool,
    hints: &SizeHints,
) -> bool {
    matches!(
        win_type,
        WinType::Dialog
            | WinType::Utility
            | WinType::Toolbar
            | WinType::Menu
            | WinType::DropdownMenu
            | WinType::PopupMenu
            | WinType::Tooltip
            | WinType::Notification
            | WinType::Splash
    ) || transient_for.is_some()
        || is_modal
        || has_fixed_size(hints)
}

/// Whether an automatic property update may change a client's floating mode.
/// A manual Super+W toggle takes precedence for the rest of the window's
/// lifetime: GTK4 clients in particular refresh `WM_NORMAL_HINTS` right after
/// a resize, and re-running the policy on that notification would immediately
/// undo the user's choice. Without a manual choice, only apply a real change.
fn should_apply_float_policy(user_choice: Option<bool>, policy: bool, current: bool) -> bool {
    user_choice.is_none() && policy != current
}

/// The map state we last told X to put a client in. `pending_unmaps` counts
/// UnmapNotify events from our own UnmapWindow requests that have not arrived
/// yet; an UnmapNotify with no such event outstanding came from the client.
#[derive(Clone, Copy, Default)]
struct MapTracking {
    mapped: bool,
    pending_unmaps: u32,
    /// Last iconic value published to the client. `None` until the first sync,
    /// so an adopted unmapped client still gets an IconicState property. Used
    /// to avoid rewriting both state properties on every layout pass.
    published_iconic: Option<bool>,
}

impl MapTracking {
    /// True when an UnmapWindow request must be sent. X emits no UnmapNotify
    /// for a window that is already unmapped, so do not count those.
    fn unmap(&mut self) -> bool {
        if !self.mapped {
            return false;
        }
        self.mapped = false;
        self.pending_unmaps += 1;
        true
    }

    /// A remap does not consume a pending unmap event: the event is still in
    /// the queue and still belongs to the WM's earlier request.
    fn map(&mut self) {
        self.mapped = true;
    }

    /// True when this UnmapNotify came from the client and should iconify it.
    fn consume_unmap(&mut self) -> bool {
        if self.pending_unmaps > 0 {
            self.pending_unmaps -= 1;
            return false;
        }
        if self.mapped {
            self.mapped = false;
            return true;
        }
        false
    }
}

pub struct Client {
    pub win: Window,
    pub tags: u32,
    pub mon: usize,
    /// dwm's `isfloating`: a floating window is outside the tiling tree.
    pub floating: bool,
    /// Set by Super+W. An explicit user choice outranks the automatic
    /// floating policy, so a later property update cannot undo it.
    float_override: Option<bool>,
    /// Monotonic stacking token. Adoption and fullscreen/floating changes take
    /// a new token, so an overlay opened after a fullscreen request stays on
    /// top of it while the next fullscreen request covers the overlay again.
    stack_seq: u64,
    /// Temporarily outside the tiling tree while Super+drag moves it. Its tree
    /// leaf stays in place, so siblings expand until the drop reinserts it.
    dragging: bool,
    /// The outer box of a floating window, like dwm's `x`, `y`, `w` and `h`.
    pub geom: Rect,
    /// True while the WM still owns the floating geometry. Client or user
    /// placement clears it so later property updates do not move the window.
    auto_place: bool,
    /// dwm's `minw`, `basew`, `incw`, aspect and friends from `WM_NORMAL_HINTS`.
    hints: SizeHints,
    /// The input-only hover zones over the window's edges and corners, in the
    /// order of `tree::ZONE_EDGES`.
    pub edge_wins: [Window; 8],
    pub transient_for: Option<Window>,
    pub win_type: WinType,
    pub is_modal: bool,
    pub fullscreen: bool,
    pub maximized_horz: bool,
    pub maximized_vert: bool,
    pub above: bool,
    pub below: bool,
    pub demands_attention: bool,
    pub hidden: bool,
    pub sticky: bool,
    pub skip_taskbar: bool,
    pub skip_pager: bool,
    pub saved_geom: Option<Rect>,
    pub saved_floating: bool,
    pub take_focus: bool,
    pub wants_input: bool,
    pub urgent: bool,
}

/// Resize cursors from the user's cursor theme. `0` is `None`.
#[derive(Clone, Copy)]
struct ResizeCursors {
    moving: u32,
    horizontal: u32,
    vertical: u32,
    top_left: u32,
    top_right: u32,
    bottom_left: u32,
    bottom_right: u32,
}

/// The resize cursors, named as in AnDWM's `dwm.c` `init cursors`.
fn create_resize_cursors(cursors: &CursorLoader) -> ResizeCursors {
    ResizeCursors {
        moving: cursors.load("fleur"),
        horizontal: cursors.load("sb_h_double_arrow"),
        vertical: cursors.load("sb_v_double_arrow"),
        top_left: cursors.load("top_left_corner"),
        top_right: cursors.load("top_right_corner"),
        bottom_left: cursors.load("bottom_left_corner"),
        bottom_right: cursors.load("bottom_right_corner"),
    }
}

pub struct Monitor {
    pub rect: Rect,
    /// dwm's `wx`, `wy`, `ww`, `wh` and `by`, set by `update_bar_pos`.
    pub wx: i32,
    pub wy: i32,
    pub ww: i32,
    pub wh: i32,
    pub by: i32,
    pub tree: Option<Node>,
    /// dwm's `gappoh`, `gappov`, `gappih` and `gappiv` for this monitor.
    pub gaps: Gaps,
    pub tagset: [u32; 2],
    pub seltags: usize,
    pub curtag: usize,
    pub prevtag: usize,
    pub showbar: bool,
    pub showbars: [bool; TAGS + 1],
    pub sel: Option<Window>,
    pub barwin: Window,
    pub bartitlewin: Window,
    pub barkbwin: Window,
    pub barcenterwin: Window,
    pub barrightwin: Window,
    pub mpris_markerwin: Window,
    pub finder_markerwin: Window,
    /// Per-monitor bar colormap, freed at shutdown.
    colormap: u32,
    /// dwm's cached finder-marker stacking and last configured position.
    finder_marker_stacked: Cell<bool>,
    finder_marker_pos: Cell<Option<(i32, i32)>>,
    /// Cached result of the last `stack_finder()` call. Restacking the popup and
    /// marker while the pointer is over the marker generates crossing events,
    /// which used to feed back into another restack and make both flicker.
    finder_stacked: Cell<bool>,
}

/// dwm's `barwidths()` output.
struct BarWidths {
    tw: i32,
    tlw: i32,
    cw: i32,
    kw: i32,
    rw: i32,
}

/// x of a center window drawn `drawn_w` wide in the gap between the right edge
/// of the title (`left`) and the left edge of the right bar (`right`). `cw` is
/// the width the bar reserved for it; the window can be wider while the audio
/// meter animates. The reserve keeps a `BARGAP` on either side, as in dwm's
/// `resizebarwin()`.
fn centered_bar_x(left: i32, right: i32, cw: i32, drawn_w: i32) -> Option<i32> {
    if right - left < cw + 2 * BARGAP {
        return None;
    }
    Some(left + (right - left) / 2 - drawn_w / 2)
}

/// Who owns the shared center window. The WM_CLASS differs for each kind,
/// and Finder takes precedence over an already-open notification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CenterKind {
    Dwm,
    Notification,
    History,
    Finder,
}

/// The last click on a tray icon, used to associate a window the app maps in
/// response with its icon. Toolkits don't agree on a hint for this: Qt uses
/// `WM_TRANSIENT_FOR`, GTK mostly uses a popup window type, and some apps set
/// neither. WM_CLASS plus a short grace period covers the last case.
struct TrayClick {
    at: Instant,
    class: Option<(String, String)>,
}

/// How long after a tray click a newly mapped window may still be adopted as
/// that icon's menu. Long enough for slow toolkits, short enough that an
/// unrelated window opened a second later is left alone.
const TRAY_MENU_GRACE: Duration = Duration::from_secs(2);

#[derive(Clone)]
struct Atoms {
    wm_protocols: u32,
    wm_delete: u32,
    wm_take_focus: u32,
    wm_state: u32,
    wm_change_state: u32,
    wm_transient_for: u32,
    net_wm_name: u32,
    net_wm_icon: u32,
    net_wm_window_type: u32,
    net_wm_window_type_dialog: u32,
    net_wm_window_type_utility: u32,
    net_wm_window_type_toolbar: u32,
    net_wm_window_type_menu: u32,
    net_wm_window_type_dropdown_menu: u32,
    net_wm_window_type_popup_menu: u32,
    net_wm_window_type_tooltip: u32,
    net_wm_window_type_notification: u32,
    net_wm_window_type_splash: u32,
    net_wm_window_type_dock: u32,
    net_wm_window_type_desktop: u32,
    net_wm_state: u32,
    net_wm_state_fullscreen: u32,
    net_wm_state_above: u32,
    net_wm_state_below: u32,
    net_wm_state_modal: u32,
    net_wm_state_demands_attention: u32,
    net_wm_state_hidden: u32,
    net_wm_state_sticky: u32,
    net_wm_state_skip_taskbar: u32,
    net_wm_state_skip_pager: u32,
    net_wm_state_maximized_vert: u32,
    net_wm_state_maximized_horz: u32,
    net_active_window: u32,
    net_client_list: u32,
    net_client_list_stacking: u32,
    net_supported: u32,
    net_supporting_wm_check: u32,
    net_wm_desktop: u32,
    net_wm_allowed_actions: u32,
    net_wm_ping: u32,
    net_close_window: u32,
    net_move_resize_window: u32,
    net_request_frame_extents: u32,
    net_workarea: u32,
    net_wm_strut: u32,
    net_wm_strut_partial: u32,
    net_showing_desktop: u32,
    net_number_of_desktops: u32,
    net_current_desktop: u32,
    net_desktop_names: u32,
    utf8_string: u32,
    motif_wm_hints: u32,
    no_animation: u32,
    rwm_monitor: u32,
    manager: u32,
    net_system_tray_opcode: u32,
    net_system_tray_orientation: u32,
    net_system_tray_visual: u32,
    xembed: u32,
    xembed_info: u32,
    targets: u32,
}

pub struct Wm {
    pub conn: RustConnection,
    pub root: Window,
    pub monitors: Vec<Monitor>,
    /// Newest first, like dwm's client list. Its order is the focus and move order.
    pub clients: Vec<Client>,
    /// Last stacking token handed out by `next_stack_seq`.
    stack_seq: u64,
    /// Iconified clients in the order they were unmapped. `Deiconify` pops the
    /// newest, so any number of windows can be hidden and restored one by one.
    iconified_stack: Vec<Window>,
    /// The WM's view of each managed client's X map state, including unmap
    /// events we still owe from our own UnmapWindow requests. Those events are
    /// not a withdraw; any other UnmapNotify means the client unmapped itself
    /// (e.g. closing to the tray) and must be treated as iconification.
    client_maps: RefCell<HashMap<Window, MapTracking>>,
    pub selmon: usize,
    keys: Vec<Key>,
    keysyms: Vec<u32>,
    min_keycode: u8,
    max_keycode: u8,
    atoms: Atoms,
    /// Text measuring for the layout, on the same Xlib display as `drw`.
    metrics: Metrics,
    /// Xlib/Xft/XRender drawing, like C dwm's `drw`.
    drw: Drw,
    /// Last clock window state, so animation only repaints when it changes.
    clock_drawn: RefCell<HashMap<Window, (i32, i32, i32, String, bool)>>,
    visual_id: u32,
    depth: u8,
    /// dwm's `finder_argb_visual`/`finder_argb_depth`/`finder_argb_colormap`:
    /// the 32-bit alpha visual used only by each monitor's center clock window.
    /// A zero `finder_argb_visual` means no ARGB visual is available (or ARGB
    /// creation failed), so the center window uses the root visual like the
    /// rest of the bar.
    finder_argb_visual: u32,
    finder_argb_depth: u8,
    finder_argb_colormap: u32,
    /// Same visual as `finder_argb_visual`, as the Xlib pointer needed to make
    /// an XRender picture for the 32-bit window.
    finder_argb_visual_ptr: *mut xlib::Visual,
    clock: String,
    /// Shared PipeWire RMS for the animated clock width. It is sampled in the
    /// main loop instead of a separate fixed-cadence thread, so there is no
    /// second 60 Hz wakeup just to publish one atomic.
    clock_level: Option<crate::sound::Level>,
    /// Smoothed adaptive gain applied to the level before the dBFS mapping.
    clock_gain: f32,
    /// Last time the level was sampled, on the shared `BAR_TICK` grid.
    clock_anim_last: Instant,
    /// dwm's `clockbar_dynw` minus `clockbar_cw`: px the clock bar grows past
    /// its text width on the selected monitor.
    clock_extra: i32,
    /// Freedesktop system tray: selection owner and the docked XEMBED icons.
    tray: crate::tray::Tray,
    /// Windows opened from a tray icon that must stay stacked above the bar.
    /// Both popup windows and full client windows the app opens from the icon
    /// can land here; only the stacking is changed, never their layout.
    tray_menus: RefCell<Vec<Window>>,
    /// Override-redirect menus, context popups and tooltips opened by ordinary
    /// clients. They are not managed, so X will not keep them above a client
    /// that is mapped or raised later. Only stacking is touched here.
    popup_windows: RefCell<Vec<Window>>,
    /// Other unmanaged override-redirect root children (hintless popups, OSDs).
    /// They are kept above clients but below the always-on-top bar layer.
    overlay_windows: RefCell<Vec<Window>>,
    /// Most recent ButtonPress delivered to a tray icon or the tray container.
    tray_click: RefCell<Option<TrayClick>>,
    /// Typed top-right bar values and `kbstr` (keyboard layout).
    bar_status: crate::status::Status,
    kbstr: String,
    /// Set by an event that may change what the bar shows. Window motion and
    /// client configure events deliberately do not set it.
    bar_dirty: bool,
    /// True while the pointer's monitor shows a fullscreen window. The timed
    /// bar tick (visualizer, status, scrolling titles and repaints) is suspended
    /// then; named refreshes still run so entering and leaving fullscreen is
    /// drawn exactly once. The PipeWire sampler is paused along with it.
    bar_suspended: bool,
    /// Exposed bar windows must repaint even when their contents are unchanged.
    /// Only these windows are forced, as in dwm's per-monitor `expose()`.
    force_windows: RefCell<HashSet<Window>>,
    /// Bar windows currently mapped. Map/unmap requests are only sent when the
    /// desired state changes, not on every frame.
    bar_mapped: RefCell<HashSet<Window>>,
    /// Last drawing key committed to each bar window. An unchanged section is
    /// not copied again, so an idle frame sends no X requests at all.
    bar_drawn: RefCell<HashMap<Window, String>>,
    /// Whether each monitor's clock window is currently mapped. A remap must
    /// repaint it even if its text and geometry match the cache.
    center_shown: RefCell<Vec<bool>>,
    /// Last names read from clients, so frame builds don't need round trips.
    name_cache: RefCell<HashMap<Window, String>>,
    /// Decoded `_NET_WM_ICON` pixels of the title bar's icons. `None` is cached
    /// too, so clients without the property are not polled every frame.
    icon_cache: RefCell<HashMap<Window, Option<crate::icon::ClientIcon>>>,
    /// Monotonic version handed to decoded icons, used in draw keys and caches.
    icon_seq: Cell<u64>,
    /// Last geometry sent to each managed window, so unchanged layouts cost no
    /// configure requests. The last field is the border width.
    geom_cache: RefCell<HashMap<Window, (i32, i32, u32, u32, u32)>>,
    /// Resize zones owned by this WM. Only newly exposed zones need mapping.
    mapped_zones: RefCell<HashSet<Window>>,
    status: crate::status::StatusSampler,
    mpris_rx: Receiver<crate::mpris::Snapshot>,
    mpris: crate::mpris::Snapshot,
    mpris_scroll_text: String,
    /// Last progress value sent to the bar, for change detection without an
    /// MPRIS Position poll.
    last_progress: Option<f32>,
    mpris_scroll_px: u32,
    /// Earliest tick at which the scrolling title may advance. Keeping a
    /// deadline instead of an accumulator locks scrolling to the bar grid.
    mpris_scroll_next: Instant,
    mpris_hovered: bool,
    mpris_marker_hovered: bool,
    mpris_volume_drag: bool,
    mpris_marker_rect: Option<(i32, i32, i32, i32)>,
    /// Whether each monitor's top-right bar was raised above client windows for
    /// the expanded MPRIS panel, so it can be lowered again when the panel
    /// collapses.
    mpris_bar_raised: RefCell<Vec<bool>>,
    /// First event code of the XKB extension, or 0 when it is unavailable.
    xkb_event_base: u8,
    /// dwm's `enablegaps`, toggled by `ToggleGaps`.
    gaps_enabled: bool,
    resize_cursors: ResizeCursors,
    /// Hand cursor for the clickable tag/workspace strip.
    tag_cursor: u32,
    /// Modal application launcher, including its GL/presentation resources.
    finder: Finder,
    /// Freedesktop notifications and AnDWM's hover history, drawn through the
    /// same center ARGB window as Finder.
    notification: crate::notification::NotificationManager,
    /// Fullscreen state of the selected monitor, tracked so entering fullscreen
    /// clears the popup exactly once like dwm's `updatefullscreenstatus`.
    notification_fullscreen: bool,
    /// Last center-window owner observed by `refresh`. Pointer events can close
    /// history before `refresh` starts, so this remembers that a repaint of the
    /// normal clock is needed even when the manager already reports inactive.
    notification_center_active_last: bool,
    /// Set when the center window was remapped under a live notification, so a
    /// cached GL frame is not treated as already presented on the new window.
    notification_force: Cell<bool>,
    /// Last WM_CLASS written to each center window.
    center_kind: RefCell<Vec<CenterKind>>,
    /// Whether this WM currently owns the modal keyboard and root pointer grabs.
    finder_grabbed: bool,
    /// X input focus captured before Finder opened. Finder keeps focus on its
    /// popup while active, then restores this window when it closes.
    finder_saved_focus: Option<Window>,
    /// Last X input focus rwm deliberately requested. FocusIn on a different
    /// window means a client (or an X focus revert) moved the keyboard without
    /// going through the selection, so focus() puts it back. This keeps the
    /// border colour, _NET_ACTIVE_WINDOW and what picom sees in agreement.
    intended_focus: Option<Window>,
    /// True while a pointer grab drives a move/resize. Crossings forwarded
    /// through handle() must not reselect a window under the dragged client.
    pointer_grabbed: bool,
    /// Until this instant an EnterNotify must not change the selection. An
    /// explicit focus such as Alt+Tab warps the pointer, and that synthetic
    /// crossing can otherwise select a window stacked over the target.
    focus_hold_until: Instant,
    /// Keeps the Xlib connection that owns the themed cursor ids alive.
    _cursor_loader: CursorLoader,
    /// EWMH's _NET_SUPPORTING_WM_CHECK window. It is an unmapped child of the
    /// root, so the startup scan would adopt it as a client without this.
    supporting_wm_check: Window,
    pub restart: bool,
}

/// Spawn `child` in its own session, like dwm's `fork(); setsid(); exec()`.
///
/// `Command::spawn()` forks already, but without `setsid()` the app remains in
/// rwm's session and process group. Signals sent to that group (for example
/// when rwm is killed from its terminal) take the app down with it. `pre_exec`
/// runs in the forked child just before exec, where detaching is still safe.
pub fn spawn_command(mut child: Command) -> Result {
    unsafe {
        child.pre_exec(|| {
            libc::signal(libc::SIGCHLD, libc::SIG_DFL);
            if libc::setsid() == -1 {
                // A spawn() child is never a process-group leader, but keep a
                // process-group boundary even if setsid() fails somehow.
                if libc::setpgid(0, 0) == -1 {
                    return Err(std::io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
    let mut child = child.spawn()?;
    // Reap the detached child without blocking the WM event loop.
    thread::spawn(move || {
        let _ = child.wait();
    });
    Ok(())
}

/// Each argument (and every `Spawn` keybinding) is a shell command run in a
/// separate session so it outlives rwm.
pub fn spawn(cmd: &str) -> Result {
    let mut child = Command::new("sh");
    child.arg("-c").arg(cmd);
    spawn_command(child)
}

/// Bar windows use the root visual and depth, like C dwm. `Drw` creates its
/// offscreen pixmap with the same visual so `XCopyArea` is a plain blit.
fn bar_visual(conn: &RustConnection, root: Window) -> Result<(u32, u8)> {
    let screen = conn
        .setup()
        .roots
        .iter()
        .find(|screen| screen.root == root)
        .ok_or("root screen not found")?;
    Ok((screen.root_visual, screen.root_depth))
}

/// dwm.c 17075-17097: find a 32-bit TrueColor visual whose XRender format has
/// an alpha mask, and create a colormap for it. Returns `(visual_id, depth,
/// colormap, visual)` or `None` when the server has no suitable ARGB visual, in
/// which case the center clock window falls back to the root visual and depth.
/// The `Visual` pointer stays valid for the lifetime of the Xlib display and is
/// needed to build the XRender picture used to paint the window.
fn bar_visual_argb(
    dpy: *mut xlib::Display,
    root: Window,
    screen: i32,
) -> Option<(u32, u8, u32, *mut xlib::Visual)> {
    unsafe {
        let mut template: xlib::XVisualInfo = std::mem::zeroed();
        template.screen = screen;
        template.depth = 32;
        template.class = xlib::TrueColor;
        let mut nvisuals = 0;
        let visuals = xlib::XGetVisualInfo(
            dpy,
            xlib::VisualScreenMask | xlib::VisualDepthMask | xlib::VisualClassMask,
            &mut template,
            &mut nvisuals,
        );
        if visuals.is_null() {
            return None;
        }
        let mut found = None;
        for i in 0..nvisuals as usize {
            let info = &*visuals.add(i);
            let format = xrender::XRenderFindVisualFormat(dpy, info.visual);
            if format.is_null()
                || (*format).type_ != xrender::PictTypeDirect
                || (*format).direct.alphaMask == 0
            {
                continue;
            }
            let colormap =
                xlib::XCreateColormap(dpy, root as xlib::Window, info.visual, xlib::AllocNone);
            if colormap == 0 {
                continue;
            }
            found = Some((
                info.visualid as u32,
                info.depth as u8,
                colormap as u32,
                info.visual,
            ));
            break;
        }
        xlib::XFree(visuals.cast());
        // x11rb creates the ARGB window on a *different* connection. Xlib
        // buffers XCreateColormap, so flush it before that connection can use
        // the id, otherwise the server answers CreateWindow with BadColor.
        xlib::XFlush(dpy);
        found
    }
}

fn now_clock() -> String {
    unsafe {
        let t = libc::time(std::ptr::null_mut());
        let mut tm: libc::tm = std::mem::zeroed();
        libc::localtime_r(&t, &mut tm);
        format!("{:02}:{:02}", tm.tm_hour, tm.tm_min)
    }
}

impl Wm {
    pub fn new(
        conn: RustConnection,
        root: Window,
        rects: Vec<Rect>,
        min_keycode: u8,
        max_keycode: u8,
    ) -> Result<Wm> {
        conn.change_window_attributes(
            root,
            &ChangeWindowAttributesAux::new().event_mask(
                EventMask::SUBSTRUCTURE_REDIRECT
                    | EventMask::SUBSTRUCTURE_NOTIFY
                    | EventMask::KEY_PRESS
                    | EventMask::PROPERTY_CHANGE
                    | EventMask::POINTER_MOTION
                    | EventMask::FOCUS_CHANGE,
            ),
        )?
        .check()?;

        // Core ButtonPress is exclusive per window: an icon that selects it for
        // its own menu stops the event from reaching the WM. XI2 has no such
        // restriction, so watch button presses on the root and use the pointer
        // position to detect clicks on the tray without stealing the app's
        // click. Older servers without XI2 simply lose this one heuristic;
        // transient_for and window type still identify most menus.
        if TRAY_MENUS_ABOVE_BAR
            && conn
                .xinput_xi_query_version(2, 0)
                .ok()
                .and_then(|c| c.reply().ok())
                .is_some()
        {
            let _ = conn.xinput_xi_select_events(
                root,
                &[xinput::EventMask {
                    deviceid: 0,
                    mask: vec![xinput::XIEventMask::BUTTON_PRESS],
                }],
            );
        }

        let intern =
            |name: &[u8]| -> Result<u32> { Ok(conn.intern_atom(false, name)?.reply()?.atom) };
        let atoms = Atoms {
            wm_protocols: intern(b"WM_PROTOCOLS")?,
            wm_delete: intern(b"WM_DELETE_WINDOW")?,
            wm_take_focus: intern(b"WM_TAKE_FOCUS")?,
            wm_state: intern(b"WM_STATE")?,
            wm_change_state: intern(b"WM_CHANGE_STATE")?,
            wm_transient_for: intern(b"WM_TRANSIENT_FOR")?,
            net_wm_name: intern(b"_NET_WM_NAME")?,
            net_wm_icon: intern(b"_NET_WM_ICON")?,
            net_wm_window_type: intern(b"_NET_WM_WINDOW_TYPE")?,
            net_wm_window_type_dialog: intern(b"_NET_WM_WINDOW_TYPE_DIALOG")?,
            net_wm_window_type_utility: intern(b"_NET_WM_WINDOW_TYPE_UTILITY")?,
            net_wm_window_type_toolbar: intern(b"_NET_WM_WINDOW_TYPE_TOOLBAR")?,
            net_wm_window_type_menu: intern(b"_NET_WM_WINDOW_TYPE_MENU")?,
            net_wm_window_type_dropdown_menu: intern(b"_NET_WM_WINDOW_TYPE_DROPDOWN_MENU")?,
            net_wm_window_type_popup_menu: intern(b"_NET_WM_WINDOW_TYPE_POPUP_MENU")?,
            net_wm_window_type_tooltip: intern(b"_NET_WM_WINDOW_TYPE_TOOLTIP")?,
            net_wm_window_type_notification: intern(b"_NET_WM_WINDOW_TYPE_NOTIFICATION")?,
            net_wm_window_type_splash: intern(b"_NET_WM_WINDOW_TYPE_SPLASH")?,
            net_wm_window_type_dock: intern(b"_NET_WM_WINDOW_TYPE_DOCK")?,
            net_wm_window_type_desktop: intern(b"_NET_WM_WINDOW_TYPE_DESKTOP")?,
            net_wm_state: intern(b"_NET_WM_STATE")?,
            net_wm_state_fullscreen: intern(b"_NET_WM_STATE_FULLSCREEN")?,
            net_wm_state_above: intern(b"_NET_WM_STATE_ABOVE")?,
            net_wm_state_below: intern(b"_NET_WM_STATE_BELOW")?,
            net_wm_state_modal: intern(b"_NET_WM_STATE_MODAL")?,
            net_wm_state_demands_attention: intern(b"_NET_WM_STATE_DEMANDS_ATTENTION")?,
            net_wm_state_hidden: intern(b"_NET_WM_STATE_HIDDEN")?,
            net_wm_state_sticky: intern(b"_NET_WM_STATE_STICKY")?,
            net_wm_state_skip_taskbar: intern(b"_NET_WM_STATE_SKIP_TASKBAR")?,
            net_wm_state_skip_pager: intern(b"_NET_WM_STATE_SKIP_PAGER")?,
            net_wm_state_maximized_vert: intern(b"_NET_WM_STATE_MAXIMIZED_VERT")?,
            net_wm_state_maximized_horz: intern(b"_NET_WM_STATE_MAXIMIZED_HORZ")?,
            net_active_window: intern(b"_NET_ACTIVE_WINDOW")?,
            net_client_list: intern(b"_NET_CLIENT_LIST")?,
            net_client_list_stacking: intern(b"_NET_CLIENT_LIST_STACKING")?,
            net_supported: intern(b"_NET_SUPPORTED")?,
            net_supporting_wm_check: intern(b"_NET_SUPPORTING_WM_CHECK")?,
            net_wm_desktop: intern(b"_NET_WM_DESKTOP")?,
            net_wm_allowed_actions: intern(b"_NET_WM_ALLOWED_ACTIONS")?,
            net_wm_ping: intern(b"_NET_WM_PING")?,
            net_close_window: intern(b"_NET_CLOSE_WINDOW")?,
            net_move_resize_window: intern(b"_NET_MOVERESIZE_WINDOW")?,
            net_request_frame_extents: intern(b"_NET_REQUEST_FRAME_EXTENTS")?,
            net_workarea: intern(b"_NET_WORKAREA")?,
            net_wm_strut: intern(b"_NET_WM_STRUT")?,
            net_wm_strut_partial: intern(b"_NET_WM_STRUT_PARTIAL")?,
            net_showing_desktop: intern(b"_NET_SHOWING_DESKTOP")?,
            net_number_of_desktops: intern(b"_NET_NUMBER_OF_DESKTOPS")?,
            net_current_desktop: intern(b"_NET_CURRENT_DESKTOP")?,
            net_desktop_names: intern(b"_NET_DESKTOP_NAMES")?,
            utf8_string: intern(b"UTF8_STRING")?,
            motif_wm_hints: intern(b"_MOTIF_WM_HINTS")?,
            no_animation: intern(b"_NO_ANIMATION")?,
            rwm_monitor: intern(b"_RWM_MONITOR")?,
            manager: intern(b"MANAGER")?,
            net_system_tray_opcode: intern(b"_NET_SYSTEM_TRAY_OPCODE")?,
            net_system_tray_orientation: intern(b"_NET_SYSTEM_TRAY_ORIENTATION")?,
            net_system_tray_visual: intern(b"_NET_SYSTEM_TRAY_VISUAL")?,
            xembed: intern(b"_XEMBED")?,
            xembed_info: intern(b"_XEMBED_INFO")?,
            targets: intern(b"TARGETS")?,
        };

        let (visual_id, depth) = bar_visual(&conn, root)?;

        let mut monitors = Vec::new();
        for rect in rects {
            monitors.push(Monitor {
                wx: rect.x,
                wy: rect.y,
                ww: rect.w as i32,
                wh: rect.h as i32,
                by: 0,
                rect,
                tree: None,
                gaps: Gaps {
                    oh: config::GAPPOH,
                    ov: config::GAPPOV,
                    ih: config::GAPPIH,
                    iv: config::GAPPIV,
                },
                tagset: [1, 1],
                seltags: 0,
                curtag: 1,
                prevtag: 1,
                showbar: true,
                showbars: [true; TAGS + 1],
                sel: None,
                barwin: 0,
                bartitlewin: 0,
                barkbwin: 0,
                barcenterwin: 0,
                barrightwin: 0,
                mpris_markerwin: 0,
                finder_markerwin: 0,
                colormap: 0,
                finder_marker_stacked: Cell::new(false),
                finder_marker_pos: Cell::new(None),
                finder_stacked: Cell::new(false),
            });
        }

        let keys = keys::bindings();
        let count = (max_keycode - min_keycode + 1) as usize;
        let map = conn
            .get_keyboard_mapping(min_keycode, count as u8)?
            .reply()?;
        let per = map.keysyms_per_keycode as usize;
        let keysyms = (0..count).map(|i| map.keysyms[i * per]).collect();

        let mpris_rx = crate::mpris::start_monitor();
        let mpris = crate::mpris::Snapshot::default();
        let notification_handle = match crate::notification::start_service() {
            Ok(handle) => handle,
            Err(err) => {
                eprintln!("rwm: notification service unavailable: {err}");
                None
            }
        };
        let mut status = crate::status::StatusSampler::new();
        let bar_status = status.sample_with_mpris(Some(&mpris));
        let cursor_loader = CursorLoader::open()?;
        let resize_cursors = create_resize_cursors(&cursor_loader);
        let tag_cursor = cursor_loader.load("pointer");
        conn.change_window_attributes(
            root,
            &ChangeWindowAttributesAux::new().cursor(cursor_loader.load("left_ptr")),
        )?;
        // Fonts, cursors and every bar pixel use this one Xlib connection, the
        // same way C dwm shares a single `Display *dpy` for all drawing.
        let dpy = cursor_loader.display();
        let screen = cursor_loader.screen();
        // Discover the ARGB visual on the Xlib display, like dwm's setup block.
        // It is used only by the center clock window; everything else keeps
        // the root visual selected by `bar_visual` above.
        let (finder_argb_visual, finder_argb_depth, finder_argb_colormap, finder_argb_visual_ptr) =
            if config::FINDER_ARGB {
                bar_visual_argb(dpy, root, screen).unwrap_or((0, 0, 0, std::ptr::null_mut()))
            } else {
                (0, 0, 0, std::ptr::null_mut())
            };
        let metrics = Metrics::new(dpy, screen)?;
        let drw = Drw::new(dpy, screen, root as x11::xlib::Window)?;
        let clock_level = if config::CLOCK_ANIMATE {
            Some(crate::sound::start())
        } else {
            None
        };
        let monitor_count = monitors.len();
        // Use the root visual for the tray. An ARGB visual would look nicer,
        // but already-running apps (Discord included) create their icon
        // windows on the 24-bit root visual and XReparentWindow rejects a
        // depth mismatch.
        let (tray_visual, tray_depth) = (visual_id, depth);
        let tray = crate::tray::Tray::new(
            &conn,
            root,
            crate::tray::Atoms {
                manager: atoms.manager,
                opcode: atoms.net_system_tray_opcode,
                orientation: atoms.net_system_tray_orientation,
                visual: atoms.net_system_tray_visual,
                xembed: atoms.xembed,
                xembed_info: atoms.xembed_info,
                targets: atoms.targets,
            },
            cursor_loader.screen(),
            tray_visual,
            tray_depth,
            BAR_BACKGROUND_PIXEL,
        )?;
        let mut wm = Wm {
            conn,
            root,
            monitors,
            clients: Vec::new(),
            stack_seq: 0,
            iconified_stack: Vec::new(),
            client_maps: RefCell::new(HashMap::new()),
            selmon: 0,
            keys,
            keysyms,
            min_keycode,
            max_keycode,
            atoms,
            metrics,
            drw,
            clock_drawn: RefCell::new(HashMap::new()),
            visual_id,
            depth,
            finder_argb_visual,
            finder_argb_depth,
            finder_argb_colormap,
            finder_argb_visual_ptr,
            clock: now_clock(),
            clock_level,
            clock_gain: 1.0,
            clock_anim_last: Instant::now() - BAR_TICK,
            clock_extra: 0,
            tray,
            tray_menus: RefCell::new(Vec::new()),
            popup_windows: RefCell::new(Vec::new()),
            overlay_windows: RefCell::new(Vec::new()),
            tray_click: RefCell::new(None),
            bar_status,
            kbstr: "us".to_string(),
            bar_dirty: true,
            bar_suspended: false,
            force_windows: RefCell::new(HashSet::new()),
            bar_mapped: RefCell::new(HashSet::new()),
            bar_drawn: RefCell::new(HashMap::new()),
            center_shown: RefCell::new(vec![false; monitor_count]),
            name_cache: RefCell::new(HashMap::new()),
            icon_cache: RefCell::new(HashMap::new()),
            icon_seq: Cell::new(0),
            geom_cache: RefCell::new(HashMap::new()),
            mapped_zones: RefCell::new(HashSet::new()),
            status,
            mpris_rx,
            mpris,
            mpris_scroll_text: String::new(),
            last_progress: None,
            mpris_scroll_px: 0,
            mpris_scroll_next: Instant::now(),
            mpris_hovered: false,
            mpris_marker_hovered: false,
            mpris_volume_drag: false,
            mpris_marker_rect: None,
            mpris_bar_raised: RefCell::new(vec![false; monitor_count]),
            xkb_event_base: 0,
            gaps_enabled: true,
            resize_cursors,
            tag_cursor,
            finder: Finder::new(),
            notification: crate::notification::NotificationManager::new(notification_handle),
            notification_fullscreen: false,
            notification_center_active_last: false,
            notification_force: Cell::new(false),
            center_kind: RefCell::new(vec![CenterKind::Dwm; monitor_count]),
            finder_grabbed: false,
            finder_saved_focus: None,
            intended_focus: None,
            pointer_grabbed: false,
            focus_hold_until: Instant::now(),
            _cursor_loader: cursor_loader,
            supporting_wm_check: NONE,
            restart: false,
        };
        // Initialize the notification GL state before the first D-Bus event.
        // Popup geometry comes from measured GL text, so a lazy init would size
        // the first notification to the 1px placeholder and never grow it.
        if !finder_argb_visual_ptr.is_null() {
            if let Err(err) = wm.notification.prepare(dpy, screen, finder_argb_visual_ptr) {
                eprintln!("rwm: notification GL unavailable: {err}");
            }
        }
        wm.tray.claim(&wm.conn, wm.root)?;
        wm.set_bar_window_class(wm.tray.window)?;
        wm.conn.change_property32(
            PropMode::REPLACE,
            root,
            wm.atoms.net_number_of_desktops,
            AtomEnum::CARDINAL,
            &[TAG_COUNT],
        )?;
        wm.update_current_desktop(wm.tags_of(0))?;
        wm.update_bars()?;
        wm.arrange()?;
        wm.grab_keys(max_keycode)?;
        wm.init_xkb();
        wm.init_randr();
        wm.setup_ewmh()?;
        // Apps that started before this WM (or before the last restart) do not
        // resend their one-shot dock request. Adopt their XEMBED windows now,
        // before the normal client scan can mistake them for clients.
        let scanned = wm.tray.scan_existing(&wm.conn, wm.root)?;
        if scanned > 0 {
            wm.relayout_tray()?;
        }
        wm.scan_existing_windows()?;
        wm.conn.flush()?;
        Ok(wm)
    }

    /// Listen for RandR screen and monitor changes so monitor geometry can be
    /// reinitialized when resolution or layout changes (e.g. via xrandr).
    fn init_randr(&self) {
        let _ = randr::select_input(
            &self.conn,
            self.root,
            randr::NotifyMask::SCREEN_CHANGE
                | randr::NotifyMask::CRTC_CHANGE
                | randr::NotifyMask::OUTPUT_CHANGE,
        );
    }

    /// dwm's setup block: select Xkb StateNotify and read the layout once.
    fn init_xkb(&mut self) {
        // Xlib calls XkbUseExtension automatically during XOpenDisplay. x11rb
        // does not, and without that negotiation XKB requests fail with Access.
        let supported = self
            .conn
            .xkb_use_extension(1, 0)
            .ok()
            .and_then(|c| c.reply().ok())
            .is_some_and(|r| r.supported);
        if !supported {
            return;
        }
        // The XKB extension registers itself as "XKEYBOARD". Querying "XKB"
        // returns present=0 on this server, which made us skip event selection
        // entirely, so group-only switches never reached the bar.
        let (present, first_event) = self
            .conn
            .query_extension(xkb::X11_EXTENSION_NAME.as_bytes())
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| (r.present, r.first_event))
            .unwrap_or((false, 0));
        if !present {
            return;
        }
        let group_parts = u16::from(xkb::StatePart::GROUP_STATE)
            | u16::from(xkb::StatePart::GROUP_BASE)
            | u16::from(xkb::StatePart::GROUP_LATCH)
            | u16::from(xkb::StatePart::GROUP_LOCK);
        let aux = xkb::SelectEventsAux::new().state_notify(xkb::SelectEventsAuxStateNotify {
            affect_state: xkb::StatePart::from(group_parts),
            state_details: xkb::StatePart::from(group_parts),
        });
        let selected = match self.conn.xkb_select_events(
            xkb::ID::USE_CORE_KBD.into(),
            xkb::EventType::default(),
            // x11rb derives `affect_which` from `details`. Passing
            // STATE_NOTIFY here too means "select all details", which
            // conflicts with the per-event details in `aux` and panics
            // while serializing.
            xkb::EventType::default(),
            xkb::MapPart::default(),
            xkb::MapPart::default(),
            &aux,
        ) {
            Ok(cookie) => cookie.check().is_ok(),
            Err(_) => false,
        };
        if selected {
            self.xkb_event_base = first_event;
        }
        self.update_kb();
    }

    fn update_kb(&mut self) {
        let atom = self
            .conn
            .intern_atom(true, b"_XKB_RULES_NAMES")
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| r.atom)
            .unwrap_or(NONE);
        if atom != NONE {
            let prop = self
                .conn
                .get_property(false, self.root, atom, AtomEnum::STRING, 0, 1024)
                .ok()
                .and_then(|c| c.reply().ok())
                .filter(|r| r.format == 8 && !r.value.is_empty());
            if let Some(r) = prop {
                // rules\0model\0layout\0variant\0options
                let bytes = &r.value;
                let mut p = 0;
                let mut entry = 0;
                let mut layout_start = None;
                while p < bytes.len() && bytes[p] != 0 && entry < 3 {
                    if entry == 2 {
                        layout_start = Some(p);
                        break;
                    }
                    while p < bytes.len() && bytes[p] != 0 {
                        p += 1;
                    }
                    p += 1;
                    entry += 1;
                }
                if let Some(start) = layout_start {
                    let end = bytes[start..]
                        .iter()
                        .position(|&b| b == 0)
                        .map(|n| start + n)
                        .unwrap_or(bytes.len());
                    let layouts = String::from_utf8_lossy(&bytes[start..end]).into_owned();
                    let group = self
                        .conn
                        .xkb_get_state(xkb::ID::USE_CORE_KBD.into())
                        .ok()
                        .and_then(|c| c.reply().ok())
                        .map(|r| u8::from(r.group) as usize)
                        .unwrap_or(0);
                    if let Some(token) = layouts.split(',').nth(group)
                        && token.len() < 16
                    {
                        self.kbstr = token.to_string();
                    }
                }
            }
        }
        if self.kbstr.is_empty() {
            self.kbstr = "us".to_string();
        }
    }

    fn setup_ewmh(&mut self) -> Result {
        // _NET_SUPPORTING_WM_CHECK
        let check_win = self.conn.generate_id()?;
        self.conn.create_window(
            self.depth,
            check_win,
            self.root,
            0,
            0,
            1,
            1,
            0,
            WindowClass::INPUT_OUTPUT,
            self.visual_id,
            &CreateWindowAux::new(),
        )?;
        self.conn.change_property32(
            PropMode::REPLACE,
            check_win,
            self.atoms.net_supporting_wm_check,
            AtomEnum::WINDOW,
            &[check_win],
        )?;
        self.conn.change_property8(
            PropMode::REPLACE,
            check_win,
            AtomEnum::WM_NAME,
            self.atoms.utf8_string,
            b"rwm",
        )?;
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_supporting_wm_check,
            AtomEnum::WINDOW,
            &[check_win],
        )?;
        self.supporting_wm_check = check_win;
        // _NET_SUPPORTED (advertise a subset we care about)
        let supported = [
            self.atoms.net_supported,
            self.atoms.net_supporting_wm_check,
            self.atoms.net_client_list,
            self.atoms.net_client_list_stacking,
            self.atoms.net_active_window,
            self.atoms.net_wm_name,
            self.atoms.net_wm_window_type,
            self.atoms.net_wm_state,
            self.atoms.net_wm_state_fullscreen,
            self.atoms.net_wm_state_maximized_vert,
            self.atoms.net_wm_state_maximized_horz,
            self.atoms.net_wm_desktop,
            self.atoms.net_current_desktop,
            self.atoms.net_number_of_desktops,
            self.atoms.net_workarea,
            self.atoms.net_close_window,
        ];
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_supported,
            AtomEnum::ATOM,
            &supported,
        )?;
        Ok(())
    }

    fn grab_keys(&self, max_keycode: u8) -> Result {
        self.conn.ungrab_key(0u8, self.root, ModMask::ANY)?;
        for key in &self.keys {
            for kc in self.min_keycode..=max_keycode {
                let sym = self.keysyms[(kc - self.min_keycode) as usize];
                if sym != key.keysym {
                    continue;
                }
                for extra in [0, LOCK_MASK, MOD2_MASK, LOCK_MASK | MOD2_MASK] {
                    self.conn.grab_key(
                        true,
                        self.root,
                        ModMask::from(key.mods | extra),
                        kc,
                        GrabMode::ASYNC,
                        GrabMode::ASYNC,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn refresh_keysyms(&mut self) -> Result {
        let count = (self.max_keycode - self.min_keycode + 1) as usize;
        let map = self
            .conn
            .get_keyboard_mapping(self.min_keycode, count as u8)?
            .reply()?;
        let per = map.keysyms_per_keycode as usize;
        self.keysyms = (0..count)
            .map(|i| map.keysyms.get(i * per).copied().unwrap_or(0))
            .collect();
        self.grab_keys(self.max_keycode)?;
        self.conn.flush()?;
        self.refresh_xlib_keymap();
        Ok(())
    }

    /// `event_keysym()` uses the Xlib Display from `Drw`. Xlib caches the
    /// keyboard mapping, so a live `setxkbmap` would leave it translating with
    /// the old US table even though x11rb and the bar see the new layout.
    fn refresh_xlib_keymap(&self) {
        let dpy = self.drw.dpy();
        if dpy.is_null() {
            return;
        }
        let mut event: xlib::XMappingEvent = unsafe { std::mem::zeroed() };
        event.type_ = xlib::MappingNotify;
        event.display = dpy;
        event.request = xlib::MappingKeyboard;
        event.first_keycode = self.min_keycode as i32;
        event.count = (self.max_keycode - self.min_keycode + 1) as i32;
        unsafe {
            xlib::XRefreshKeyboardMapping(&mut event);
        }
    }

    /// Keysym for a key press in the layout the user is actually typing in.
    ///
    /// `keysyms` caches the first keysym of each keycode (group 0), which is
    /// what WM bindings are grabbed with. An XKB group switch does not emit a
    /// core MappingNotify, so that cache stays US even when the rest of the
    /// system has switched to Thai. Text input has to follow the group carried
    /// in the event state instead, or Finder and notification fields keep
    /// typing English while every other app accepts Thai.
    fn event_keysym(&self, e: &KeyPressEvent) -> u32 {
        let dpy = self.drw.dpy();
        if !dpy.is_null() {
            let mut consumed: c_uint = 0;
            let mut sym: c_ulong = 0;
            // XLookupKeysym ignores the group bits in the event state (its
            // index selects group 0/1), which is exactly why Finder stayed in
            // English. XkbLookupKeySym translates keycode + full event state,
            // so the active group is honoured.
            let ok = unsafe {
                xlib::XkbLookupKeySym(dpy, e.detail, u32::from(e.state), &mut consumed, &mut sym)
            };
            if ok != 0 && sym != 0 {
                return sym as u32;
            }
        }
        self.keysyms
            .get(usize::from(e.detail.saturating_sub(self.min_keycode)))
            .copied()
            .unwrap_or(0)
    }

    /// Adopt existing top-level windows (startup scan).
    ///
    /// Map state must not be used as a filter here: the previous WM unmaps
    /// windows on workspaces other than the one it was showing, so those
    /// clients would never be registered and would stay unmapped forever even
    /// after switching to their workspace. Adopt every non-override-redirect
    /// child and keep the workspace recorded in `_NET_WM_DESKTOP` so hidden
    /// clients stay hidden until their workspace is selected.
    fn scan_existing_windows(&mut self) -> Result {
        let reply = match self.conn.query_tree(self.root) {
            Ok(c) => match c.reply() {
                Ok(r) => r,
                Err(_) => return Ok(()),
            },
            Err(_) => return Ok(()),
        };
        // Collect our own windows to avoid managing them. The EWMH check window
        // is not override-redirect and not mapped, so it needs an explicit entry.
        let mut ours = std::collections::HashSet::new();
        for m in &self.monitors {
            ours.insert(m.barwin);
            ours.insert(m.bartitlewin);
            ours.insert(m.barcenterwin);
            ours.insert(m.barkbwin);
            ours.insert(m.barrightwin);
            ours.insert(m.mpris_markerwin);
            ours.insert(m.finder_markerwin);
        }
        ours.insert(self.supporting_wm_check);
        ours.insert(self.tray.window);
        // A previous WM that does not publish _NET_WM_DESKTOP (vanilla dwm is
        // one) leaves hidden windows with no record of their workspace. Keep
        // them off the workspace selected now instead of dumping them all
        // there; the next tag is an arbitrary but stable landing place where
        // they can be found and mapped later.
        let pointer = self
            .conn
            .query_pointer(self.root)
            .ok()
            .and_then(|c| c.reply().ok());
        let mi = pointer
            .map(|p| self.monitor_at(p.root_x as i32, p.root_y as i32))
            .unwrap_or(self.selmon);
        let cur = self.tags_of(mi);
        let offscreen_tags = if cur.count_ones() == 1 {
            let next = (cur.trailing_zeros() as usize + 1) % TAG_COUNT as usize;
            1u32 << next
        } else {
            1u32 << 1
        };
        for &win in &reply.children {
            if ours.contains(&win) || self.is_managed(win) {
                continue;
            }
            let attrs = match self.conn.get_window_attributes(win) {
                Ok(c) => match c.reply() {
                    Ok(a) => a,
                    Err(_) => continue,
                },
                Err(_) => continue,
            };
            if attrs.override_redirect || attrs.class == WindowClass::INPUT_ONLY {
                continue;
            }
            if self.should_ignore_window(win) {
                let _ = self.conn.configure_window(
                    win,
                    &x11rb::protocol::xproto::ConfigureWindowAux::new().border_width(0),
                );
                continue;
            }
            let hidden = attrs.map_state != x11rb::protocol::xproto::MapState::VIEWABLE;
            let tags = self
                .read_net_wm_desktop(win)
                .and_then(Self::desktop_to_tags)
                .or_else(|| hidden.then_some(offscreen_tags));
            let initial_mon = self
                .read_rwm_monitor(win)
                .and_then(|r| self.monitor_for_saved_rect(r));
            let _ = self.manage_on(win, tags, initial_mon);
        }
        Ok(())
    }

    fn grab_buttons(&self, win: Window) -> Result {
        self.conn
            .ungrab_button(ButtonIndex::ANY, win, ModMask::ANY)?;
        for button in [ButtonIndex::M1, ButtonIndex::M3] {
            for extra in [0, LOCK_MASK, MOD2_MASK, LOCK_MASK | MOD2_MASK] {
                self.conn.grab_button(
                    false,
                    win,
                    EventMask::BUTTON_PRESS,
                    GrabMode::ASYNC,
                    GrabMode::ASYNC,
                    NONE,
                    NONE,
                    button,
                    ModMask::from(MOD_4 | extra),
                )?;
            }
        }
        Ok(())
    }

    fn resize_cursor(&self, edges: Option<(bool, bool, bool, bool)>) -> u32 {
        let rc = self.resize_cursors;
        match edges {
            Some((true, _, true, _)) => rc.top_left,
            Some((_, true, _, true)) => rc.bottom_right,
            Some((_, true, true, _)) => rc.top_right,
            Some((true, _, _, true)) => rc.bottom_left,
            Some((true, _, _, _)) | Some((_, true, _, _)) => rc.horizontal,
            Some((_, _, true, _)) | Some((_, _, _, true)) => rc.vertical,
            _ => NONE,
        }
    }

    /// dwm's `updatecurrentdesktop()`: the index of the first selected tag.
    fn update_current_desktop(&self, tagset: u32) -> Result {
        let idx = (0..TAG_COUNT).find(|i| tagset & (1 << i) != 0).unwrap_or(0);
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_current_desktop,
            AtomEnum::CARDINAL,
            &[idx],
        )?;
        Ok(())
    }

    fn tags_of(&self, mi: usize) -> u32 {
        let m = &self.monitors[mi];
        m.tagset[m.seltags]
    }

    /// A client counts as visible only when its tags are selected and it is not
    /// iconified. Iconified clients keep their tree leaf, client-list entry and
    /// geometry, but take no tile, cannot be focused and stay unmapped.
    fn is_visible(&self, c: &Client) -> bool {
        c.tags & self.tags_of(c.mon) != 0 && !c.hidden
    }

    /// Visible windows on `mi` in stack order, like dwm's `ISVISIBLE` walk.
    fn stack_order(&self, mi: usize) -> Vec<Window> {
        self.clients
            .iter()
            .filter(|c| c.mon == mi && self.is_visible(c))
            .map(|c| c.win)
            .collect()
    }

    /// Hand out the next stacking token. Called when a client is adopted or
    /// changes floating/fullscreen state, so the token records when it last
    /// asked to be on top rather than just when it was created.
    fn next_stack_seq(&mut self) -> u64 {
        self.stack_seq = self.stack_seq.wrapping_add(1);
        self.stack_seq
    }

    /// All visible fullscreen clients on `mi`, newest first: `clients` is
    /// newest-first because adoption inserts at index 0. `apply_layout()` keeps
    /// every one of them mapped and covers the monitor with each, so a new
    /// fullscreen window sits above an older one instead of unmapping it.
    fn fullscreen_windows(&self, mi: usize) -> Vec<(usize, Window)> {
        self.clients
            .iter()
            .enumerate()
            .filter(|(_, c)| c.fullscreen && c.mon == mi && self.is_visible(c))
            .map(|(idx, c)| (idx, c.win))
            .collect()
    }

    /// Whether `win` may be mapped while `fs_owner` owns its monitor. Every
    /// fullscreen client stays mapped (they form a stack, newest on top), as
    /// do floating overlays; tiled windows stay hidden behind the stack.
    fn map_allowed(win: Window, floating: bool, fullscreen: bool, fs_owner: Option<Window>) -> bool {
        fs_owner.is_none_or(|owner| owner == win || fullscreen || floating)
    }

    fn is_managed(&self, win: Window) -> bool {
        self.clients.iter().any(|c| c.win == win)
    }

    fn bar_h(&self) -> i32 {
        self.metrics.bar_height()
    }

    /// dwm's `updatesystrayicongeom()`: icons fill `bh - vertpadbar` vertically.
    fn tray_icon_size(&self) -> i32 {
        (self.bar_h() - VERTPADBAR).clamp(TRAY_ICON_MIN, TRAY_ICON_MAX)
    }

    /// Only the selected monitor shows the single system tray, so only its
    /// status section is pushed left to make room for it.
    fn tray_width(&self, mi: usize) -> i32 {
        if mi == self.selmon {
            self.tray.width(self.tray_icon_size(), SYSTRAY_SPACING)
        } else {
            0
        }
    }

    fn tray_x(&self, mi: usize) -> i32 {
        let m = &self.monitors[mi];
        let bar_right = if FLOATBAR {
            m.wx + m.ww - m.gaps.ov
        } else {
            m.wx + m.ww
        };
        bar_right - self.tray_width(mi)
    }

    fn is_tray_icon(&self, win: Window) -> bool {
        self.tray.contains(win)
    }

    fn relayout_tray(&mut self) -> Result {
        let size = self.tray_icon_size();
        self.tray
            .layout(&self.conn, size, SYSTRAY_SPACING, self.bar_h())?;
        self.conn.flush()?;
        self.bar_dirty = true;
        Ok(())
    }

    fn dock_tray_icon(&mut self, win: Window) -> Result {
        if self.tray.dock(&self.conn, win)? {
            self.relayout_tray()?;
        }
        Ok(())
    }

    /// A ButtonPress on an icon (or on the empty tray) marks the short window
    /// in which windows mapped by that app are treated as its menus. Selecting
    /// ButtonPress on the icons in `Tray::dock` is what makes these events
    /// visible; the app still receives the very same click.
    fn record_tray_click(&self, icon: Window) {
        if TRAY_MENUS_ABOVE_BAR {
            *self.tray_click.borrow_mut() = Some(TrayClick {
                at: Instant::now(),
                class: if icon != 0 { self.read_wm_class(icon) } else { None },
            });
        }
    }

    /// Is this root coordinate inside the selected monitor's tray cell? The
    /// tray is only mapped on `selmon`, so other monitors have zero width.
    fn pointer_in_tray(&self, x: i32, y: i32) -> bool {
        let mi = self.selmon;
        let tw = self.tray_width(mi);
        let tx = self.tray_x(mi);
        let ty = self.monitors[mi].by;
        tw > 0 && x >= tx && x < tx + tw && y >= ty && y < ty + self.bar_h()
    }

    /// Is `win` a menu or window opened from a tray icon?
    ///
    /// The reliable hints are checked first: a `WM_TRANSIENT_FOR` pointing at
    /// an icon, or a menu parented by the icon or the tray container. Toolkits
    /// that set neither are caught by the popup window type or by the class of
    /// the icon that was just clicked, within a short grace period.
    fn is_tray_menu(&self, win: Window) -> bool {
        if !TRAY_MENUS_ABOVE_BAR
            || win == 0
            || win == self.tray.window
            || self.is_tray_icon(win)
            || self.tray_menus.borrow().contains(&win)
        {
            return false;
        }
        let menus = self.tray_menus.borrow();
        if self.read_transient_for(win).is_some_and(|p| {
            self.is_tray_icon(p) || p == self.tray.window || menus.contains(&p)
        }) {
            return true;
        }
        let parent = self
            .conn
            .query_tree(win)
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| r.parent);
        let popup = is_popup_win_type(self.read_win_type(win));
        if parent == Some(self.tray.window) {
            return true;
        }
        // A submenu is commonly transient for, or parented by, the menu that
        // opened it rather than by the icon. Follow tracked menus here too.
        if parent.is_some_and(|p| (self.is_tray_icon(p) || menus.contains(&p)) && popup) {
            return true;
        }
        drop(menus);
        let click_borrow = self.tray_click.borrow();
        let Some(click) = click_borrow.as_ref() else {
            return false;
        };
        if click.at.elapsed() > TRAY_MENU_GRACE || parent != Some(self.root) {
            return false;
        }
        // Only top-level windows are adopted by the class heuristic; an icon's
        // own drawing children are not menus and must never be reparented.
        popup
            || match (&click.class, self.read_wm_class(win)) {
                (Some(a), Some(b)) => *a == b,
                _ => false,
            }
    }

    /// Remember a tray menu and put it on top of the bar layer. A menu created
    /// as a child of an icon has to move to the root first: X stacks siblings
    /// within one parent, so raising it inside the tray subtree cannot lift it
    /// above the bar windows, which are siblings of the tray container.
    fn track_tray_menu(&self, win: Window) -> Result {
        if !TRAY_MENUS_ABOVE_BAR || win == 0 {
            return Ok(());
        }
        {
            let mut menus = self.tray_menus.borrow_mut();
            if menus.contains(&win) {
                return Ok(());
            }
            menus.push(win);
        }
        let parent = self.conn.query_tree(win)?.reply()?.parent;
        if parent == self.tray.window || self.is_tray_icon(parent) {
            if let Ok(coords) = self
                .conn
                .translate_coordinates(win, self.root, 0, 0)?
                .reply()
            {
                self.conn
                    .reparent_window(win, self.root, coords.dst_x, coords.dst_y)?;
            }
        }
        let _ = self
            .conn
            .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE));
        self.conn.flush()?;
        Ok(())
    }

    fn raise_tray_menus(&self) {
        for &win in self.tray_menus.borrow().iter() {
            let _ = self
                .conn
                .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE));
        }
    }

    /// Is `win` an override-redirect root child the WM does not manage? Menus
    /// and tooltips are almost always mapped that way. Nested children of a
    /// client are excluded: they already follow their parent's place in the
    /// root stack and cannot be raised above root siblings.
    fn is_unmanaged_overlay(&self, win: Window) -> bool {
        if win == 0 || win == self.root || self.is_our_window(win) || self.is_managed(win) {
            return false;
        }
        let Some(attrs) = self
            .conn
            .get_window_attributes(win)
            .ok()
            .and_then(|c| c.reply().ok())
        else {
            return false;
        };
        if !attrs.override_redirect || attrs.class == WindowClass::INPUT_ONLY {
            return false;
        }
        let parent = self
            .conn
            .query_tree(win)
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| r.parent);
        parent == Some(self.root)
    }

    /// A popup announces itself with a popup window type or `WM_TRANSIENT_FOR`.
    /// Such windows belong above the bar layer, like tray menus do.
    fn is_overlay_popup(&self, win: Window) -> bool {
        self.is_unmanaged_overlay(win)
            && (is_popup_win_type(self.read_win_type(win))
                || self.read_transient_for(win).is_some())
    }

    /// Remember an unmanaged root child seen on MapNotify and put it in its
    /// layer. Override-redirect windows never send MapRequest, so this is the
    /// only chance to see them before a later restack buries them under a newly
    /// mapped tiled client.
    fn track_overlay(&self, win: Window) -> Result {
        if !self.is_unmanaged_overlay(win) {
            return Ok(());
        }
        let popup = self.is_overlay_popup(win);
        {
            let mut tracked = if popup {
                self.popup_windows.borrow_mut()
            } else {
                self.overlay_windows.borrow_mut()
            };
            if tracked.contains(&win) {
                return Ok(());
            }
            tracked.push(win);
        }
        self.conn
            .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE))?;
        // A generic OSD must not hide the bar that was on top before it mapped.
        if !popup {
            self.raise_bars()?;
        }
        self.conn.flush()?;
        Ok(())
    }

    /// Restore the unmanaged overlay layers after clients and bars have been
    /// restacked. Generic overlays go below the bar, popups above it.
    fn raise_overlays(&self) {
        for &win in self.overlay_windows.borrow().iter() {
            let _ = self
                .conn
                .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE));
        }
    }

    fn raise_popups(&self) {
        for &win in self.popup_windows.borrow().iter() {
            let _ = self
                .conn
                .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE));
        }
    }

    /// dwm's `updatesizehints()`, using x11rb's `WM_SIZE_HINTS` parser.
    fn read_size_hints(&self, win: Window) -> Result<SizeHints> {
        let Some(parsed) = WmSizeHints::get_normal_hints(&self.conn, win)?.reply()? else {
            return Ok(SizeHints::default());
        };
        let (min_w, min_h) = parsed.min_size.unwrap_or((0, 0));
        let (max_w, max_h) = parsed.max_size.unwrap_or((0, 0));
        let (base_w, base_h) = parsed.base_size.unwrap_or((min_w, min_h));
        let (inc_w, inc_h) = parsed.size_increment.unwrap_or((0, 0));
        let (min_aspect, max_aspect) = parsed.aspect.map_or((0.0, 0.0), |(lo, hi)| {
            let lo = if lo.numerator != 0 {
                lo.denominator as f64 / lo.numerator as f64
            } else {
                0.0
            };
            let hi = if hi.denominator != 0 {
                hi.numerator as f64 / hi.denominator as f64
            } else {
                0.0
            };
            (lo, hi)
        });
        Ok(SizeHints {
            min_w: min_w.max(0),
            min_h: min_h.max(0),
            max_w: max_w.max(0),
            max_h: max_h.max(0),
            base_w: base_w.max(0),
            base_h: base_h.max(0),
            inc_w: inc_w.max(0),
            inc_h: inc_h.max(0),
            min_aspect,
            max_aspect,
            requested_pos: parsed.position.map(|(_, x, y)| (x, y)),
            user_position: matches!(
                parsed.position,
                Some((WmSizeHintsSpecification::UserSpecified, _, _))
            ),
            requested_size: parsed.size.map(|(_, w, h)| (w, h)),
            gravity: parsed.win_gravity,
        })
    }

    fn read_wm_hints(&self, win: Window) -> (bool, bool) {
        // returns (wants_input, urgent); defaults (true, false)
        let Ok(cookie) = self.conn.get_property(false, win, AtomEnum::WM_HINTS, AtomEnum::ANY, 0, 9) else {
            return (true, false);
        };
        let Ok(reply) = cookie.reply() else { return (true, false); };
        let vals: Vec<u32> = reply.value32().map(|it| it.collect()).unwrap_or_default();
        if vals.is_empty() { return (true, false); }
        let flags = vals[0];
        let input_hint = (flags & (1 << 0)) != 0;
        let urgency_hint = (flags & (1 << 8)) != 0;
        let wants_input = if input_hint && vals.len() >= 2 { vals[1] != 0 } else { true };
        (wants_input, urgency_hint)
    }

    fn read_transient_for(&self, win: Window) -> Option<Window> {
        self.conn
            .get_property(false, win, self.atoms.wm_transient_for, AtomEnum::WINDOW, 0, 1)
            .ok()
            .and_then(|c| c.reply().ok())
            .and_then(|r| r.value32().and_then(|mut it| it.next()))
    }

    fn read_net_wm_state(&self, win: Window) -> Vec<u32> {
        self.conn
            .get_property(false, win, self.atoms.net_wm_state, AtomEnum::ATOM, 0, 64)
            .ok()
            .and_then(|c| c.reply().ok())
            .and_then(|r| r.value32().map(|it| it.collect()))
            .unwrap_or_default()
    }

    fn read_net_wm_state_modal(&self, win: Window) -> bool {
        self.read_net_wm_state(win)
            .contains(&self.atoms.net_wm_state_modal)
    }

    /// Workspace the previous WM recorded for `win`, if any. Application-sent
    /// `_NET_WM_DESKTOP` messages are ignored (see `client_message`), but at
    /// startup this property is the only way to tell where a window that is
    /// currently unmapped belongs.
    fn read_net_wm_desktop(&self, win: Window) -> Option<u32> {
        self.conn
            .get_property(
                false,
                win,
                self.atoms.net_wm_desktop,
                AtomEnum::CARDINAL,
                0,
                1,
            )
            .ok()?
            .reply()
            .ok()?
            .value32()?
            .next()
    }

    /// Turn an EWMH desktop index into the tag bit rwm uses internally.
    /// 0xFFFFFFFF means "all desktops", matching `set_client_desktop`.
    fn desktop_to_tags(desk: u32) -> Option<u32> {
        if desk == 0xFFFF_FFFF {
            Some(TAGMASK)
        } else if desk < TAG_COUNT {
            Some(1u32 << desk)
        } else {
            None
        }
    }

    fn read_rwm_monitor(&self, win: Window) -> Option<Rect> {
        let reply = self
            .conn
            .get_property(
                false,
                win,
                self.atoms.rwm_monitor,
                AtomEnum::CARDINAL,
                0,
                4,
            )
            .ok()?
            .reply()
            .ok()?;
        let mut vals = reply.value32()?;
        let x = vals.next()? as i32;
        let y = vals.next()? as i32;
        let w = vals.next()?;
        let h = vals.next()?;
        Some(Rect { x, y, w, h })
    }

    fn monitor_for_saved_rect(&self, rect: Rect) -> Option<usize> {
        if let Some((i, _)) = self.monitors.iter().enumerate().find(|(_, m)| m.rect == rect) {
            return Some(i);
        }
        let cx = rect.x + rect.w as i32 / 2;
        let cy = rect.y + rect.h as i32 / 2;
        Some(self.monitor_at(cx, cy))
    }

    fn set_rwm_monitor(&self, win: Window, mi: usize) -> Result {
        let Some(m) = self.monitors.get(mi) else {
            return Ok(());
        };
        let r = m.rect;
        self.conn.change_property32(
            PropMode::REPLACE,
            win,
            self.atoms.rwm_monitor,
            AtomEnum::CARDINAL,
            &[r.x as u32, r.y as u32, r.w, r.h],
        )?;
        Ok(())
    }

    fn read_wm_class(&self, win: Window) -> Option<(String, String)> {
        let reply = self
            .conn
            .get_property(false, win, AtomEnum::WM_CLASS, AtomEnum::STRING, 0, 64)
            .ok()?
            .reply()
            .ok()?;
        if reply.value.is_empty() {
            return None;
        }
        let mut parts = reply
            .value
            .split(|&b| b == 0)
            .filter(|p| !p.is_empty())
            .map(|p| String::from_utf8_lossy(p).into_owned());
        let instance = parts.next()?;
        let class = parts.next().unwrap_or_default();
        Some((instance, class))
    }

    fn read_window_name(&self, win: Window) -> String {
        let utf8 = self
            .conn
            .get_property(
                false,
                win,
                self.atoms.net_wm_name,
                self.atoms.utf8_string,
                0,
                256,
            )
            .ok()
            .and_then(|c| c.reply().ok());
        if let Some(r) = utf8.filter(|r| !r.value.is_empty()) {
            return String::from_utf8_lossy(&r.value).into_owned();
        }
        self.conn
            .get_property(false, win, AtomEnum::WM_NAME, AtomEnum::STRING, 0, 256)
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| String::from_utf8_lossy(&r.value).into_owned())
            .unwrap_or_default()
    }

    fn should_ignore_window(&self, win: Window) -> bool {
        if let Some((instance, class)) = self.read_wm_class(win) {
            if instance.eq_ignore_ascii_case("picom") || class.eq_ignore_ascii_case("picom") {
                return true;
            }
        }
        let name = self.read_window_name(win);
        name.starts_with("Qt Selection Owner for ")
            || name.starts_with("Qt Clipboard Owner for ")
    }

    fn read_win_type(&self, win: Window) -> WinType {
        let cookie = match self.conn.get_property(
            false,
            win,
            self.atoms.net_wm_window_type,
            AtomEnum::ATOM,
            0,
            16,
        ) {
            Ok(c) => c,
            Err(_) => return WinType::Normal,
        };
        let reply = match cookie.reply() {
            Ok(r) => r,
            Err(_) => return WinType::Normal,
        };
        if reply.format == 0 {
            return WinType::Normal;
        }
        if let Some(atoms) = reply.value32() {
            for a in atoms {
                if a == self.atoms.net_wm_window_type_dialog {
                    return WinType::Dialog;
                } else if a == self.atoms.net_wm_window_type_utility {
                    return WinType::Utility;
                } else if a == self.atoms.net_wm_window_type_toolbar {
                    return WinType::Toolbar;
                } else if a == self.atoms.net_wm_window_type_menu {
                    return WinType::Menu;
                } else if a == self.atoms.net_wm_window_type_dropdown_menu {
                    return WinType::DropdownMenu;
                } else if a == self.atoms.net_wm_window_type_popup_menu {
                    return WinType::PopupMenu;
                } else if a == self.atoms.net_wm_window_type_tooltip {
                    return WinType::Tooltip;
                } else if a == self.atoms.net_wm_window_type_notification {
                    return WinType::Notification;
                } else if a == self.atoms.net_wm_window_type_splash {
                    return WinType::Splash;
                } else if a == self.atoms.net_wm_window_type_dock {
                    return WinType::Dock;
                } else if a == self.atoms.net_wm_window_type_desktop {
                    return WinType::Desktop;
                }
            }
        }
        WinType::Normal
    }

    /// The monitor's area below the bar, set by `update_bar_pos`.
    fn work(&self, mi: usize) -> Rect {
        let m = &self.monitors[mi];
        Rect {
            x: m.wx,
            y: m.wy,
            w: m.ww as u32,
            h: m.wh as u32,
        }
    }

    /// The visible tiled windows on `mi` in stack order.
    fn tiled_order(&self, mi: usize) -> Vec<Window> {
        self.clients
            .iter()
            .filter(|c| c.mon == mi && !c.floating && !c.dragging && self.is_visible(c))
            .map(|c| c.win)
            .collect()
    }

    /// The outer box `win` is drawn in: the monitor for a fullscreen client,
    /// otherwise its floating geometry or its tile.
    fn geometry(&self, mi: usize, win: Window) -> Option<Rect> {
        if let Some(c) = self.clients.iter().find(|c| c.win == win && c.fullscreen) {
            let m = self.monitors[c.mon].rect;
            return Some(Rect {
                x: m.x,
                y: m.y,
                w: m.w,
                h: m.h,
            });
        }
        if let Some(c) = self
            .clients
            .iter()
            .find(|c| c.win == win && (c.floating || c.dragging))
        {
            return Some(c.geom);
        }
        self.layout_mon(mi)
            .into_iter()
            .find(|(w, _)| *w == win)
            .map(|(_, r)| r)
    }

    /// The box of a client's transient parent, when it is managed. A tiled
    /// parent has no `geom`, so this uses its actual layout/frame geometry.
    fn transient_geometry(&self, transient: Option<Window>, fallback_mon: usize) -> Option<Rect> {
        let parent = transient?;
        let pm = self
            .clients
            .iter()
            .find(|c| c.win == parent)
            .map(|c| c.mon)
            .unwrap_or(fallback_mon);
        self.geometry(pm, parent)
    }

    /// Where an automatically placed floating window goes after a resize that
    /// did not come with a new position: on its parent, or work-area center.
    fn auto_float_origin(&self, c: &Client, w: i32, h: i32) -> (i32, i32) {
        let area = self
            .transient_geometry(c.transient_for, c.mon)
            .unwrap_or_else(|| self.work(c.mon));
        centered_in(area, w, h)
    }

    /// dwm's `getgaps()`: the gaps in use for the current window count.
    fn effective_gaps(&self, mi: usize) -> Gaps {
        let m = &self.monitors[mi];
        if !self.gaps_enabled {
            return Gaps::default();
        }
        let n = self.tiled_order(mi).len();
        let outer = !(config::SMARTGAPS && n == 1);
        Gaps {
            oh: if outer { m.gaps.oh } else { 0 },
            ov: if outer { m.gaps.ov } else { 0 },
            ih: m.gaps.ih,
            iv: m.gaps.iv,
        }
    }

    /// The area tiled windows are laid out in: `work` inside the outer gaps.
    fn tile_area(&self, mi: usize) -> Rect {
        tree::inset(self.work(mi), &self.effective_gaps(mi))
    }

    /// dwm's `updatebarpos()`, without the showtab branch.
    fn update_bar_pos(&mut self, mi: usize) {
        let bh = self.bar_h();
        let m = &mut self.monitors[mi];
        m.wy = m.rect.y;
        m.wh = m.rect.h as i32;
        if m.showbar {
            if FLOATBAR {
                m.wh -= m.gaps.oh + bh;
                m.by = if TOPBAR {
                    m.wy + m.gaps.oh
                } else {
                    m.wy + m.wh
                };
            } else {
                m.wh -= bh;
                m.by = if TOPBAR { m.wy } else { m.wy + m.wh };
            }
            if TOPBAR {
                m.wy += if FLOATBAR { bh + m.gaps.oh } else { bh };
            }
        } else {
            m.by = -bh - m.gaps.oh;
        }
    }

    /// Creates the bar windows and markers for every monitor.
    fn update_bars(&mut self) -> Result {
        for mi in 0..self.monitors.len() {
            self.create_monitor_ui(mi)?;
        }
        Ok(())
    }

    /// dwm gives the bar windows `WM_CLASS(STRING) = "dwm", "dwm"`. Apply it
    /// to the sections, center and tray; Finder/notification popups and the
    /// separate markers manage their own classes.
    fn set_bar_window_class(&self, win: Window) -> Result {
        self.conn
            .change_property8(
                PropMode::REPLACE,
                win,
                AtomEnum::WM_CLASS,
                AtomEnum::STRING,
                b"dwm\0dwm\0",
            )?
            .check()?;
        Ok(())
    }

    /// Creates the bar windows and markers for a single monitor.
    fn create_monitor_ui(&mut self, mi: usize) -> Result {
        let bh = self.bar_h() as u16;
        let root_colormap = self
            .conn
            .get_window_attributes(self.root)?
            .reply()?
            .colormap;
        let marker_pixel = self
            .conn
            .alloc_color(root_colormap, 0xB8B8, 0xE9E9, 0xB4B4)?
            .reply()?
            .pixel;
        let bar_events = EventMask::EXPOSURE
            | EventMask::ENTER_WINDOW
            | EventMask::LEAVE_WINDOW
            | EventMask::BUTTON_PRESS
            | EventMask::BUTTON_RELEASE
            | EventMask::POINTER_MOTION;

        let r = self.monitors[mi].rect;
        let cmap = self.conn.generate_id()?;
        self.conn
            .create_colormap(ColormapAlloc::NONE, cmap, self.root, self.visual_id)?;

        let mut wins = [0 as Window; 4];
        for (i, win) in wins.iter_mut().enumerate() {
            *win = self.conn.generate_id()?;
            let aux = CreateWindowAux::new()
                .background_pixel(BAR_BACKGROUND_PIXEL)
                .border_pixel(0)
                .bit_gravity(Gravity::NORTH_WEST)
                .colormap(cmap)
                .override_redirect(1)
                .event_mask(bar_events);
            // wins[0] is the tag strip; show a hand cursor over its cells.
            let aux = if i == 0 { aux.cursor(self.tag_cursor) } else { aux };
            self.conn
                .create_window(
                    self.depth,
                    *win,
                    self.root,
                    r.x as i16,
                    r.y as i16,
                    1,
                    bh,
                    0,
                    WindowClass::INPUT_OUTPUT,
                    self.visual_id,
                    &aux,
                )?
                .check()?;
            self.set_bar_window_class(*win)?;
            self.conn.map_window(*win)?;
            self.bar_mapped.borrow_mut().insert(*win);
        }

        let center = self.conn.generate_id()?;
        let argb_ok = self.finder_argb_visual != 0
            && self
                .conn
                .create_window(
                    self.finder_argb_depth,
                    center,
                    self.root,
                    r.x as i16,
                    r.y as i16,
                    1,
                    bh,
                    0,
                    WindowClass::INPUT_OUTPUT,
                    self.finder_argb_visual,
                    &CreateWindowAux::new()
                        .background_pixel(BAR_TRANSPARENT_PIXEL)
                        .border_pixel(0)
                        .bit_gravity(Gravity::NORTH_WEST)
                        .colormap(self.finder_argb_colormap)
                        .override_redirect(1)
                        .event_mask(bar_events),
                )?
                .check()
                .is_ok();
        if !argb_ok {
            self.finder_argb_visual = 0;
            self.finder_argb_depth = 0;
            if self.finder_argb_colormap != 0 {
                let _ = self.conn.free_colormap(self.finder_argb_colormap);
            }
            self.finder_argb_colormap = 0;
            self.finder_argb_visual_ptr = std::ptr::null_mut();
            self.conn
                .create_window(
                    self.depth,
                    center,
                    self.root,
                    r.x as i16,
                    r.y as i16,
                    1,
                    bh,
                    0,
                    WindowClass::INPUT_OUTPUT,
                    self.visual_id,
                    &CreateWindowAux::new()
                        .background_pixel(BAR_BACKGROUND_PIXEL)
                        .border_pixel(0)
                        .bit_gravity(Gravity::NORTH_WEST)
                        .colormap(cmap)
                        .override_redirect(1)
                        .event_mask(bar_events),
                )?
                .check()?;
        }
        self.set_bar_window_class(center)?;
        self.conn.map_window(center)?;
        self.bar_mapped.borrow_mut().insert(center);

        let mpris_markerwin = self.conn.generate_id()?;
        self.conn
            .create_window(
                0,
                mpris_markerwin,
                self.root,
                0,
                0,
                24,
                16,
                0,
                WindowClass::INPUT_OUTPUT,
                0,
                &CreateWindowAux::new()
                    .background_pixel(marker_pixel)
                    .border_pixel(0)
                    .override_redirect(1)
                    .event_mask(
                        EventMask::ENTER_WINDOW
                            | EventMask::LEAVE_WINDOW
                            | EventMask::BUTTON_PRESS
                            | EventMask::BUTTON_RELEASE
                            | EventMask::POINTER_MOTION,
                    ),
            )?
            .check()?;
        self.conn
            .change_property8(
                PropMode::REPLACE,
                mpris_markerwin,
                AtomEnum::WM_NAME,
                AtomEnum::STRING,
                b"dwm-mpris-volume-marker",
            )?
            .check()?;
        self.conn
            .change_property8(
                PropMode::REPLACE,
                mpris_markerwin,
                AtomEnum::WM_CLASS,
                AtomEnum::STRING,
                b"dwm-mpris-volume-marker\0dwm-mpris-volume-marker\0",
            )?
            .check()?;

        let finder_markerwin = self.conn.generate_id()?;
        let white = unsafe { xlib::XWhitePixel(self.drw.dpy(), self.drw.screen()) };
        self.conn
            .create_window(
                0,
                finder_markerwin,
                self.root,
                0,
                0,
                crate::config::FINDER_MARKER_WIDTH as u16,
                38,
                0,
                WindowClass::INPUT_OUTPUT,
                0,
                &CreateWindowAux::new()
                    .background_pixel(white as u32)
                    .border_pixel(0)
                    .override_redirect(1),
            )?
            .check()?;
        // The marker is only a visual overlay. Give it an empty input shape so
        // clicks and wheel events land on the Finder popup underneath instead:
        // while Finder holds a pointer grab, events over a window that selects
        // no buttons are swallowed (XI2 watchers still see them), which made
        // the highlighted row unclickable and unscrollable.
        if let Ok(cookie) = self.conn.shape_rectangles(
            SO::SET,
            SK::INPUT,
            ClipOrdering::UNSORTED,
            finder_markerwin,
            0,
            0,
            &[],
        ) {
            let _ = cookie.check();
        }
        self.conn
            .change_property8(
                PropMode::REPLACE,
                finder_markerwin,
                AtomEnum::WM_NAME,
                AtomEnum::STRING,
                b"dwm-finder-marker\0",
            )?
            .check()?;
        self.conn
            .change_property8(
                PropMode::REPLACE,
                finder_markerwin,
                AtomEnum::WM_CLASS,
                AtomEnum::STRING,
                b"dwm-finder-marker\0dwm-finder-marker\0",
            )?
            .check()?;

        let m = &mut self.monitors[mi];
        m.barwin = wins[0];
        m.bartitlewin = wins[1];
        m.barkbwin = wins[2];
        m.barrightwin = wins[3];
        m.barcenterwin = center;
        m.colormap = cmap;
        m.mpris_markerwin = mpris_markerwin;
        m.finder_markerwin = finder_markerwin;
        m.finder_marker_stacked.set(false);
        m.finder_marker_pos.set(None);
        m.finder_stacked.set(false);
        // The center window starts as the ordinary bar clock; Finder and
        // notifications change its class while they own it.
        self.center_kind.borrow_mut()[mi] = CenterKind::Dwm;
        self.set_bar_class(mi)?;
        Ok(())
    }

    /// Destroys the bar windows and markers for a single monitor.
    fn destroy_monitor_ui(&mut self, mi: usize) {
        let windows = {
            let m = &self.monitors[mi];
            [
                m.barwin,
                m.bartitlewin,
                m.barcenterwin,
                m.barkbwin,
                m.barrightwin,
                m.mpris_markerwin,
                m.finder_markerwin,
            ]
        };
        for win in windows.into_iter().filter(|w| *w != 0) {
            let _ = self.conn.unmap_window(win);
            let _ = self.conn.destroy_window(win);
            self.bar_mapped.borrow_mut().remove(&win);
            self.bar_drawn.borrow_mut().remove(&win);
            self.clock_drawn.borrow_mut().remove(&win);
            self.force_windows.borrow_mut().remove(&win);
            self.geom_cache.borrow_mut().remove(&win);
        }
        let cmap = self.monitors[mi].colormap;
        if cmap != 0 {
            let _ = self.conn.free_colormap(cmap);
        }
        let m = &mut self.monitors[mi];
        m.barwin = 0;
        m.bartitlewin = 0;
        m.barcenterwin = 0;
        m.barkbwin = 0;
        m.barrightwin = 0;
        m.mpris_markerwin = 0;
        m.finder_markerwin = 0;
        m.colormap = 0;
    }

    fn tagsbarwidth(&self) -> i32 {
        let w: i32 = (0..TAGS).map(|_| self.metrics.textw(TAG_LABEL)).sum();
        BORDERPX + w + self.metrics.textw(LAYOUT_SYMBOL)
    }

    /// dwm's `bartitlewidth()`: the focused window's icon (or the launcher
    /// glyph when it has none) plus the selected client's name, capped at the
    /// available bar width.
    fn bartitlewidth(&self, mi: usize, budget: i32) -> i32 {
        let sel = self.monitors[mi].sel;
        let mut w: i32 = match sel.and_then(|win| self.client_icon(win)) {
            Some(icon) => CLIENT_ICON_LEFT_PAD + icon.width as i32 + CLIENT_ICON_SPACING,
            None => LAUNCHERS.iter().map(|name| self.metrics.textw(name)).sum(),
        };
        if let Some(sel) = sel {
            w += self.metrics.textw(&self.client_name(sel));
        }
        w.min(budget)
    }

    fn monitor_fullscreen(&self, mi: usize) -> bool {
        self.clients.iter().any(|c| c.fullscreen && c.mon == mi && self.is_visible(c))
    }

    /// Owner of a monitor's center window, with Finder overriding notification.
    fn center_kind(&self, mi: usize) -> CenterKind {
        if mi == self.selmon && self.finder.is_active() {
            CenterKind::Finder
        } else if mi == self.selmon && self.notification.is_center_active() {
            match self.notification.center_class() {
                crate::notification::CenterClass::History => CenterKind::History,
                crate::notification::CenterClass::Notification => CenterKind::Notification,
                crate::notification::CenterClass::Dwm => CenterKind::Dwm,
            }
        } else {
            CenterKind::Dwm
        }
    }

    /// dwm's `barwidths()`. The systray is not ported, so its width is 0.
    fn barwidths(&self, mi: usize) -> BarWidths {
        let m = &self.monitors[mi];
        let barw = if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww };
        let status_w = if let Some(custom) = &self.bar_status.custom {
            self.metrics.status_width(custom)
        } else {
            self.metrics.status_runs_width(&self.bar_status)
        };
        let mut rw = status_w + HORIZPADBAR;
        if self.mpris_hovered && mi == self.selmon && self.mpris.present {
            rw = rw.max(320 + HORIZPADBAR);
        }
        // dwm's `barwidths()` reserves `finder_popup_width()` for the selected
        // center window while Finder is open, so the popup never overlaps the
        // title or status sections.
        let cw = if mi == self.selmon && self.finder.is_active() {
            self.finder.popup_width() as i32
        } else if mi == self.selmon && self.notification.is_center_active() {
            self.notification.popup_size(self.bar_h()).0 as i32
        } else {
            self.metrics.text_width(&self.clock) + 2 * CLOCKPAD
        };
        let kw = self.metrics.text_width(&self.kbstr) + 2 * KBLAYOUTPAD;
        let tw = self.tagsbarwidth();
        let tray_w = self.tray_width(mi);
        let tray_gap = if tray_w > 0 { BARGAP } else { 0 };
        let used = tw + rw + cw + kw + 4 * BARGAP + tray_w + tray_gap;
        let avail = if barw > used { barw - used } else { 0 };
        let budget = if avail > BORDERPX {
            avail - BORDERPX
        } else {
            0
        };
        let mut tlw = BORDERPX + self.bartitlewidth(mi, budget);
        if tlw > avail {
            tlw = avail;
        }
        BarWidths {
            tw,
            tlw,
            cw,
            kw,
            rw,
        }
    }

    /// Width of the center clock window: dwm's `dcw`. Only the selected monitor
    /// grows, and the layout keeps the fixed `cw`.
    fn clock_window_width(&self, mi: usize, cw: i32) -> i32 {
        if mi == self.selmon && (self.finder.is_active() || self.notification.is_center_active()) {
            // The popup geometry is already the full center width; the audio
            // audio animation is suppressed while an overlay owns this window.
            cw
        } else if mi == self.selmon {
            cw + self.clock_extra
        } else {
            cw
        }
    }

    /// dwm's center section placement from `resizebarwin()`: the clock window's
    /// `(x, width)` on monitor `mi`, or `None` when there is no room for it. The
    /// clock thread moves the window together with its pixels, so it never shows
    /// a new size with the old text.
    fn clock_place(&self, mi: usize) -> Option<(i32, i32)> {
        let m = &self.monitors[mi];
        let b = self.barwidths(mi);
        let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
        let kx = lx + b.tw + BARGAP;
        let title_right = kx + b.kw + BARGAP + b.tlw;
        // rightbar_x() reserves the systray, so the clock follows the right
        // bar left when tray icons appear instead of staying at the old edge.
        let rx = self.rightbar_x(mi);
        let dcw = self.clock_window_width(mi, b.cw);
        Some((centered_bar_x(title_right, rx, b.cw, dcw)?, dcw))
    }

    /// Maps or unmaps a bar window only when its state actually changes. The
    /// old code sent MapWindow for every mapped window on every bar frame.
    fn set_mapped(&self, win: Window, map: bool) -> Result {
        let mut mapped = self.bar_mapped.borrow_mut();
        if mapped.contains(&win) == map {
            return Ok(());
        }
        if map {
            self.conn.map_window(win)?;
            mapped.insert(win);
        } else {
            self.conn.unmap_window(win)?;
            mapped.remove(&win);
        }
        // Mapping another bar section can raise it over the popup. Do not
        // invalidate for the popup or its own marker: that would restack them
        // again while the pointer is hovering the marker.
        let center_owned = (self.finder.is_active()
            && self
                .monitors
                .iter()
                .any(|m| m.barcenterwin == win || m.finder_markerwin == win))
            || (self.notification.is_center_active()
                && self.monitors.iter().any(|m| m.barcenterwin == win));
        if !center_owned {
            self.invalidate_finder_stacking();
        }
        Ok(())
    }

    /// Whether a bar section needs its pixels copied again. An Expose event
    /// forces a repaint even when the cached key matches.
    fn section_changed(&self, win: Window, key: &str) -> bool {
        self.force_windows.borrow().contains(&win)
            || self.bar_drawn.borrow().get(&win).map(String::as_str) != Some(key)
    }

    /// Configures `win` only when its geometry actually changes. This keeps the
    /// per-tick bar layout work from generating X requests and damage. Returns
    /// whether a configure request was sent.
    fn configure_cached(
        &self,
        win: Window,
        x: i32,
        y: i32,
        w: i32,
        h: i32,
        border: u32,
    ) -> Result<bool> {
        let (w, h) = (w.max(1) as u32, h.max(1) as u32);
        let key = (x, y, w, h, border);
        if self.geom_cache.borrow().get(&win) == Some(&key) {
            return Ok(false);
        }
        self.conn.configure_window(
            win,
            &ConfigureWindowAux::new()
                .x(x)
                .y(y)
                .width(w)
                .height(h)
                .border_width(border),
        )?;
        self.geom_cache.borrow_mut().insert(win, key);
        Ok(true)
    }

    fn place_cached(&self, win: Window, x: i32, y: i32, w: i32, h: i32) -> Result {
        self.configure_cached(win, x, y, w, h, 0)?;
        Ok(())
    }

    /// dwm's `configure()`: tells the client the geometry the WM settled on.
    /// The X server also reports the real configure, but the explicit one is
    /// what dwm sends and some clients rely on it to repaint during a drag.
    fn send_configure(
        &self,
        win: Window,
        rect: Rect,
        inner_w: u32,
        inner_h: u32,
        border: u32,
    ) -> Result {
        let event = ConfigureNotifyEvent {
            response_type: CONFIGURE_NOTIFY_EVENT,
            sequence: 0,
            event: win,
            window: win,
            above_sibling: NONE,
            x: rect.x as i16,
            y: rect.y as i16,
            width: inner_w as u16,
            height: inner_h as u16,
            border_width: border as u16,
            override_redirect: false,
        };
        self.conn
            .send_event(false, win, EventMask::STRUCTURE_NOTIFY, event)?;
        Ok(())
    }

    /// Configures one client and sends dwm's synthetic `ConfigureNotify` only
    /// when the geometry changed. Returns the geometry actually applied, after
    /// `WM_NORMAL_HINTS` for floating clients, and whether it changed.
    fn place_client(&self, c: &Client, rect: Rect) -> Result<(Rect, bool)> {
        let border = client_border(c);
        // A fullscreen client owns the whole monitor: no border and no size
        // hint clamping, so its content matches the screen exactly.
        let rect = if c.floating && !c.fullscreen {
            constrain_size(&c.hints, rect, border, self.bar_h())
        } else {
            rect
        };
        let inner_w = (rect.w as i32 - 2 * border).max(1) as u32;
        let inner_h = (rect.h as i32 - 2 * border).max(1) as u32;
        let changed = self.configure_cached(
            c.win,
            rect.x,
            rect.y,
            inner_w as i32,
            inner_h as i32,
            border as u32,
        )?;
        if changed {
            self.send_configure(c.win, rect, inner_w, inner_h, border as u32)?;
        }
        Ok((rect, changed))
    }

    /// dwm's `resizebarwin()`, without the systray, Finder, notification and
    /// MPRIS sections. The clock window is placed by the clock thread.
    fn resize_bar_win(&self, mi: usize) -> Result {
        let m = &self.monitors[mi];
        let bh = self.bar_h();
        // If any fullscreen client is on this monitor, hide the bar entirely.
        let has_fullscreen = self.clients.iter().any(|c| c.fullscreen && c.mon == mi && self.is_visible(c));
        if !m.showbar || has_fullscreen {
            for win in [
                m.barwin,
                m.bartitlewin,
                m.barcenterwin,
                m.barkbwin,
                m.barrightwin,
            ] {
                self.place_cached(win, m.wx, m.by, 1, bh)?;
                self.set_mapped(win, false)?;
            }
            if mi == self.selmon {
                self.set_mapped(self.tray.window, false)?;
            }
            self.set_mapped(m.mpris_markerwin, false)?;
            self.unmap_finder_marker(mi)?;
            self.center_shown.borrow_mut()[mi] = false;
            return Ok(());
        }

        let b = self.barwidths(mi);
        let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
        let rx = self.rightbar_x(mi);

        self.place_cached(m.barwin, lx, m.by, b.tw, bh)?;
        self.set_mapped(m.barwin, true)?;

        let kx = lx + b.tw + BARGAP;
        self.place_cached(m.barkbwin, kx, m.by, b.kw, bh)?;
        self.set_mapped(m.barkbwin, true)?;

        let titlex = kx + b.kw + BARGAP;
        self.place_cached(m.bartitlewin, titlex, m.by, b.tlw, bh)?;
        self.set_mapped(m.bartitlewin, true)?;

        let finder_center = mi == self.selmon && self.finder.is_active();
        let notification_center =
            mi == self.selmon && !finder_center && self.notification.is_center_active();
        let mut show_clock = if finder_center {
            if let Some((cx, cy, cw, ch)) = self.finder_place(mi) {
                self.place_cached(m.barcenterwin, cx, cy, cw as i32, ch as i32)?;
            }
            true
        } else if notification_center {
            if let Some((cx, _width)) = self.clock_place(mi) {
                let (nw, nh) = self.notification.popup_size(bh);
                self.place_cached(m.barcenterwin, cx, m.by, nw as i32, nh as i32)?;
            }
            self.clock_place(mi).is_some()
        } else {
            if let Some((cx, width)) = self.clock_place(mi) {
                self.place_cached(m.barcenterwin, cx, m.by, width, bh)?;
            }
            self.clock_place(mi).is_some()
        };
        if self.monitor_fullscreen(mi) {
            show_clock = false;
        }
        self.set_mapped(m.barcenterwin, show_clock)?;
        let was_shown = self.center_shown.borrow()[mi];
        if was_shown != show_clock {
            self.center_shown.borrow_mut()[mi] = show_clock;
            if show_clock {
                self.force_windows.borrow_mut().insert(m.barcenterwin);
                if notification_center {
                    self.notification_force.set(true);
                }
            }
        }

        let right_h = if self.mpris_hovered && mi == self.selmon && self.mpris.present {
            bh * 2
        } else {
            bh
        };
        self.place_cached(m.barrightwin, rx, m.by, b.rw, right_h)?;
        self.set_mapped(m.barrightwin, true)?;

        if mi == self.selmon {
            let tw = self.tray_width(mi);
            self.place_cached(
                self.tray.window,
                self.tray_x(mi),
                m.by,
                tw.max(1),
                bh,
            )?;
            self.set_mapped(self.tray.window, tw > 0)?;
        }
        Ok(())
    }

    /// Put one monitor's bar windows back in the top layer, bottom-to-top.
    ///
    /// The bars are override-redirect, but X has no permanent "always on top"
    /// layer: any `StackMode::ABOVE` on a client (floating windows,
    /// `_NET_WM_STATE_ABOVE`, drag zones) or any map of a client window can
    /// bury them. Raising the whole group in creation order restores both the
    /// layer and the sections' relative stacking. The transparent center and
    /// the two markers go last so they stay above their neighbouring sections.
    fn raise_bar_layer(&self, mi: usize) -> Result {
        // Unmanaged OSDs and hintless popups must stay above clients too, but
        // the bar stays above them. The menu layers are restored at the end.
        self.raise_overlays();
        let m = &self.monitors[mi];
        for win in [
            m.barwin,
            m.bartitlewin,
            m.barkbwin,
            m.barrightwin,
            m.barcenterwin,
            if mi == self.selmon { self.tray.window } else { 0 },
            m.mpris_markerwin,
            m.finder_markerwin,
        ] {
            if win != 0 {
                self.conn.configure_window(
                    win,
                    &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
                )?;
            }
        }
        // The bar layer is rebuilt on every map, focus change and `_NET_WM_STATE_ABOVE`
        // client. Put menus back on top in the same pass, otherwise a menu is
        // immediately buried by the bar (or client) that caused the restack.
        self.raise_tray_menus();
        self.raise_popups();
        Ok(())
    }

    fn raise_bars(&self) -> Result {
        for mi in 0..self.monitors.len() {
            self.raise_bar_layer(mi)?;
        }
        Ok(())
    }

    /// True for root children this WM stacks itself, so stacking notifications
    /// for them must not trigger another `raise_bars()` round trip.
    fn is_our_window(&self, win: Window) -> bool {
        self.tray.window == win
            || self.tray_menus.borrow().contains(&win)
            || self.popup_windows.borrow().contains(&win)
            || self.overlay_windows.borrow().contains(&win)
            || self.supporting_wm_check == win
            || self.monitors.iter().any(|m| {
                [
                    m.barwin,
                    m.bartitlewin,
                    m.barkbwin,
                    m.barcenterwin,
                    m.barrightwin,
                    m.mpris_markerwin,
                    m.finder_markerwin,
                ]
                .contains(&win)
            })
            || self.clients.iter().any(|c| {
                c.win == win
                    || c.edge_wins.contains(&win)
            })
    }

    /// Raise or restore the top-right bar and its volume marker relative to
    /// client windows. On hover the panel grows to two rows and can overlap a
    /// floating client, so while expanded it must sit on top of every window;
    /// otherwise the extra row is hidden and its controls cannot be clicked.
    ///
    /// Both windows select `EnterWindow`/`LeaveWindow`, so the order of the two
    /// configure requests matters. Raising the panel with a bare `ABOVE` first
    /// briefly puts it over the marker; X then reports a LeaveNotify on the
    /// marker and an EnterNotify on the panel, the hover flags flip, the next
    /// frame restacks again, and the marker flickers. Raise the marker first,
    /// then slide the panel in directly beneath it with a sibling-relative
    /// `BELOW`. When the order is already correct both requests are no-ops, so
    /// no crossing events are synthesized.
    fn stack_mpris_bar(&self, mi: usize, above: bool) -> Result {
        let m = &self.monitors[mi];
        if above {
            self.conn.configure_window(
                m.mpris_markerwin,
                &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
            )?;
            self.conn.configure_window(
                m.barrightwin,
                &ConfigureWindowAux::new()
                    .sibling(m.mpris_markerwin)
                    .stack_mode(StackMode::BELOW),
            )?;
            // An open menu stays on top of the expanded panel as well.
            self.raise_tray_menus();
            self.raise_popups();
        } else {
            // Restore the bar's place in the top layer. Lowering with a bare
            // `BELOW` would put the collapsed panel under *all* root children,
            // including clients, which is the opposite of always-on-top.
            self.raise_bar_layer(mi)?;
        }
        Ok(())
    }

    /// Keep the ARGB clock-bar window and its white marker above every other
    /// root child while Finder is open. The popup is an override-redirect
    /// extension of the clock bar, so it must follow the same top layer as the
    /// floating clients that the layout raises with `StackMode::ABOVE`.
    /// Something else was just raised above the Finder popup. On the next bar
    /// refresh `stack_finder()` must put it back on top.
    fn invalidate_finder_stacking(&self) {
        if self.finder.is_active() || self.notification.is_center_active() {
            for m in &self.monitors {
                m.finder_stacked.set(false);
            }
        }
    }

    fn stack_finder(&self, mi: usize, above: bool) -> Result {
        let m = &self.monitors[mi];
        // The `true` path runs on every popup frame; the cached flag keeps it
        // from issuing restacks (and crossing events) when nothing moved.
        // Lowering only runs on close, so always restore the whole layer.
        if above && m.finder_stacked.get() {
            return Ok(());
        }
        if above {
            let aux = ConfigureWindowAux::new().stack_mode(StackMode::ABOVE);
            self.conn.configure_window(m.barcenterwin, &aux)?;
            if m.finder_markerwin != 0 {
                self.conn.configure_window(m.finder_markerwin, &aux)?;
            }
        } else {
            // Put the center window back in the bar layer instead of lowering
            // it below clients: a bare `BELOW` buries the normal clock too.
            self.raise_bar_layer(mi)?;
        }
        m.finder_stacked.set(above);
        Ok(())
    }

    /// dwm's `notification_update_wm_class`. Finder overrides a notification,
    /// and the history gets its own instance name while sharing `notify`.
    /// Only the center window changes class; the bar sections stay `dwm`.
    fn set_bar_class(&self, mi: usize) -> Result {
        let kind = self.center_kind(mi);
        if self.center_kind.borrow()[mi] == kind {
            return Ok(());
        }
        let class: &[u8] = match kind {
            CenterKind::Finder => b"finder\0finder\0",
            CenterKind::Notification => b"notification\0notify\0",
            CenterKind::History => b"notification-history\0notify\0",
            CenterKind::Dwm => b"dwm\0dwm\0",
        };
        self.conn
            .change_property8(
                PropMode::REPLACE,
                self.monitors[mi].barcenterwin,
                AtomEnum::WM_CLASS,
                AtomEnum::STRING,
                class,
            )?
            .check()?;
        self.center_kind.borrow_mut()[mi] = kind;
        Ok(())
    }

    /// Refreshes the center WM_CLASS after Finder or notification state changed.
    fn sync_center_class(&self) -> Result {
        for mi in 0..self.monitors.len() {
            self.set_bar_class(mi)?;
        }
        Ok(())
    }

    fn layout_mon(&self, mi: usize) -> Vec<(Window, Rect)> {
        let mut out = Vec::new();
        let vis: HashSet<Window> = self.tiled_order(mi).into_iter().collect();
        let gaps = self.effective_gaps(mi);
        if let Some(tree) = &self.monitors[mi].tree {
            tree.layout(self.tile_area(mi), &vis, &gaps, &mut out);
        }
        out
    }

    fn monitor_at(&self, x: i32, y: i32) -> usize {
        self.monitors
            .iter()
            .position(|m| m.rect.contains(x, y))
            .unwrap_or(0)
    }

    fn screen_rect(&self) -> Result<Rect> {
        let geom = self.conn.get_geometry(self.root)?.reply()?;
        Ok(Rect {
            x: 0,
            y: 0,
            w: geom.width as u32,
            h: geom.height as u32,
        })
    }

    fn query_monitor_rects(&self) -> Result<Vec<Rect>> {
        let screen = self.screen_rect()?;
        let reply = randr::get_monitors(&self.conn, self.root, true)?.reply()?;
        let mut rects: Vec<Rect> = reply
            .monitors
            .iter()
            .map(|m| Rect {
                x: m.x as i32,
                y: m.y as i32,
                w: m.width as u32,
                h: m.height as u32,
            })
            .collect();
        if rects.is_empty() {
            rects.push(screen);
        }
        Ok(rects)
    }

    fn new_monitor(rect: Rect) -> Monitor {
        Monitor {
            wx: rect.x,
            wy: rect.y,
            ww: rect.w as i32,
            wh: rect.h as i32,
            by: 0,
            rect,
            tree: None,
            gaps: Gaps {
                oh: config::GAPPOH,
                ov: config::GAPPOV,
                ih: config::GAPPIH,
                iv: config::GAPPIV,
            },
            tagset: [1, 1],
            seltags: 0,
            curtag: 1,
            prevtag: 1,
            showbar: true,
            showbars: [true; TAGS + 1],
            sel: None,
            barwin: 0,
            bartitlewin: 0,
            barkbwin: 0,
            barcenterwin: 0,
            barrightwin: 0,
            mpris_markerwin: 0,
            finder_markerwin: 0,
            colormap: 0,
            finder_marker_stacked: Cell::new(false),
            finder_marker_pos: Cell::new(None),
            finder_stacked: Cell::new(false),
        }
    }

    /// Reinitializes monitor geometry and bar placement after resolution or
    /// monitor layout changes (e.g. xrandr), similar to dwm's updategeom().
    fn updategeom(&mut self) -> Result {
        let new_rects = self.query_monitor_rects()?;
        let same = new_rects.len() == self.monitors.len()
            && new_rects
                .iter()
                .zip(&self.monitors)
                .all(|(r, m)| *r == m.rect);
        if same {
            return Ok(());
        }

        if self.finder.is_active() {
            let _ = self.finder_close();
        }

        while self.monitors.len() > new_rects.len() {
            let old = self.monitors.len() - 1;
            let target = 0usize.min(self.monitors.len().saturating_sub(2));
            let moved: Vec<Window> = self
                .clients
                .iter()
                .filter(|c| c.mon == old)
                .map(|c| c.win)
                .collect();
            for win in moved {
                if let Some(ci) = self.clients.iter().position(|c| c.win == win) {
                    self.monitors[old].tree =
                        self.monitors[old].tree.take().and_then(|t| t.remove(win));
                    if self.monitors[old].sel == Some(win) {
                        self.monitors[old].sel = None;
                    }
                    let area = self.tile_area(target);
                    let tags = self.tags_of(target);
                    {
                        let t = &mut self.monitors[target];
                        t.tree = Some(tree::append(t.tree.take(), win, area));
                        if t.sel.is_none() {
                            t.sel = Some(win);
                        }
                    }
                    self.clients[ci].mon = target;
                    self.clients[ci].tags = tags;
                    let _ = self.set_client_desktop(win, tags);
                    let _ = self.set_rwm_monitor(win, target);
                }
            }
            self.destroy_monitor_ui(old);
            self.monitors.pop();
            self.mpris_bar_raised.borrow_mut().pop();
            self.center_shown.borrow_mut().pop();
            self.center_kind.borrow_mut().pop();
        }

        while self.monitors.len() < new_rects.len() {
            let rect = new_rects[self.monitors.len()];
            self.monitors.push(Self::new_monitor(rect));
            self.mpris_bar_raised.borrow_mut().push(false);
            self.center_shown.borrow_mut().push(false);
            self.center_kind.borrow_mut().push(CenterKind::Dwm);
            let mi = self.monitors.len() - 1;
            self.create_monitor_ui(mi)?;
        }

        for (mi, rect) in new_rects.into_iter().enumerate() {
            let m = &mut self.monitors[mi];
            m.rect = rect;
            m.wx = rect.x;
            m.wy = rect.y;
            m.ww = rect.w as i32;
            m.wh = rect.h as i32;
        }

        // Clamp and follow the pointer to a valid monitor after reconfiguration.
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        self.selmon = self
            .monitor_at(pointer.root_x as i32, pointer.root_y as i32)
            .min(self.monitors.len().saturating_sub(1));
        for mi in 0..self.monitors.len() {
            self.ensure_sel(mi);
        }

        // Force a full bar redraw/reposition after geometry changes.
        self.bar_drawn.borrow_mut().clear();
        self.clock_drawn.borrow_mut().clear();
        self.geom_cache.borrow_mut().clear();
        self.bar_dirty = true;
        for c in &self.clients {
            let _ = self.set_rwm_monitor(c.win, c.mon);
        }
        self.arrange()
    }

    /// Picks the first visible client on `mi` when the selection is hidden.
    fn ensure_sel(&mut self, mi: usize) {
        let keep = self.monitors[mi].sel.is_some_and(|w| {
            self.clients
                .iter()
                .any(|c| c.win == w && c.mon == mi && self.is_visible(c))
        });
        if !keep {
            self.monitors[mi].sel = self.stack_order(mi).first().copied();
        }
    }

    /// Whether an EnterNotify on `win` should leave the current selection
    /// alone. Tiled clients behind a fullscreen stack are unmapped, so the
    /// pointer can only ever cross the fullscreen window on top. Letting that
    /// crossing reset the selection would undo an explicit focus (Alt+Tab or
    /// the just-mapped client we are about to fullscreen). A mapped floating
    /// overlay is above the stack, though, so moving onto the fullscreen
    /// client from one should still select it.
    fn keep_selection_entering_fullscreen(&self, win: Window, mon: usize) -> bool {
        if self.selmon != mon
            || !self
                .clients
                .iter()
                .any(|c| c.win == win && c.fullscreen && c.mon == mon)
        {
            return false;
        }
        let Some(sel) = self.monitors[mon].sel else {
            return false;
        };
        let Some(sel_client) = self.clients.iter().find(|c| c.win == sel) else {
            return false;
        };
        if sel_client.mon != mon || !self.is_visible(sel_client) {
            return false;
        }
        let mapped = self
            .client_maps
            .borrow()
            .get(&sel)
            .is_some_and(|state| state.mapped);
        sel_client.fullscreen || !mapped
    }

    /// Selects the monitor currently under the pointer, as requested for
    /// workspace-changing keybinds in multi-monitor setups.
    fn sync_selmon_to_pointer(&mut self) -> Result {
        let p = self.conn.query_pointer(self.root)?.reply()?;
        self.activate_monitor_at(p.root_x as i32, p.root_y as i32)
    }

    /// Makes `mi` the selected monitor and focuses its selected client. This is
    /// used when the pointer crosses to another monitor so a window focused on
    /// the previous monitor no longer stays focused.
    fn activate_monitor_at(&mut self, x: i32, y: i32) -> Result {
        let mi = self.monitor_at(x, y);
        if mi == self.selmon {
            return Ok(());
        }
        self.selmon = mi;
        self.ensure_sel(mi);
        self.focus()?;
        self.bar_dirty = true;
        Ok(())
    }

    fn update_client_list(&self) -> Result {
        let wins: Vec<u32> = self.clients.iter().map(|c| c.win).collect();
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_client_list,
            AtomEnum::WINDOW,
            &wins,
        )?;
        Ok(())
    }

    fn update_client_list_stacking(&self) -> Result {
        // Bottom to top: reverse of clients list? clients is newest-first in our model;
        // stacking order in our model is roughly that order on top; for simplicity use clients order reversed
        let wins: Vec<u32> = self.clients.iter().rev().map(|c| c.win).collect();
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_client_list_stacking,
            AtomEnum::WINDOW,
            &wins,
        )?;
        Ok(())
    }

    fn update_active_window(&self) -> Result {
        let sel = self.monitors.get(self.selmon).and_then(|m| m.sel).unwrap_or(0);
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_active_window,
            AtomEnum::WINDOW,
            &[sel],
        )?;
        Ok(())
    }

    fn set_client_desktop(&self, win: Window, tags: u32) -> Result {
        let desk = if tags == 0 || tags == !0 {
            // treat all-set or invalid as sticky
            0xFFFFFFFFu32
        } else if tags.count_ones() != 1 {
            0xFFFFFFFFu32
        } else {
            tags.trailing_zeros()
        };
        if desk == 0xFFFFFFFF || desk < TAG_COUNT {
            let _ = self.conn.change_property32(
                PropMode::REPLACE,
                win,
                self.atoms.net_wm_desktop,
                AtomEnum::CARDINAL,
                &[desk],
            );
        }
        Ok(())
    }

    fn update_workarea(&self) -> Result {
        let mut data: Vec<u32> = Vec::new();
        for m in &self.monitors {
            let wa = self.work_area_for_monitor(m);
            data.push(wa.x.max(0) as u32);
            data.push(wa.y.max(0) as u32);
            data.push(wa.w);
            data.push(wa.h);
        }
        self.conn.change_property32(
            PropMode::REPLACE,
            self.root,
            self.atoms.net_workarea,
            AtomEnum::CARDINAL,
            &data,
        )?;
        Ok(())
    }

    fn work_area_for_monitor(&self, m: &Monitor) -> Rect {
        let mut wa = if m.showbar {
            if TOPBAR {
                Rect {
                    x: m.rect.x,
                    y: m.rect.y + self.bar_h(),
                    w: m.rect.w,
                    h: m.rect.h.saturating_sub(self.bar_h() as u32),
                }
            } else {
                Rect {
                    x: m.rect.x,
                    y: m.rect.y,
                    w: m.rect.w,
                    h: m.rect.h.saturating_sub(self.bar_h() as u32),
                }
            }
        } else {
            m.rect
        };
        // Heuristic STRUT application: only apply left to leftmost monitor, right to rightmost, etc.
        let min_x = self.monitors.iter().map(|mm| mm.rect.x).min().unwrap_or(0);
        let max_x = self.monitors.iter().map(|mm| mm.rect.x + mm.rect.w as i32).max().unwrap_or(0);
        let min_y = self.monitors.iter().map(|mm| mm.rect.y).min().unwrap_or(0);
        let max_y = self.monitors.iter().map(|mm| mm.rect.y + mm.rect.h as i32).max().unwrap_or(0);
        let is_leftmost = m.rect.x == min_x;
        let is_rightmost = (m.rect.x + m.rect.w as i32) == max_x;
        let is_topmost = m.rect.y == min_y;
        let is_bottommost = (m.rect.y + m.rect.h as i32) == max_y;
        // Apply STRUTs: use cached atoms
        for c in &self.clients {
            let mut v4: Option<[u32; 4]> = None;
            if let Ok(prop) = self.conn.get_property(false, c.win, self.atoms.net_wm_strut_partial, AtomEnum::CARDINAL, 0, 12) {
                if let Ok(r2) = prop.reply() {
                    if let Some(vals) = r2.value32() {
                        let v: Vec<u32> = vals.collect();
                        if v.len() >= 4 {
                            v4 = Some([v[0], v[1], v[2], v[3]]);
                        }
                    }
                }
            }
            if v4.is_none() {
                if let Ok(prop) = self.conn.get_property(false, c.win, self.atoms.net_wm_strut, AtomEnum::CARDINAL, 0, 4) {
                    if let Ok(r2) = prop.reply() {
                        if let Some(vals) = r2.value32() {
                            let v: Vec<u32> = vals.collect();
                            if v.len() >= 4 {
                                v4 = Some([v[0], v[1], v[2], v[3]]);
                            }
                        }
                    }
                }
            }
            if let Some(v) = v4 {
                let left = v[0] as i32;
                let right = v[1] as i32;
                let top = v[2] as i32;
                let bottom = v[3] as i32;
                if is_leftmost && left > 0 {
                    wa.x = wa.x.max(m.rect.x + left);
                }
                if is_topmost && top > 0 {
                    wa.y = wa.y.max(m.rect.y + top);
                }
                let right_edge = if is_rightmost && right > 0 {
                    (m.rect.x + m.rect.w as i32 - right).min(wa.x + wa.w as i32)
                } else {
                    wa.x + wa.w as i32
                };
                let bottom_edge = if is_bottommost && bottom > 0 {
                    (m.rect.y + m.rect.h as i32 - bottom).min(wa.y + wa.h as i32)
                } else {
                    wa.y + wa.h as i32
                };
                wa.w = (right_edge - wa.x).max(0) as u32;
                wa.h = (bottom_edge - wa.y).max(0) as u32;
            }
        }
        wa
    }

    /// Sets X input focus and remembers what rwm intended. FocusIn events on
    /// another window are then a reliable signal that somebody moved the
    /// keyboard behind our back, instead of being indistinguishable from a
    /// focus change rwm itself requested.
    fn set_focus_window(&mut self, win: Window, revert_to: InputFocus) -> Result {
        self.conn
            .set_input_focus(revert_to, win, CURRENT_TIME)?;
        self.intended_focus = Some(win);
        Ok(())
    }

    /// dwm's `focus()`: gives the selected window of the selected monitor the
    /// focus border colour and every other window the normal one.
    fn focus(&mut self) -> Result {
        let sel = self.monitors[self.selmon].sel;
        for c in &self.clients {
            let pixel = if Some(c.win) == sel {
                config::COL_SEL_BORDER
            } else {
                config::COL_NORM_BORDER
            };
            self.conn.change_window_attributes(
                c.win,
                &ChangeWindowAttributesAux::new().border_pixel(pixel),
            )?;
        }
        // Finder owns keyboard focus while it is modal. Layout and mapping work
        // may still update the selection and border colours, but must not hand
        // X input focus to a client behind the popup.
        if self.finder.is_active() {
            self.conn.flush()?;
            let _ = self.update_active_window();
            return Ok(());
        }
        let target = sel.unwrap_or(self.root);
        let mut focus_target = target;
        if sel.is_some_and(|w| self.clients.iter().any(|c| c.win == w && c.hidden)) {
            // Iconified windows are unmapped; X would refuse to focus them.
            // Drop the stale selection so _NET_ACTIVE_WINDOW does not name one.
            self.monitors[self.selmon].sel = None;
            focus_target = self.root;
        } else if let Some(win) = sel {
            if let Some(c) = self.clients.iter().find(|cc| cc.win == win) {
                if c.take_focus {
                    let ev = ClientMessageEvent::new(
                        32,
                        win,
                        self.atoms.wm_protocols,
                        [self.atoms.wm_take_focus, CURRENT_TIME, 0, 0, 0],
                    );
                    let _ = self.conn.send_event(false, win, EventMask::NO_EVENT, ev);
                }
                // If client does not want input and doesn't use take_focus, avoid focusing it
                if !c.wants_input && !c.take_focus {
                    focus_target = self.root;
                } else {
                    focus_target = win;
                }
            }
        } else {
            focus_target = self.root;
        }
        // RevertToParent, not PointerRoot: if a client is unmapped while it is
        // focused, PointerRoot silently hands the keyboard to whatever window
        // happens to be under the mouse. That leaves the border and
        // _NET_ACTIVE_WINDOW on the old client while picom sees another window
        // focused, which is exactly the overlap/Alt+Tab focus-loss symptom.
        self.set_focus_window(focus_target, InputFocus::PARENT)?;
        // Clear urgency/demands_attention on focused client
        if let Some(win) = sel {
            if let Some(idx) = self.clients.iter().position(|c| c.win == win) {
                if self.clients[idx].demands_attention || self.clients[idx].urgent {
                    self.clients[idx].demands_attention = false;
                    self.clients[idx].urgent = false;
                    let _ = self.sync_client_wm_state(&self.clients[idx]);
                }
            }
        }
        let _ = self.update_active_window();
        self.conn.flush()?;
        Ok(())
    }

    /// True when `win` is `ancestor` or one of its descendants. A client is
    /// allowed to move focus into its own input widget; that is still focus on
    /// the selected client as far as the WM and compositor are concerned.
    fn focus_within(&self, win: Window, ancestor: Window) -> Result<bool> {
        if win == ancestor {
            return Ok(true);
        }
        if win == NONE || ancestor == NONE || ancestor == self.root {
            return Ok(false);
        }
        let mut cur = win;
        // Bound the walk so a malicious child cannot keep us in the loop.
        for _ in 0..32 {
            let Ok(reply) = self.conn.query_tree(cur)?.reply() else {
                return Ok(false);
            };
            let parent = reply.parent;
            if parent == ancestor {
                return Ok(true);
            }
            if parent == NONE || parent == self.root {
                return Ok(false);
            }
            cur = parent;
        }
        Ok(false)
    }

    /// Reassert the selection when X input focus ends up somewhere rwm did not
    /// ask for. A client can call XSetInputFocus itself (some toolkits do on a
    /// pointer crossing) and an obscured window can keep the keyboard while
    /// rwm's border still claims another window is focused. Listening for
    /// FocusIn is what makes the visible focus state match the real one.
    fn focus_in(&mut self, _e: &FocusInEvent) -> Result {
        if self.finder.is_active() || self.notification.has_input_focus() {
            return Ok(());
        }
        let Some(intended) = self.intended_focus else {
            return Ok(());
        };
        // x11rb's FocusInEvent only carries the ancestor that reported the
        // crossing; ask the server for the real focus window (including a
        // child a client focused itself).
        let actual = self.conn.get_input_focus()?.reply()?.focus;
        if actual == intended || self.focus_within(actual, intended)? {
            return Ok(());
        }
        // XEMBED tray icons and the notification/Finder bar surface are
        // legitimate focus owners that do not change the client selection.
        if self.tray.contains(actual)
            || self.monitors.iter().any(|m| {
                m.barcenterwin == actual || m.finder_markerwin == actual || m.barwin == actual
            })
        {
            return Ok(());
        }
        if self.monitors[self.selmon].sel.is_some() {
            self.focus()?;
        }
        Ok(())
    }

    /// Record the initial X map state of a client we just adopted.
    fn track_client(&self, win: Window, mapped: bool) {
        self.client_maps.borrow_mut().insert(
            win,
            MapTracking {
                mapped,
                pending_unmaps: 0,
                published_iconic: None,
            },
        );
    }

    /// Unmap a client ourselves, counting the UnmapNotify it will generate so
    /// the event handler does not mistake it for the client withdrawing. X
    /// emits no event when the window is already unmapped, so only count (and
    /// send) when we believe it is mapped. Either way the client is iconic:
    /// the reason for the unmap (tag switch, fullscreen, iconify) does not
    /// change what panels must show.
    fn wm_unmap(&self, win: Window) -> Result {
        let send = {
            let mut maps = self.client_maps.borrow_mut();
            let Some(state) = maps.get_mut(&win) else {
                self.conn.unmap_window(win)?;
                return Ok(());
            };
            state.unmap()
        };
        if send {
            if let Err(err) = self.conn.unmap_window(win) {
                if let Some(state) = self.client_maps.borrow_mut().get_mut(&win) {
                    state.pending_unmaps = state.pending_unmaps.saturating_sub(1);
                }
                return Err(err.into());
            }
        }
        self.sync_map_state(win)
    }

    /// Map a visible client. Keep any pending unmap count: even after we remap,
    /// the earlier UnmapNotify can still be waiting in the event queue and
    /// must still be attributed to the WM, not to the client.
    fn wm_map(&self, win: Window) -> Result {
        if let Some(state) = self.client_maps.borrow_mut().get_mut(&win) {
            state.map();
        }
        self.conn.map_window(win)?;
        self.sync_map_state(win)
    }

    /// Consume one UnmapNotify. Returns true when it was caused by the client
    /// (rather than by an UnmapWindow request of ours) and the client was
    /// believed mapped at the time.
    fn consume_client_unmap(&self, win: Window) -> bool {
        let withdrawn = {
            let mut maps = self.client_maps.borrow_mut();
            let Some(state) = maps.get_mut(&win) else {
                return false;
            };
            state.consume_unmap()
        };
        if withdrawn {
            let _ = self.sync_map_state(win);
        }
        withdrawn
    }

    /// Unmap a client that is not visible on the current tag set.
    ///
    /// Drop the cached geometry for every hidden client, fullscreen ones
    /// included. Games often resize their render buffer on `UnmapNotify` or
    /// when they remap; without a fresh configure and synthetic
    /// `ConfigureNotify` on the way back, they keep the smaller tile size while
    /// the X window itself is fullscreen, leaving black borders. The reconfigure
    /// always uses the fullscreen geometry, so it cannot shrink the client out
    /// of fullscreen.
    fn unmap_hidden_client(&self, c: &Client) -> Result {
        self.geom_cache.borrow_mut().remove(&c.win);
        self.wm_unmap(c.win)
    }

    /// True when the WM currently keeps `win` unmapped, whatever the reason:
    /// an explicit iconify, a tag switch, a fullscreen client covering it, or
    /// a withdraw by the client itself. This is the state panels must see.
    fn is_iconic(&self, win: Window) -> bool {
        !self
            .client_maps
            .borrow()
            .get(&win)
            .is_some_and(|s| s.mapped)
    }

    /// Publish ICCCM `WM_STATE`. Panels use IconicState to show a client as
    /// minimized, so unmapping the X window alone is not enough to be iconic.
    /// Every unmap is iconic, not just Super+H: the property follows the map
    /// state we actually asked X for, not the explicit iconify flag.
    fn sync_wm_state(&self, c: &Client) -> Result {
        let iconic = self.is_iconic(c.win);
        let state = if iconic {
            WM_STATE_ICONIC
        } else {
            WM_STATE_NORMAL
        };
        self.conn.change_property32(
            PropMode::REPLACE,
            c.win,
            self.atoms.wm_state,
            self.atoms.wm_state,
            &[state, 0], // state, icon_window (None)
        )?;
        if let Some(s) = self.client_maps.borrow_mut().get_mut(&c.win) {
            s.published_iconic = Some(iconic);
        }
        Ok(())
    }

    /// Republish `WM_STATE` and `_NET_WM_STATE` after a map or unmap. Repeated
    /// layout passes write nothing until the published value changes.
    fn sync_map_state(&self, win: Window) -> Result {
        let iconic = self.is_iconic(win);
        if self
            .client_maps
            .borrow()
            .get(&win)
            .is_some_and(|s| s.published_iconic == Some(iconic))
        {
            return Ok(());
        }
        if let Some(c) = self.clients.iter().find(|c| c.win == win) {
            self.sync_wm_state(c)?;
            self.sync_client_wm_state(c)?;
        }
        Ok(())
    }

    /// Flip a client's hidden state, keeping the restore stack and both state
    /// properties in sync. Callers run `arrange()` afterwards to apply mapping.
    fn set_hidden(&mut self, win: Window, hidden: bool) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        if self.clients[idx].hidden == hidden {
            return Ok(());
        }
        self.clients[idx].hidden = hidden;
        self.iconified_stack.retain(|&w| w != win);
        if hidden {
            self.iconified_stack.push(win);
        }
        let c = &self.clients[idx];
        let _ = self.sync_client_wm_state(c);
        let _ = self.sync_map_state(win);
        Ok(())
    }

    /// Super+H: iconify the focused client. `arrange()` then unmaps it, lets its
    /// tile collapse and focuses the next visible client on the same monitor.
    fn iconify(&mut self) -> Result {
        let Some(win) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        self.set_hidden(win, true)?;
        self.arrange()
    }

    /// Map a hidden client, switching to its tag and monitor when needed so the
    /// restored window is actually on screen, then select and focus it.
    fn restore_client(&mut self, win: Window) -> Result {
        let Some((mi, tags)) = self
            .clients
            .iter()
            .find(|c| c.win == win)
            .map(|c| (c.mon, c.tags & TAGMASK))
        else {
            return Ok(());
        };
        self.set_hidden(win, false)?;
        self.selmon = mi;
        self.monitors[mi].sel = Some(win);
        if tags != 0 && tags != self.tags_of(mi) {
            // view() arranges and focuses the selection we just set.
            return self.view(tags);
        }
        self.arrange()
    }

    /// Super+Shift+H: restore the most recently iconified client, regardless of
    /// which window is focused now. Stale stack entries are skipped so repeated
    /// presses restore every window that was hidden, newest first.
    fn deiconify(&mut self) -> Result {
        while let Some(win) = self.iconified_stack.pop() {
            if self.clients.iter().any(|c| c.win == win && c.hidden) {
                return self.restore_client(win);
            }
        }
        Ok(())
    }

    fn apply_layout(&mut self) -> Result {
        let mut boxes: Vec<(Window, Rect, bool)> = Vec::new();
        // Every visible fullscreen client covers its own monitor. They form a
        // per-monitor stack, not a single owner: a second fullscreen request
        // must not unmap the older one. Monitors are independent, so monitor 1
        // and monitor 2 can each have their own fullscreen stack.
        let fullscreen: Vec<Vec<(usize, Window)>> = (0..self.monitors.len())
            .map(|mi| self.fullscreen_windows(mi))
            .collect();
        let fs_on = |mi: usize| fullscreen.get(mi).is_some_and(|v| !v.is_empty());

        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
            if fs_on(mi) {
                let mrect = self.monitors[mi].rect;
                let frect = Rect { x: mrect.x, y: mrect.y, w: mrect.w, h: mrect.h };
                for &(fidx, fwin) in &fullscreen[mi] {
                    let (rect, changed) = self.place_client(&self.clients[fidx], frect)?;
                    self.clients[fidx].geom = rect;
                    boxes.push((fwin, rect, changed));
                }
                continue;
            }
            for (win, r) in self.layout_mon(mi) {
                let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
                    continue;
                };
                let (rect, changed) = self.place_client(&self.clients[idx], r)?;
                self.clients[idx].geom = rect;
                boxes.push((win, rect, changed));
            }
        }

        // Oldest first, so the newest floating window ends up on top. Floating
        // windows are placed on fullscreen monitors too: an overlay opened
        // after the last fullscreen request must stay above it.
        let floating: Vec<(usize, Rect)> = self
            .clients
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, c)| c.floating && self.is_visible(c))
            .map(|(i, c)| (i, c.geom))
            .collect();
        for (idx, geom) in floating {
            let (rect, changed) = self.place_client(&self.clients[idx], geom)?;
            self.clients[idx].geom = rect;
            boxes.push((self.clients[idx].win, rect, changed));
        }
        // A tiled client being moved is visible, but its leaf is hidden from
        // layout_mon() so its siblings take the whole workspace. Keep its
        // zones at the last dragged position without reconfiguring the client.
        for c in self
            .clients
            .iter()
            .filter(|c| c.dragging && self.is_visible(c) && !fs_on(c.mon))
        {
            boxes.push((c.win, c.geom, false));
        }

        // On a fullscreen monitor every fullscreen client and every floating
        // window is mapped; tiled windows stay hidden behind the stack.
        // `view()` changes the tag set before `arrange()` runs, so windows from
        // the tag we just switched away from are no longer "visible" here and
        // must not be left mapped on top of the fullscreen stack.
        for c in &self.clients {
            let owner = fullscreen
                .get(c.mon)
                .and_then(|stack| stack.first().map(|(_, w)| *w));
            let shown = self.is_visible(c)
                && Self::map_allowed(c.win, c.floating, c.fullscreen, owner);
            if shown {
                self.wm_map(c.win)?;
            } else {
                self.unmap_hidden_client(c)?;
            }
        }
        for idx in 0..self.clients.len() {
            let win = self.clients[idx].win;
            match boxes.iter().find(|(w, _, _)| *w == win) {
                Some((_, r, changed)) => {
                    let zones = self.clients[idx].edge_wins;
                    let restack =
                        *changed || self.clients[idx].floating || self.clients[idx].dragging;
                    self.place_edge_zones(zones, win, *r, restack)?;
                }
                None => {
                    for zone in self.clients[idx].edge_wins {
                        self.conn.unmap_window(zone)?;
                        self.mapped_zones.borrow_mut().remove(&zone);
                        self.geom_cache.borrow_mut().remove(&zone);
                    }
                }
            }
        }
        // Restack overlay clients in the order they last asked to be on top:
        // adoption, Super+W or a fullscreen request all take a new token. A
        // dialog opened while a window is fullscreen sits above it; the next
        // fullscreen request covers the dialog again. Older fullscreen clients
        // stay mapped underneath at monitor size, so no client is unmapped just
        // because another one went fullscreen.
        let mut raised: Vec<(u64, Window)> = self
            .clients
            .iter()
            .filter(|c| (c.floating || c.fullscreen) && self.is_visible(c))
            .map(|c| (c.stack_seq, c.win))
            .collect();
        raised.sort_unstable_by_key(|(seq, _)| *seq);
        for (_, win) in raised {
            self.conn.configure_window(
                win,
                &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
            )?;
        }
        // The pass above puts floating clients above their own resize zones,
        // so put the zones back directly over them.
        for c in self.clients.iter().filter(|c| c.floating && self.is_visible(c)) {
            if let Some((_, r, _)) = boxes.iter().find(|(w, _, _)| *w == c.win) {
                self.place_edge_zones(c.edge_wins, c.win, *r, true)?;
            }
        }
        // Floating windows, drag zones and mapped clients are all raised into
        // the root child stack above. Restore the bar layer after them.
        self.raise_bars()?;
        self.invalidate_finder_stacking();
        self.conn.flush()?;
        Ok(())
    }

    /// Puts the hover zones of `win` over its outer box `r`, each directly above
    /// the window so that other windows still stack over it correctly.
    fn place_edge_zones(&self, zones: [Window; 8], win: Window, r: Rect, restack: bool) -> Result {
        let rects = tree::edge_zones(r, config::RESIZE_EDGE_PX);
        let mut mapped = self.mapped_zones.borrow_mut();
        for (zone, z) in zones.iter().zip(rects) {
            let changed = self.configure_cached(*zone, z.x, z.y, z.w as i32, z.h as i32, 0)?;
            if changed || restack || !mapped.contains(zone) {
                self.conn.configure_window(
                    *zone,
                    &ConfigureWindowAux::new()
                        .sibling(win)
                        .stack_mode(StackMode::ABOVE),
                )?;
            }
            if changed || !mapped.contains(zone) {
                self.conn.map_window(*zone)?;
                mapped.insert(*zone);
            }
        }
        Ok(())
    }

    /// Reconcile `mi`'s tiling tree with the current client list. A leaf can go
    /// missing when a drop lands where no tile contains the pointer, or when a
    /// window is moved between tags; once a visible client has no leaf it is
    /// skipped by `layout_mon()`, so it stops resizing, loses its resize zones
    /// and new windows appear to tile on top of it at full size. Hidden clients
    /// keep their leaves so their place in the layout survives a tag switch.
    fn sync_tree(&mut self, mi: usize) {
        let managed: HashSet<Window> = self.clients.iter().map(|c| c.win).collect();
        let mut leaves = Vec::new();
        if let Some(t) = &self.monitors[mi].tree {
            t.leaves(&mut leaves);
        }
        for win in leaves {
            if !managed.contains(&win) {
                let tree = &mut self.monitors[mi].tree;
                *tree = tree.take().and_then(|t| t.remove(win));
            }
        }

        let visible: Vec<Window> = self
            .clients
            .iter()
            .filter(|c| c.mon == mi && !c.floating && !c.dragging && self.is_visible(c))
            .map(|c| c.win)
            .collect();
        let area = self.tile_area(mi);
        for win in visible {
            let has_leaf = self.monitors[mi]
                .tree
                .as_ref()
                .is_some_and(|t| t.has_leaf(win));
            if !has_leaf {
                let tree = &mut self.monitors[mi].tree;
                *tree = Some(tree::append(tree.take(), win, area));
            }
        }
    }

    fn arrange(&mut self) -> Result {
        for mi in 0..self.monitors.len() {
            self.ensure_sel(mi);
            self.update_bar_pos(mi);
            self.sync_tree(mi);
        }
        self.apply_layout()?;
        // Minimal restack for above/below (avoid conflict: above wins)
        for c in self.clients.iter().rev() {
            if c.below && !c.above && self.is_visible(c) {
                let _ = self.conn.configure_window(c.win, &ConfigureWindowAux::new().stack_mode(StackMode::BELOW));
            }
        }
        for c in &self.clients {
            if c.above && self.is_visible(c) {
                let _ = self.conn.configure_window(c.win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE));
            }
        }
        // `_NET_WM_STATE_ABOVE` clients were just raised; keep the bar layer
        // above them in the same pass.
        self.raise_bars()?;
        self.focus()?;
        let _ = self.update_client_list();
        let _ = self.update_client_list_stacking();
        let _ = self.update_workarea();
        Ok(())
    }

    fn manage(&mut self, win: Window) -> Result {
        self.manage_on(win, None, None)
    }

    /// Adopt `win`. `initial_tags`/`initial_mon` are only passed by the startup
    /// scan: a window hidden on another workspace or monitor must not inherit
    /// the monitor/workspace that happens to be selected when rwm starts.
    fn manage_on(
        &mut self,
        win: Window,
        initial_tags: Option<u32>,
        initial_mon: Option<usize>,
    ) -> Result {
        let attrs = self
            .conn
            .get_window_attributes(win)
            .ok()
            .and_then(|c| c.reply().ok());
        if attrs
            .as_ref()
            .is_some_and(|a| a.override_redirect || a.class == WindowClass::INPUT_ONLY)
        {
            return Ok(());
        }
        if self.should_ignore_window(win) {
            return Ok(());
        }
        // A MapRequest arrives before the server maps the window (the WM has
        // SubstructureRedirect), so its attributes still say UNMAPPED there.
        // arrange() maps it right after adoption and updates the tracking.
        let initial_mapped = attrs
            .as_ref()
            .map(|a| a.map_state == x11rb::protocol::xproto::MapState::VIEWABLE)
            .unwrap_or(true);
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        let (mx, my) = (pointer.root_x as i32, pointer.root_y as i32);
        let mi = initial_mon
            .filter(|&m| m < self.monitors.len())
            .unwrap_or_else(|| self.monitor_at(mx, my));

        let hints = self.read_size_hints(win).unwrap_or_default();
        let transient_for = self.read_transient_for(win);
        let win_type = self.read_win_type(win);
        let is_modal = self.read_net_wm_state_modal(win);
        let initial_fullscreen = self
            .read_net_wm_state(win)
            .contains(&self.atoms.net_wm_state_fullscreen);
        let take_focus = self.supports_take_focus(win);
        let (wants_input, urgent) = self.read_wm_hints(win);

        // EWMH dialog-like types, transients and modal windows float; so do
        // windows whose size hints allow exactly one size, like updater popups
        // that forget to set an EWMH window type.
        let should_float = wants_floating(win_type, transient_for, is_modal, &hints);

        // Dock/Desktop: for now, do not tile normally in a heavy way; float them out of the way
        let is_dock_or_desktop = matches!(win_type, WinType::Dock | WinType::Desktop);

        if !should_float && !is_dock_or_desktop {
            let work = self.tile_area(mi);
            let restore = initial_mon.is_some();
            let target = if restore {
                None
            } else {
                let leaves = self.layout_mon(mi);
                leaves
                    .iter()
                    .copied()
                    .find(|(_, r)| r.contains(mx, my))
                    .or(leaves.last().copied())
            };
            let tree = &mut self.monitors[mi].tree;
            match target {
                Some((target, rect)) => {
                    let (new_first, side_by_side) = tree::split_for_drop(rect, (mx, my));
                    if let Some(t) = tree.as_mut() {
                        t.insert(target, win, new_first, side_by_side);
                    }
                }
                None => {
                    let t = tree::append(tree.take(), win, work);
                    *tree = Some(t);
                }
            }
        }

        let tags = initial_tags.unwrap_or_else(|| self.tags_of(mi));
        let mut geom = Rect { x: 0, y: 0, w: 0, h: 0 };
        if should_float || is_dock_or_desktop {
            // Dialogs and other requested-floating windows get their size from
            // WM_NORMAL_HINTS when available, then center below the bar or on
            // the transient parent. An explicit hint position wins over both.
            let parent = self.transient_geometry(transient_for, mi);
            geom = floating_geometry(&hints, self.work(mi), parent, BORDERPX);
        }

        let stack_seq = self.next_stack_seq();
        let mut edge_wins = [NONE; 8];
        for (i, slot) in edge_wins.iter_mut().enumerate() {
            let zone = self.conn.generate_id()?;
            self.conn.create_window(
                0,
                zone,
                self.root,
                0,
                0,
                1,
                1,
                0,
                WindowClass::INPUT_ONLY,
                x11rb::COPY_FROM_PARENT,
                &CreateWindowAux::new()
                    .event_mask(EventMask::BUTTON_PRESS)
                    .cursor(self.resize_cursor(Some(tree::ZONE_EDGES[i]))),
            )?;
            *slot = zone;
        }
        self.clients.insert(
            0,
            Client {
                win,
                tags,
                mon: mi,
                floating: should_float || is_dock_or_desktop,
                float_override: None,
                stack_seq,
                dragging: false,
                geom,
                auto_place: true,
                hints,
                edge_wins,
                transient_for,
                win_type,
                is_modal,
                fullscreen: false,
                maximized_horz: false,
                maximized_vert: false,
                above: false,
                below: false,
                demands_attention: false,
                hidden: false,
                sticky: false,
                skip_taskbar: false,
                skip_pager: false,
                saved_geom: None,
                saved_floating: false,
                take_focus,
                wants_input,
                urgent,
            },
        );
        self.track_client(win, initial_mapped);
        self.selmon = mi;
        self.monitors[mi].sel = Some(win);
        // Every managed client gets both state properties. A client adopted
        // while unmapped is iconic from the start, not just one hidden later.
        let _ = self.sync_map_state(win);
        let _ = self.set_client_desktop(win, tags);
        let _ = self.set_rwm_monitor(win, mi);
        if urgent {
            if let Some(c) = self.clients.iter().find(|cc| cc.win == win) {
                let _ = self.sync_client_wm_state(c);
            }
        }
        self.conn.change_window_attributes(
            win,
            &ChangeWindowAttributesAux::new()
                .event_mask(
                    EventMask::ENTER_WINDOW
                        | EventMask::PROPERTY_CHANGE
                        | EventMask::FOCUS_CHANGE,
                ),
        )?;
        self.grab_buttons(win)?;
        // Some clients set _NET_WM_STATE_FULLSCREEN on the window before
        // mapping instead of sending a _NET_WM_STATE message. Honor that
        // initial state so they do not need a manual keybind toggle.
        if initial_fullscreen && !self.clients.iter().any(|c| c.win == win && c.fullscreen) {
            self.toggle_fullscreen_for(win)?;
        } else {
            self.arrange()?;
        }
        Ok(())
    }

    fn unmanage(&mut self, win: Window) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let client = self.clients.remove(idx);
        self.iconified_stack.retain(|&w| w != win);
        self.client_maps.borrow_mut().remove(&win);
        self.name_cache.borrow_mut().remove(&win);
        self.icon_cache.borrow_mut().remove(&win);
        self.geom_cache.borrow_mut().remove(&win);
        for zone in client.edge_wins {
            self.conn.destroy_window(zone)?;
            self.geom_cache.borrow_mut().remove(&zone);
            self.mapped_zones.borrow_mut().remove(&zone);
        }
        let m = &mut self.monitors[client.mon];
        m.tree = m.tree.take().and_then(|t| t.remove(win));
        if m.sel == Some(win) {
            m.sel = None;
        }
        self.arrange()
    }

    fn client_name(&self, win: Window) -> String {
        if let Some(name) = self.name_cache.borrow().get(&win) {
            return name.clone();
        }
        let utf8 = self
            .conn
            .get_property(
                false,
                win,
                self.atoms.net_wm_name,
                self.atoms.utf8_string,
                0,
                256,
            )
            .ok()
            .and_then(|c| c.reply().ok());
        let name = if let Some(r) = utf8.filter(|r| !r.value.is_empty()) {
            String::from_utf8_lossy(&r.value).into_owned()
        } else {
            self.conn
                .get_property(false, win, AtomEnum::WM_NAME, AtomEnum::STRING, 0, 256)
                .ok()
                .and_then(|c| c.reply().ok())
                .map(|r| String::from_utf8_lossy(&r.value).into_owned())
                .unwrap_or_default()
        };
        self.name_cache.borrow_mut().insert(win, name.clone());
        name
    }

    /// AnDWM's `updateicon()` + `geticonprop()` for the bar: decode the
    /// selected client's `_NET_WM_ICON` once and reuse it until that property
    /// changes. A missing icon is cached as `None` so idle frames do not keep
    /// asking clients for a property they never set.
    fn client_icon(&self, win: Window) -> Option<crate::icon::ClientIcon> {
        if let Some(cached) = self.icon_cache.borrow().get(&win) {
            return cached.clone();
        }
        let icon = self.read_client_icon(win);
        self.icon_cache.borrow_mut().insert(win, icon.clone());
        icon
    }

    fn read_client_icon(&self, win: Window) -> Option<crate::icon::ClientIcon> {
        let prop = self
            .conn
            .get_property(
                false,
                win,
                self.atoms.net_wm_icon,
                AtomEnum::ANY,
                0,
                u32::MAX,
            )
            .ok()?
            .reply()
            .ok()?;
        if prop.format != 32 || prop.value.len() < 12 {
            return None;
        }
        // 32-bit X11 properties are arrays of native-endian cardinals.
        let data: Vec<u32> = prop
            .value
            .chunks_exact(4)
            .map(|b| u32::from_ne_bytes([b[0], b[1], b[2], b[3]]))
            .collect();
        let id = self.icon_seq.get() + 1;
        let icon = crate::icon::client_icon(&data, CLIENT_ICON_SIZE, id)?;
        self.icon_seq.set(id);
        Some(icon)
    }

    /// Redraws every shown bar. Returns true when the clock text changed.
    pub fn update_clock(&mut self) -> bool {
        let now = now_clock();
        if now == self.clock {
            return false;
        }
        self.clock = now;
        true
    }

    /// Maps a normalized level to the one-bar dBFS meter. `CLOCK_METER_MIN_DB`
    /// is 0 px and full scale is `CLOCK_ANIM_EXTRA` px.
    fn clock_extra_from_rms(normalized_rms: f32) -> i32 {
        let db = if normalized_rms > 1e-8 {
            20.0 * normalized_rms.log10()
        } else {
            -100.0
        };
        // Expand around the expected normalized peak so quiet passages drop
        // much lower and beats push higher, instead of hovering at one level.
        let center = 20.0 * (config::CLOCK_RMS_TARGET * config::CLOCK_EXPECTED_CREST).log10();
        let db = (center + (db - center) * config::CLOCK_DYNAMIC_EXPAND)
            .clamp(config::CLOCK_METER_MIN_DB, 0.0);
        let span = -config::CLOCK_METER_MIN_DB;
        let px = (db - config::CLOCK_METER_MIN_DB) / span * config::CLOCK_ANIM_EXTRA as f32;
        let step = config::CLOCK_ANIM_STEP.max(1);
        let raw = px as i32;
        ((raw / step) * step).clamp(0, config::CLOCK_ANIM_EXTRA)
    }

    /// Adapts a linear gain so `rms` lands near `CLOCK_RMS_TARGET`. Near silence
    /// the previous gain is held, and changes are smoothed in log (dB) space
    /// with the same time constant in both directions.
    fn adaptive_gain(gain: f32, rms: f32, dt: f32) -> f32 {
        let desired = if rms >= config::CLOCK_RMS_GATE {
            (config::CLOCK_RMS_TARGET / rms.max(config::CLOCK_RMS_FLOOR))
                .clamp(config::CLOCK_GAIN_MIN, config::CLOCK_GAIN_MAX)
        } else {
            gain
        };
        let alpha = 1.0 - (-dt / config::CLOCK_GAIN_ADAPT_SECS).exp();
        let current = gain.max(1e-6).ln();
        let target = desired.max(1e-6).ln();
        (current + (target - current) * alpha).exp()
    }

    /// Samples the PipeWire RMS/peak on the shared `BAR_TICK` grid. The RMS
    /// drives the adaptive gain (normalization); the normalized peak goes
    /// straight to the meter. Returns true when the quantized width changed.
    pub fn update_clock_anim(&mut self) -> bool {
        let Some(level) = self.clock_level.as_ref() else {
            return false;
        };
        let now = Instant::now();
        let elapsed = now.duration_since(self.clock_anim_last);
        if elapsed + TICK_GRACE < BAR_TICK {
            return false;
        }
        self.clock_anim_last = now;

        // Cap long gaps (e.g. while a popup owns the center window) so the
        // gain does not jump in one step when animation resumes.
        let dt = elapsed.as_secs_f32().min(0.1);
        let (rms, peak) = crate::sound::read(level);
        self.clock_gain = Self::adaptive_gain(self.clock_gain, rms, dt);
        let extra = Self::clock_extra_from_rms(peak * self.clock_gain);
        if extra == self.clock_extra {
            return false;
        }
        self.clock_extra = extra;
        true
    }

    /// Redraws every shown bar. Returns true when the status text changed.
    pub fn update_status(&mut self) -> bool {
        let new_status = self.status.sample_with_mpris(Some(&self.mpris));
        if new_status.key() != self.bar_status.key() {
            self.bar_status = new_status;
            true
        } else {
            false
        }
    }

    pub fn update_mpris(&mut self) -> bool {
        let mut latest = None;
        while let Ok(snapshot) = self.mpris_rx.try_recv() {
            latest = Some(snapshot);
        }
        let Some(snapshot) = latest else {
            return false;
        };

        let scroll_text = if snapshot.present && snapshot.playing {
            snapshot.scroll_text()
        } else {
            String::new()
        };
        if scroll_text != self.mpris_scroll_text {
            self.mpris_scroll_text = scroll_text;
            self.mpris_scroll_px = 0;
            self.mpris_scroll_next = Instant::now();
        }
        let artwork_changed = match (&self.mpris.artwork, &snapshot.artwork) {
            (None, None) => false,
            (Some(a), Some(b)) => !std::sync::Arc::ptr_eq(a, b),
            _ => true,
        };
        let changed = self.mpris.present != snapshot.present
            || self.mpris.playing != snapshot.playing
            || self.mpris.service != snapshot.service
            || self.mpris.artist != snapshot.artist
            || self.mpris.title != snapshot.title
            || self.mpris.art_url != snapshot.art_url
            || artwork_changed
            || self.mpris.progress != snapshot.progress
            || (self.mpris.volume - snapshot.volume).abs() > 0.001;
        self.mpris = snapshot;
        if !self.mpris.present {
            self.mpris_hovered = false;
            self.mpris_marker_hovered = false;
            self.mpris_volume_drag = false;
        }
        let status_changed = self.update_status();
        changed || status_changed
    }

    pub fn update_mpris_scroll(&mut self) -> bool {
        if !self.scroll_active() {
            self.mpris_scroll_next = Instant::now();
            return false;
        }
        let now = Instant::now();
        if now < self.mpris_scroll_next {
            return false;
        }
        self.mpris_scroll_next = now + BAR_TICK * SCROLL_TICKS;
        let text_width = self.metrics.text_width(&self.mpris_scroll_text);
        let cycle = (text_width + 32).max(1) as u32;
        self.mpris_scroll_px = (self.mpris_scroll_px + 1) % cycle;
        true
    }

    /// Whether a title is currently scrolling. Both the scroll step and the
    /// main loop's next deadline use this, so they cannot disagree.
    fn scroll_active(&self) -> bool {
        if !self.mpris.present || !self.mpris.playing || self.mpris_scroll_text.is_empty() {
            return false;
        }
        self.metrics.text_width(&self.mpris_scroll_text) + 16 > 240
    }

    /// Picks the earliest deadline for the next bar tick. Keeping this pure
    /// makes the 60 fps clock guarantee testable without a live `Wm`.
    fn bar_next_tick(
        now: Instant,
        status_next: Instant,
        clock_animate: bool,
        finder_active: bool,
        notification_center_active: bool,
        scroll_active: bool,
        scroll_next: Instant,
        finder_next: Option<Instant>,
        fullscreen_idle: bool,
    ) -> Instant {
        if fullscreen_idle {
            // The pointer's monitor is fullscreen and its bar is unmapped. No
            // animation, status or scrolling needs a 60 fps wakeup; only drain
            // channel-delivered notifications at a slow cadence.
            return now + FULLSCREEN_IDLE_POLL;
        }
        let mut next = status_next;
        // Clamp the poll timeout to BAR_TICK while the clock visualizer is
        // enabled. Sampling only when the last sample already differs from the
        // drawn width misses levels that arrive just after the deadline was
        // computed, which left idle animation at 1 fps. Finder and notification
        // history own the center window and freeze the animated clock width.
        if clock_animate && !finder_active && !notification_center_active {
            next = next.min(now + BAR_TICK);
        }
        if scroll_active {
            next = next.min(scroll_next);
        }
        if let Some(finder_next) = finder_next {
            next = next.min(finder_next);
        }
        next.min(now + IDLE_POLL)
    }

    pub fn needs_refresh(&self) -> bool {
        self.bar_dirty
    }

    pub fn finder_active(&self) -> bool {
        self.finder.is_active()
    }

    /// The bar is only animated on the monitor under the pointer. While that
    /// monitor shows a fullscreen window its bar is unmapped, so every per-tick
    /// bar task (PipeWire level math, status sampling, title scroll, repaints)
    /// can be skipped. Finder keeps its frames even on a fullscreen monitor.
    fn bar_suspended_now(&self) -> bool {
        !self.finder.is_active() && self.monitor_fullscreen(self.selmon)
    }

    /// Applies the current fullscreen-idle state. Called after every event batch
    /// so pointer crossings, fullscreen toggles and tag changes take effect even
    /// when the next timed refresh was still far away. The transition itself
    /// forces one normal refresh: entering hides the bar and clears any popup,
    /// leaving restores them from current values.
    pub fn sync_bar_suspended(&mut self) {
        let suspended = self.bar_suspended_now();
        if suspended == self.bar_suspended {
            return;
        }
        self.bar_suspended = suspended;
        if let Some(level) = self.clock_level.as_ref() {
            crate::sound::set_paused(level, suspended);
        }
        self.bar_dirty = true;
    }

    /// Deadline for the next bar tick. The main loop blocks on the X connection
    /// until this instant or an event, making this the only wakeup source.
    pub fn next_tick(&self) -> Instant {
        let now = Instant::now();
        let finder_active = self.finder.is_active();
        let finder_next = finder_active.then(|| {
            // dwm's run(): 0 ms while a frame is pending, 10 ms for ease/scroll,
            // 30 ms for the slower fades, 500 ms for the caret.
            self.finder.next_tick(now)
        });
        let notification_center_active = self.notification.is_center_active();
        let next = Self::bar_next_tick(
            now,
            self.status.next_sample(),
            config::CLOCK_ANIMATE,
            finder_active,
            notification_center_active,
            self.scroll_active(),
            self.mpris_scroll_next,
            finder_next,
            self.bar_suspended,
        );
        if !self.bar_suspended && self.notification.is_active() {
            next.min(self.notification.next_tick(now))
        } else {
            next
        }
    }

    /// Recomputes and updates the positions and widths of all bar windows.
    pub fn update_bars_geometry(&self) -> Result {
        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
        }
        Ok(())
    }

    /// dwm's `finder_popup_*` geometry: center the popup on the clock window
    /// and let it grow downward into a tall ARGB window.
    fn finder_place(&self, mi: usize) -> Option<(i32, i32, u32, u32)> {
        let m = &self.monitors[mi];
        let (x, width) = self.clock_place(mi)?;
        let (w, h) = self.finder.popup_size(self.bar_h() as u32);
        // `barwidths()` reserved exactly `w`, and `clock_window_width()` keeps
        // it unanimated, so the center window's own geometry is the popup.
        debug_assert_eq!(width, w as i32);
        Some((x, m.by, w, h))
    }

    fn pointer_root(&self) -> Result<(i32, i32)> {
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        Ok((pointer.root_x as i32, pointer.root_y as i32))
    }

    fn finder_pointer_monitor(&self) -> Result<usize> {
        let (x, y) = self.pointer_root()?;
        Ok(self.monitor_at(x, y))
    }

    /// dwm's `finder_focus_pointer()`: after an outside click, focus the client
    /// at the click position and move selection to its monitor. The button event
    /// carries root coordinates, so this does not depend on `query_pointer()`
    /// still reporting the clicked window immediately after the grab is released.
    fn finder_focus_pointer(&mut self, x: i32, y: i32) -> Result {
        let mi = self.monitor_at(x, y);
        let found = self.clients.iter().find_map(|c| {
            self.geometry(c.mon, c.win)
                .is_some_and(|r| r.contains(x, y))
                .then_some((c.win, c.mon))
        });
        if let Some((win, mon)) = found {
            self.selmon = mon;
            self.monitors[mon].sel = Some(win);
            self.focus()?;
        } else {
            self.selmon = mi;
            self.set_focus_window(self.root, InputFocus::PARENT)?;
            self.conn.flush()?;
        }
        Ok(())
    }

    fn finder_pointer_inside(&self, x: i32, y: i32) -> bool {
        self.finder_place(self.selmon)
            .is_some_and(|(px, py, w, h)| {
                x >= px && x < px + w as i32 && y >= py && y < py + h as i32
            })
    }

    fn unmap_finder_marker(&self, mi: usize) -> Result {
        let m = &self.monitors[mi];
        self.set_mapped(m.finder_markerwin, false)?;
        m.finder_marker_stacked.set(false);
        m.finder_marker_pos.set(None);
        Ok(())
    }

    /// dwm's `finder_marker()`, using the popup geometry already computed for
    /// `resizebarwin()` instead of an XTranslateCoordinates round trip.
    fn finder_marker(&self) -> Result {
        for mi in 0..self.monitors.len() {
            let offset = if self.finder.is_active() && mi == self.selmon {
                self.finder.marker_px()
            } else {
                -1
            };
            if offset < 0 || !self.monitors[mi].showbar {
                self.unmap_finder_marker(mi)?;
                continue;
            }
            let Some((x, y, w, _)) = self.finder_place(mi) else {
                self.unmap_finder_marker(mi)?;
                continue;
            };
            let m = &self.monitors[mi];
            let mx = x + (w as i32 - crate::config::FINDER_MARKER_WIDTH) / 2;
            let my = y + offset;
            if m.finder_marker_pos.get() != Some((mx, my)) {
                self.conn.configure_window(
                    m.finder_markerwin,
                    &ConfigureWindowAux::new()
                        .x(mx)
                        .y(my)
                        .width(crate::config::FINDER_MARKER_WIDTH as u32)
                        .height(38),
                )?;
                m.finder_marker_pos.set(Some((mx, my)));
            }
            self.set_mapped(m.finder_markerwin, true)?;
            if !m.finder_marker_stacked.get() {
                self.conn.configure_window(
                    m.finder_markerwin,
                    &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
                )?;
                m.finder_marker_stacked.set(true);
            }
        }
        Ok(())
    }

    /// Remembers which window had X input focus before Finder took over. Any
    /// real window is worth restoring, including one that survived a WM restart
    /// and is not in `clients` yet; root, PointerRoot, None and Finder's own
    /// popup/marker keep the existing root fallback.
    fn remember_finder_focus(&mut self) -> Result {
        if self.finder_saved_focus.is_some() {
            return Ok(());
        }
        let focused = self.conn.get_input_focus()?.reply()?.focus;
        let finder_window = self
            .monitors
            .iter()
            .any(|m| m.barcenterwin == focused || m.finder_markerwin == focused);
        let real_window = focused != u32::from(InputFocus::NONE)
            && focused != u32::from(InputFocus::POINTER_ROOT)
            && focused != self.root
            && !finder_window;
        self.finder_saved_focus = real_window.then_some(focused);
        Ok(())
    }

    /// Gives X input focus back to the window that had it before Finder. If it
    /// was destroyed while Finder was open, fall back to root like the old close
    /// path did.
    fn restore_finder_focus(&mut self) -> Result {
        let saved = self.finder_saved_focus.take();
        let alive = match saved {
            Some(win) => match self.conn.get_window_attributes(win) {
                Ok(cookie) => cookie.reply().is_ok(),
                Err(_) => false,
            },
            None => false,
        };
        let win = if alive { saved.unwrap() } else { self.root };
        self.set_focus_window(win, InputFocus::PARENT)?;
        self.conn.flush()?;
        Ok(())
    }

    fn finder_open(&mut self) -> Result {
        // dwm's drawfinder_frame() simply returns without the 32-bit visual;
        // keep the ordinary clock and skip the modal path in that case. An
        // already-active Finder with no grabs is the asynchronous OCR result
        // path: install the grabs without resetting the recognized query.
        if (self.finder.is_active() && self.finder_grabbed)
            || self.finder_argb_visual == 0
            || self.finder_argb_visual_ptr.is_null()
        {
            return Ok(());
        }
        self.selmon = self.finder_pointer_monitor()?;
        let mon = &self.monitors[self.selmon];
        let fullscreen = mon.sel.is_some_and(|w| {
            self.clients
                .iter()
                .find(|c| c.win == w)
                .is_some_and(|c| c.geom.w >= mon.rect.w && c.geom.h >= mon.rect.h)
        });
        if fullscreen {
            return Ok(());
        }
        self.remember_finder_focus()?;
        self.finder.open();
        self.set_bar_class(self.selmon)?;
        self.stack_finder(self.selmon, true)?;
        let win = self.monitors[self.selmon].barcenterwin;
        let _ = self
            .conn
            .grab_keyboard(true, win, CURRENT_TIME, GrabMode::ASYNC, GrabMode::ASYNC)?
            .reply();
        let status = self
            .conn
            .grab_pointer(
                true,
                self.root,
                EventMask::BUTTON_PRESS | EventMask::POINTER_MOTION,
                GrabMode::ASYNC,
                GrabMode::ASYNC,
                NONE,
                NONE,
                CURRENT_TIME,
            )?
            .reply()?
            .status;
        if status != GrabStatus::SUCCESS {
            let _ = self.conn.ungrab_keyboard(CURRENT_TIME);
            return self.finder_close();
        }
        self.finder_grabbed = true;
        self.set_focus_window(win, InputFocus::PARENT)?;
        self.conn.flush()?;
        self.bar_dirty = true;
        Ok(())
    }

    /// Tears down the modal state. Unlike `Finder::close()`, this is also safe
    /// to call after `Finder` closed itself on Escape, Return or an outside
    /// click, which is why there is no `is_active()` early return here.
    fn finder_close(&mut self) -> Result {
        self.finder.close();
        // Resizing the center window back from Finder to a clock/noti-
        // fication generates an EnterNotify at the old pointer position.
        // dwm suppresses that synthetic crossing for one grace period.
        let (rx, ry) = self.pointer_root().unwrap_or((0, 0));
        self.notification.arm_hover_grace(rx, ry);
        if self.finder_grabbed {
            self.finder_grabbed = false;
            let _ = self.conn.ungrab_keyboard(CURRENT_TIME);
            let _ = self.conn.ungrab_pointer(CURRENT_TIME);
        }
        self.restore_finder_focus()?;
        for mi in 0..self.monitors.len() {
            self.set_bar_class(mi)?;
            self.stack_finder(mi, false)?;
            let win = self.monitors[mi].barcenterwin;
            self.geom_cache.borrow_mut().remove(&win);
            self.clock_drawn.borrow_mut().remove(&win);
            self.force_windows.borrow_mut().insert(win);
            self.unmap_finder_marker(mi)?;
        }
        self.bar_dirty = true;
        Ok(())
    }

    fn finder_toggle(&mut self) -> Result {
        if self.finder.is_active() {
            self.finder_close()
        } else {
            self.finder_open()
        }
    }

    fn finder_draw(&mut self) -> Result {
        if !self.finder.is_active() {
            for mi in 0..self.monitors.len() {
                self.unmap_finder_marker(mi)?;
            }
            return Ok(());
        }
        if self.finder_argb_visual == 0 || self.finder_argb_visual_ptr.is_null() {
            return self.finder_close();
        }
        let mi = self.selmon;
        let Some((x, y, _w, _h)) = self.finder_place(mi) else {
            return Ok(());
        };
        let win = self.monitors[mi].barcenterwin;
        let screen = self.drw.screen();
        let visual = self.finder_argb_visual_ptr;
        let bh = self.bar_h();
        let clock = self.clock.clone();
        let (fw, fh) = self.finder.popup_size(bh as u32);
        // MPRIS scrolling can repaint the bars dozens of times a second without
        // changing the popup. Skipping here keeps those refreshes from touching
        // the cached GL frame or even copying its XRender pixmap.
        if !self.finder.needs_draw(fw, fh, x, y, bh, &clock) {
            return Ok(());
        }
        if self
            .finder
            .draw(&mut self.drw, screen, visual, win as u64, x, y, bh, &clock)
            .is_err()
        {
            // A failed GL/presentation init must not kill the WM loop. Drop the
            // modal state and let the next refresh draw the normal clock.
            return self.finder_close();
        }
        self.geom_cache.borrow_mut().remove(&win);
        self.conn.flush()?;
        self.finder_marker()?;
        Ok(())
    }

    /// Draws the notification popup or hover history into the center ARGB
    /// window. The frame cache is shared with Finder's presentation path, so a
    /// repaint of the clock or status bar does not swap pixels needlessly.
    fn notification_draw(&mut self) -> Result {
        let force = self.notification_force.take();
        if !self.notification.is_center_active() || self.finder.is_active() {
            return Ok(());
        }
        if force {
            self.notification.invalidate_frame();
        }
        if self.finder_argb_visual == 0 || self.finder_argb_visual_ptr.is_null() {
            return Ok(());
        }
        let mi = self.selmon;
        if self.monitor_fullscreen(mi) {
            return Ok(());
        }
        let Some((x, _width)) = self.clock_place(mi) else {
            return Ok(());
        };
        let win = self.monitors[mi].barcenterwin;
        let y = self.monitors[mi].by;
        let bh = self.bar_h();
        let (w, h) = self.notification.popup_size(bh);
        if !self.notification.needs_draw(w, h, x, y, bh) {
            return Ok(());
        }
        let screen = self.drw.screen();
        let visual = self.finder_argb_visual_ptr;
        if self
            .notification
            .draw(&mut self.drw, screen, visual, win as u64, x, y, bh)
            .is_err()
        {
            // A failed GL init must not kill the WM loop. Archive the queue and
            // let the next refresh restore the normal clock.
            self.notification.clear_for_fullscreen(bh);
            self.bar_dirty = true;
            return Ok(());
        }
        self.geom_cache.borrow_mut().remove(&win);
        self.conn.flush()?;
        Ok(())
    }

    /// Configures and draws one clock window synchronously, like C dwm's
    /// `drawclockbar()` followed by `drw_map()`. A window whose position, size,
    /// text and focus did not change is not touched at all, so PipeWire noise
    /// cannot keep the compositor busy.
    fn draw_clock(&mut self, mi: usize) -> Result {
        let m = &self.monitors[mi];
        let Some((x, w)) = self.clock_place(mi) else {
            return Ok(());
        };
        let (win, y) = (m.barcenterwin, m.by);
        let focused = mi == self.selmon;
        let text = self.clock.clone();
        let forced = self.force_windows.borrow().contains(&win);
        let key = (x, y, w, text.clone(), focused);
        if !forced && self.clock_drawn.borrow().get(&win) == Some(&key) {
            return Ok(());
        }
        let bh = self.bar_h();
        let (dw, dh) = (w.max(1) as u32, bh.max(1) as u32);
        self.place_cached(win, x, y, w, bh)?;
        self.conn.flush()?;
        self.drw.resize(dw, dh);
        self.drw.clock(&self.metrics, dw as i32, &text, focused);
        if self.finder_argb_visual != 0 && !self.finder_argb_visual_ptr.is_null() {
            // XCopyArea would raise BadMatch against the 32-bit ARGB window.
            self.drw.map_argb(
                win as x11::xlib::Window,
                self.finder_argb_visual_ptr,
                dw,
                dh,
            );
        } else {
            self.drw.map(win as x11::xlib::Window, dw, dh);
        }
        self.clock_drawn.borrow_mut().insert(win, key);
        Ok(())
    }

    /// dwm's `drawbar()` for each shown monitor. Every section is drawn into
    /// the one Xlib `drw` drawable, copied into its window and flushed before
    /// the next section, exactly like the C version.
    pub fn draw_bars(&mut self) -> Result {
        // The geometry changes were queued on the x11rb connection; send them
        // before the Xlib pixels land so a resized window gets the new frame.
        self.conn.flush()?;
        self.mpris_marker_rect = None;
        let bh = self.bar_h().max(1);
        for mi in 0..self.monitors.len() {
            if !self.monitors[mi].showbar {
                continue;
            }
            let m = &self.monitors[mi];
            let occupied = self
                .clients
                .iter()
                .filter(|c| c.mon == mi)
                .fold(0, |acc, c| acc | c.tags);
            let title = m.sel.map(|w| self.client_name(w));
            let icon = m.sel.and_then(|w| self.client_icon(w));
            let icon_id = icon.as_ref().map_or(0, |i| i.id);
            let focused = mi == self.selmon;
            let b = self.barwidths(mi);
            let (barwin, titlewin, kbwin, rightwin, marker_win) = (
                m.barwin,
                m.bartitlewin,
                m.barkbwin,
                m.barrightwin,
                m.mpris_markerwin,
            );
            let selected = self.tags_of(mi);
            let kbstr = self.kbstr.clone();
            let status = self.bar_status.clone();
            let player = self.mpris.clone();
            let (scroll, progress, marker_hovered) = (
                self.mpris_scroll_px,
                self.mpris.current_progress(),
                self.mpris_marker_hovered,
            );

            let tw = b.tw.max(1) as u32;
            let tag_key = format!("tags:{tw}:{occupied}:{selected}");
            if self.section_changed(barwin, &tag_key) {
                self.drw.resize(tw, bh as u32);
                self.drw.tags(&self.metrics, tw as i32, occupied, selected);
                self.drw.map(barwin as x11::xlib::Window, tw, bh as u32);
                self.bar_drawn.borrow_mut().insert(barwin, tag_key);
            }

            let tlw = b.tlw.max(1) as u32;
            let title_key = format!("title:{tlw}:{title:?}:{focused}:{icon_id}");
            if self.section_changed(titlewin, &title_key) {
                self.drw.resize(tlw, bh as u32);
                self.drw.title(
                    &self.metrics,
                    tlw as i32,
                    title.as_deref(),
                    focused,
                    icon.as_ref(),
                );
                self.drw.map(titlewin as x11::xlib::Window, tlw, bh as u32);
                self.bar_drawn.borrow_mut().insert(titlewin, title_key);
            }

            let kw = b.kw.max(1) as u32;
            let kb_key = format!("kb:{kw}:{kbstr}:{focused}");
            if self.section_changed(kbwin, &kb_key) {
                self.drw.resize(kw, bh as u32);
                self.drw.kb(&self.metrics, kw as i32, &kbstr, focused);
                self.drw.map(kbwin as x11::xlib::Window, kw, bh as u32);
                self.bar_drawn.borrow_mut().insert(kbwin, kb_key);
            }

            if mi == self.selmon && self.mpris_hovered && self.mpris.present {
                // The expanded panel covers the row below the bar. Re-assert
                // it above every window on each frame so a client raised by a
                // focus change or a layout pass cannot bury it again.
                self.stack_mpris_bar(mi, true)?;
                self.mpris_bar_raised.borrow_mut()[mi] = true;
                let rw = b.rw.max(1) as u32;
                let ph = (bh * 2) as u32;
                let (marker_x, marker_y, marker_w, marker_h) =
                    crate::bar::mpris_knob(rw as i32, bh, player.volume, marker_hovered);
                let x = self.rightbar_x(mi) + marker_x;
                let y = m.by + marker_y;
                self.place_cached(marker_win, x, y, marker_w, marker_h)?;
                self.set_mapped(marker_win, true)?;
                self.mpris_marker_rect = Some((x, y, marker_w, marker_h));
                self.drw.resize(rw, ph);
                self.drw.mpris_panel(
                    &self.metrics,
                    rw as i32,
                    &status,
                    &player,
                    scroll,
                    marker_hovered,
                );
                self.drw.map(rightwin as x11::xlib::Window, rw, ph);
                // The panel has state the collapsed cache cannot describe.
                self.bar_drawn.borrow_mut().remove(&rightwin);
            } else {
                // Restore the normal stacking when the panel collapses.
                let was_raised = self.mpris_bar_raised.borrow()[mi];
                if was_raised {
                    self.stack_mpris_bar(mi, false)?;
                    self.mpris_bar_raised.borrow_mut()[mi] = false;
                }
                self.set_mapped(marker_win, false)?;
                let rw = b.rw.max(1) as u32;
                let progress_key = progress.map(|p| (p * 10_000.0) as u32);
                let right_key = format!(
                    "status:{rw}:{bh}:{}:{scroll}:{progress_key:?}",
                    status.key()
                );
                if self.section_changed(rightwin, &right_key) {
                    self.drw.resize(rw, bh as u32);
                    if let Some(custom) = &status.custom {
                        self.drw
                            .status(&self.metrics, rw as i32, custom, scroll, progress);
                    } else {
                        self.drw
                            .status_runs(&self.metrics, rw as i32, &status, scroll, progress);
                    }
                    self.drw.map(rightwin as x11::xlib::Window, rw, bh as u32);
                    self.bar_drawn.borrow_mut().insert(rightwin, right_key);
                }
            }
            if !(mi == self.selmon
                && (self.finder.is_active() || self.notification.is_center_active()))
            {
                self.draw_clock(mi)?;
            }
        }
        self.conn.flush()?;
        self.force_windows.borrow_mut().clear();
        Ok(())
    }

    /// One pass of the bar's per-tick work: applies state changes, then
    /// redraws the bars only when their contents or layout changed. Window
    /// motion and client configure events do not get here.
    pub fn refresh(&mut self) -> Result {
        // A transition forces bar_dirty above, so the frame that enters or
        // leaves fullscreen still runs the full path. Steady-state timed ticks
        // while fullscreen take the cheap path below.
        self.sync_bar_suspended();
        let mut bars = std::mem::take(&mut self.bar_dirty);
        if self.bar_suspended && !bars && !self.finder.is_active() {
            // Keep draining notification events with fullscreen=true so they
            // are filed in history instead of popping up when fullscreen ends.
            // Everything else (PipeWire sampling, status, scrolling titles and
            // bar/X work) is suspended while the pointer's bar is unmapped.
            let _ = self.notification.poll(true, self.bar_h(), Instant::now())?;
            return Ok(());
        }
        let finder_dirty = self.finder.tick()?;
        // OCR finishes on a worker thread while Finder is closed. When its
        // result opens the popup, install the modal grabs here just like a
        // Super+A press would.
        if self.finder.is_active() && !self.finder_grabbed {
            self.finder_open()?;
        }
        let finder_active = self.finder.is_active();
        self.notification.set_finder_active(finder_active);
        bars |= finder_dirty;
        let notification_was_active = self.notification_center_active_last;
        let notification_had_focus = self.notification.has_input_focus();
        let fullscreen = self.monitor_fullscreen(self.selmon);
        if fullscreen != self.notification_fullscreen {
            if fullscreen {
                self.notification.clear_for_fullscreen(self.bar_h());
                bars = true;
            }
            self.notification_fullscreen = fullscreen;
        }
        if self
            .notification
            .poll(fullscreen, self.bar_h(), Instant::now())?
        {
            bars = true;
        }
        self.sync_center_class()?;
        let notification_active = self.notification.is_center_active();
        let notification_has_focus = self.notification.has_input_focus();
        if !finder_active && notification_had_focus != notification_has_focus {
            if notification_has_focus {
                let win = self.monitors[self.selmon].barcenterwin;
                self.set_focus_window(win, InputFocus::PARENT)?;
            } else {
                // Hand the keyboard back to the selected client instead of
                // leaving focus on root while the border still names a client.
                self.focus()?;
            }
        }
        if notification_was_active && !notification_active && !finder_active {
            // A pointer event may have closed history before refresh ran, so
            // the cached clock frame is stale even though the manager now says
            // it is inactive. Force a real repaint, not just a geometry update.
            bars = true;
            for mi in 0..self.monitors.len() {
                self.stack_finder(mi, false)?;
                let win = self.monitors[mi].barcenterwin;
                self.geom_cache.borrow_mut().remove(&win);
                self.clock_drawn.borrow_mut().remove(&win);
                self.force_windows.borrow_mut().insert(win);
            }
            self.conn.flush()?;
        }
        if self.update_mpris() {
            bars = true;
        }
        if self.update_clock() {
            // The clock text can change the width budget, which moves and
            // resizes the other bar sections too.
            bars = true;
        }
        // dwm freezes the animated clock width while Finder or a notification
        // owns the center window, so its resize deadline never competes with
        // the popup frames. Still sample the level so it resumes in sync.
        let clock_level_changed = self.update_clock_anim();
        let clock_anim = !finder_active && !notification_active && clock_level_changed;
        if self.update_status() {
            bars = true;
        }
        if self.update_mpris_scroll() {
            bars = true;
        }
        // Position changes are interpolated from the last D-Bus reading. Only
        // repaint when the progress bar would visibly move.
        let progress = self.mpris.current_progress();
        let progress_changed = match (progress, self.last_progress) {
            (Some(now), Some(before)) => (now - before).abs() >= PROGRESS_EPSILON,
            (None, None) => false,
            _ => true,
        };
        if progress_changed {
            self.last_progress = progress;
            bars = true;
        }
        if bars {
            self.update_bars_geometry()?;
            self.draw_bars()?;
            if finder_active {
                self.finder_draw()?;
                // Mapping the neighboring bar sections can put the center
                // window back below them. dwm's final raise in resizebarwin()
                // keeps the popup and its marker above every bar section.
                if self.finder.is_active() {
                    self.stack_finder(self.selmon, true)?;
                    self.conn.flush()?;
                }
            } else if notification_active {
                self.notification_draw()?;
                if self.notification.is_center_active() {
                    self.stack_finder(self.selmon, true)?;
                    self.conn.flush()?;
                }
            }
        } else if clock_anim {
            // Only the center window's width changed: redraw just the clocks.
            for mi in 0..self.monitors.len() {
                if self.monitors[mi].showbar
                    && !(mi == self.selmon
                        && (self.finder.is_active() || self.notification.is_center_active()))
                {
                    self.draw_clock(mi)?;
                }
            }
            self.conn.flush()?;
        }
        self.notification_center_active_last = self.notification.is_center_active();
        Ok(())
    }

    fn rightbar_x(&self, mi: usize) -> i32 {
        let b = self.barwidths(mi);
        let gap = if self.tray_width(mi) > 0 { BARGAP } else { 0 };
        self.tray_x(mi) - gap - b.rw
    }

    fn update_mpris_marker_class(&self, mi: usize) -> Result {
        let class = if self.mpris_marker_hovered {
            b"dwm-mpris-volume-marker-larg\0".as_slice()
        } else {
            b"dwm-mpris-volume-marker\0".as_slice()
        };
        let mut wm_class = b"dwm-mpris-volume-marker\0".to_vec();
        wm_class.extend_from_slice(class);
        self.conn
            .change_property8(
                PropMode::REPLACE,
                self.monitors[mi].mpris_markerwin,
                AtomEnum::WM_CLASS,
                AtomEnum::STRING,
                &wm_class,
            )?
            .check()?;
        Ok(())
    }

    fn pointer_over_mpris_bar(&self, mi: usize, x: i32, y: i32) -> bool {
        let m = &self.monitors[mi];
        let h = self.bar_h()
            * if self.mpris_hovered && self.mpris.present && mi == self.selmon {
                2
            } else {
                1
            };
        x >= self.rightbar_x(mi)
            && x < self.rightbar_x(mi) + self.barwidths(mi).rw
            && y >= m.by
            && y < m.by + h
    }

    fn set_mpris_volume_from_x(&mut self, mi: usize, x: i32) {
        let slider_x = 46;
        let slider_w = (self.barwidths(mi).rw - slider_x - 120).max(1);
        let position = (x - slider_x - 12) as f32 / slider_w as f32;
        let volume = crate::mpris::slider_volume(position);
        self.mpris.volume = volume;
        crate::mpris::set_volume(&self.mpris.service, volume);
    }

    fn mpris_panel_button(&mut self, mi: usize, x: i32, y: i32, button: u8) {
        let bh = self.bar_h();
        if !self.mpris.present || !self.mpris_hovered || y < bh || y >= bh * 2 {
            return;
        }
        if button == 4 || button == 5 {
            let delta = if button == 4 { 0.05 } else { -0.05 };
            self.mpris.volume = (self.mpris.volume + delta).clamp(0.0, 1.0);
            crate::mpris::set_volume(&self.mpris.service, self.mpris.volume);
            return;
        }
        if button != 1 {
            return;
        }

        let control_w = 34;
        let slider_x = control_w + 12;
        let slider_w = (self.barwidths(mi).rw - slider_x - 120).max(1);
        let volume_x = slider_x + slider_w + 6;
        let previous_x = volume_x + 46;
        let next_x = previous_x + control_w;
        let marker_half = if self.mpris_marker_hovered { 16 } else { 12 };
        if x < control_w {
            crate::mpris::play_pause(&self.mpris.service);
        } else if x >= slider_x - marker_half && x <= slider_x + slider_w + marker_half {
            self.mpris_volume_drag = true;
            self.set_mpris_volume_from_x(mi, x);
        } else if x >= previous_x && x < next_x {
            crate::mpris::previous(&self.mpris.service);
        } else if x >= next_x && x < next_x + control_w {
            crate::mpris::next(&self.mpris.service);
        }
    }

    /// A left click on a workspace cell switches to that workspace on the
    /// monitor whose strip was clicked. Cell geometry matches `Drw::tags`:
    /// the row starts at `BORDERPX` and each tag is `textw(TAG_LABEL)` wide.
    fn tags_button(&mut self, e: &ButtonPressEvent) -> Result<bool> {
        if e.detail != 1 {
            return Ok(false);
        }
        if !self.monitors.iter().any(|m| m.barwin == e.event) {
            return Ok(false);
        }
        let x = e.event_x as i32 - BORDERPX;
        let cell = self.metrics.textw(TAG_LABEL);
        if x < 0 || cell <= 0 {
            return Ok(false);
        }
        let idx = (x / cell) as usize;
        if idx >= TAGS {
            return Ok(false);
        }
        // A click also selects the monitor under the pointer, so a strip on a
        // non-focused monitor switches that monitor's workspace.
        self.activate_monitor_at(e.root_x as i32, e.root_y as i32)?;
        self.view(1u32 << idx)?;
        self.bar_dirty = true;
        Ok(true)
    }

    /// dwm's `notification_clock_hit`: only the fixed clock-sized part of the
    /// animated center window opens history while the clock is shown.
    fn notification_clock_hit(&self, mi: usize, x: i32) -> bool {
        if self.notification.is_center_active() {
            return true;
        }
        let cw = self.barwidths(mi).cw;
        let dcw = self.clock_window_width(mi, cw);
        self.notification.clock_hit(x, cw, dcw)
    }

    /// Applies the small state changes caused by pointer events. The next
    /// refresh does the geometry and pixel work, like dwm's drawbars/resize.
    fn notification_pointer_state(&mut self, dirty: bool) -> Result {
        if dirty {
            self.bar_dirty = true;
            self.sync_center_class()?;
        }
        Ok(())
    }

    fn notification_enter(&mut self, e: &EnterNotifyEvent) -> Result<bool> {
        let Some(mi) = self.monitors.iter().position(|m| m.barcenterwin == e.event) else {
            return Ok(false);
        };
        if mi != self.selmon {
            return Ok(false);
        }
        if self.finder.is_active() || self.monitor_fullscreen(mi) {
            return Ok(true);
        }
        if !self.notification_clock_hit(mi, e.event_x as i32) {
            return Ok(true);
        }
        let dirty = self.notification.enter(
            e.event_x as i32,
            e.event_y as i32,
            e.root_x as i32,
            e.root_y as i32,
            self.bar_h(),
        );
        self.notification_pointer_state(dirty)?;
        Ok(true)
    }

    fn notification_leave(&mut self, e: &LeaveNotifyEvent) -> Result<bool> {
        let Some(mi) = self.monitors.iter().position(|m| m.barcenterwin == e.event) else {
            return Ok(false);
        };
        if mi != self.selmon {
            return Ok(false);
        }
        if self.finder.is_active() {
            return Ok(true);
        }
        let dirty = self.notification.leave(self.bar_h());
        self.notification_pointer_state(dirty)?;
        Ok(true)
    }

    fn notification_motion(&mut self, e: &MotionNotifyEvent) -> Result<bool> {
        let Some(mi) = self.monitors.iter().position(|m| m.barcenterwin == e.event) else {
            return Ok(false);
        };
        if mi != self.selmon {
            return Ok(false);
        }
        if self.finder.is_active() || self.monitor_fullscreen(mi) {
            return Ok(true);
        }
        if !self.notification_clock_hit(mi, e.event_x as i32) {
            return Ok(true);
        }
        let dirty = self.notification.motion(
            e.event_x as i32,
            e.event_y as i32,
            e.root_x as i32,
            e.root_y as i32,
            self.bar_h(),
        );
        self.notification_pointer_state(dirty)?;
        Ok(true)
    }

    fn notification_button(&mut self, e: &ButtonPressEvent) -> Result<bool> {
        let Some(mi) = self.monitors.iter().position(|m| m.barcenterwin == e.event) else {
            return Ok(false);
        };
        if mi != self.selmon {
            return Ok(false);
        }
        if self.finder.is_active() || self.monitor_fullscreen(mi) {
            return Ok(true);
        }
        // Without an active popup, clicks on the clock remain ordinary root
        // bindings, exactly as in dwm's buttonpress().
        if !self.notification.is_center_active() {
            return Ok(false);
        }
        let had_focus = self.notification.has_input_focus();
        self.notification
            .button(e.detail, e.event_x as i32, e.event_y as i32, self.bar_h());
        let has_focus = self.notification.has_input_focus();
        if had_focus != has_focus {
            if has_focus {
                self.set_focus_window(self.monitors[mi].barcenterwin, InputFocus::PARENT)?;
            } else {
                self.focus()?;
            }
        }
        self.bar_dirty = true;
        self.sync_center_class()?;
        Ok(true)
    }

    /// Returns true when a notification input row or the open history consumed
    /// this key. Ordinary WM bindings must not run in that case.
    fn notification_keypress(&mut self, e: &KeyPressEvent) -> Result<bool> {
        let sym = self.event_keysym(e);
        let state = u16::from(e.state) & CLEAN_MASK;
        let had_focus = self.notification.has_input_focus();
        let consumed = if had_focus {
            let text = Finder::key_char(sym, state)
                .map(String::from)
                .unwrap_or_default();
            self.notification.keypress(sym, &text, self.bar_h())
        } else if self.notification.is_history_active() && sym == XK_Escape {
            self.notification.escape(self.bar_h())
        } else {
            false
        };
        if !consumed {
            return Ok(false);
        }
        let has_focus = self.notification.has_input_focus();
        if had_focus != has_focus {
            if has_focus {
                self.set_focus_window(self.monitors[self.selmon].barcenterwin, InputFocus::PARENT)?;
            } else {
                self.focus()?;
            }
        }
        self.bar_dirty = true;
        self.sync_center_class()?;
        Ok(true)
    }

    pub fn handle(&mut self, event: Event) -> Result {
        // While the finder is modal it owns keyboard and button input before
        // any of the ordinary WM bindings, as in dwm's buttonpress/keypress.
        if self.finder.is_active() {
            match &event {
                Event::KeyPress(e) => {
                    let sym = self.event_keysym(&e);
                    self.finder.keypress(sym, u16::from(e.state) & CLEAN_MASK);
                    if !self.finder.is_active() {
                        // Escape and Return close Finder inside Finder itself.
                        self.finder_close()?;
                    } else {
                        self.bar_dirty = true;
                    }
                    return Ok(());
                }
                Event::ButtonPress(e) => {
                    let (rx, ry) = (e.root_x as i32, e.root_y as i32);
                    if !self.finder_pointer_inside(rx, ry) {
                        self.finder_close()?;
                        self.finder_focus_pointer(rx, ry)?;
                        return Ok(());
                    }
                    if let Some((_, popup_y, _, _)) = self.finder_place(self.selmon) {
                        self.finder
                            .buttonpress(e.detail, ry - popup_y, self.bar_h());
                    }
                    if !self.finder.is_active() {
                        // A click on a result launches and closes Finder there.
                        self.finder_close()?;
                    } else {
                        self.bar_dirty = true;
                    }
                    return Ok(());
                }
                Event::ButtonRelease(_) => return Ok(()),
                Event::MotionNotify(e) => {
                    let (rx, ry) = (e.root_x as i32, e.root_y as i32);
                    if self.finder_pointer_inside(rx, ry)
                        && let Some((_, popup_y, _, _)) = self.finder_place(self.selmon)
                    {
                        self.finder.motion(ry, popup_y, self.bar_h());
                    }
                    return Ok(());
                }
                _ => {}
            }
        }
        match event {
            // XI2 sees clicks on embedded icon windows without competing with
            // the app for the core ButtonPress selection.
            Event::XinputButtonPress(e) => {
                const FP1616_ONE: i32 = 1 << 16;
                let (x, y) = (e.root_x / FP1616_ONE, e.root_y / FP1616_ONE);
                if self.pointer_in_tray(x, y) {
                    let icon = self.tray.icon_at(
                        x - self.tray_x(self.selmon),
                        self.tray_icon_size(),
                        SYSTRAY_SPACING,
                    );
                    self.record_tray_click(icon.unwrap_or(0));
                }
                return Ok(());
            }
            // Override-redirect menus map without a MapRequest. This is the
            // only place to catch them before the next raise_bars() buries them.
            Event::MapNotify(e) if self.is_tray_menu(e.window) => {
                self.track_tray_menu(e.window)?;
                return Ok(());
            }
            // Ordinary applications map their right-click menus and tooltips
            // without a MapRequest. Track them too, so the next arrange() does
            // not leave them under a newly spawned tiled window.
            Event::MapNotify(e) if self.is_unmanaged_overlay(e.window) => {
                self.track_overlay(e.window)?;
                return Ok(());
            }
            Event::MapRequest(e) => {
                if self.is_tray_icon(e.window) {
                    self.tray.set_visible(e.window, true);
                    self.relayout_tray()?;
                    return Ok(());
                }
                let tray_menu = self.is_tray_menu(e.window);
                if tray_menu && !self.is_managed(e.window) {
                    let unmanaged = self
                        .conn
                        .get_window_attributes(e.window)
                        .ok()
                        .and_then(|c| c.reply().ok())
                        .is_some_and(|a| {
                            a.override_redirect || a.class == WindowClass::INPUT_ONLY
                        });
                    if unmanaged || is_popup_win_type(self.read_win_type(e.window)) {
                        let _ = self.conn.map_window(e.window);
                        self.track_tray_menu(e.window)?;
                        return Ok(());
                    }
                    // A regular window the app opened from its tray icon is
                    // still managed like any other client. Remember it before
                    // arrange() raises the bar layer so it ends up on top.
                    self.track_tray_menu(e.window)?;
                }
                if !self.is_managed(e.window) {
                    // Do not manage override-redirect or InputOnly windows.
                    let attrs = self
                        .conn
                        .get_window_attributes(e.window)
                        .ok()
                        .and_then(|c| c.reply().ok());
                    if let Some(attrs) = attrs {
                        if attrs.override_redirect || attrs.class == WindowClass::INPUT_ONLY {
                            let _ = self.conn.map_window(e.window);
                            let _ = self.track_overlay(e.window);
                            // Mapping a root child puts it at the top of the
                            // stack, so restore the bar layer immediately.
                            let _ = self.raise_bars();
                            let _ = self.conn.flush();
                        } else if self.should_ignore_window(e.window) {
                            let _ = self.conn.map_window(e.window);
                            let _ = self.track_overlay(e.window);
                            // Mapping a root child puts it at the top of the
                            // stack, so restore the bar layer immediately.
                            let _ = self.raise_bars();
                            let _ = self.conn.flush();
                        } else {
                            self.manage(e.window)?;
                        }
                    }
                } else {
                    // A managed client mapping itself must not escape its
                    // workspace: let the layout decide whether it is visible.
                    // A blind map here would leave a hidden window on screen
                    // until the next arrange() unmaps it again. Clear the
                    // iconified flag first, though: a client restoring from the
                    // tray withdrew itself, so without this arrange() would
                    // unmap it again on the same pass.
                    self.set_hidden(e.window, false)?;
                    // apply_layout() sets the real map state when it maps the
                    // window; if the client belongs to another tag it stays
                    // unmapped and must not be counted as mapped here.
                    self.arrange()?;
                }
                self.bar_dirty = true;
            }
            // Tray icons hide by unmapping, so the row must shrink to close the
            // gap. Managed clients we unmapped ourselves (tag switch, iconify,
            // fullscreen) are marked by wm_unmap(); anything else is the client
            // withdrawing its own window, e.g. "close to tray" in Electron apps.
            // DestroyNotify is still what removes a client that went away.
            Event::UnmapNotify(e) => {
                // A popup that closes must leave the tracked layer; MapNotify
                // will add it again the next time the client opens it.
                self.popup_windows.borrow_mut().retain(|&w| w != e.window);
                self.overlay_windows.borrow_mut().retain(|&w| w != e.window);
                // Reparenting a mapped icon (scan_existing adopting an icon left
                // mapped by Discord or a previous WM) makes X do an internal
                // UnmapWindow before the reparent. That UnmapNotify is reported
                // via SubstructureNotify on the old parent, root, which we
                // select. It is our own reparent, not the app hiding the icon,
                // so ignore it or the freshly docked icon is immediately hidden.
                if self.is_tray_icon(e.window)
                    && e.event != self.root
                    && self.tray.set_visible(e.window, false)
                {
                    self.relayout_tray()?;
                }
                if !self.consume_client_unmap(e.window) {
                    return Ok(());
                }
                if self.is_managed(e.window)
                    && !self.clients.iter().any(|c| c.win == e.window && c.hidden)
                {
                    // Without this the client stays "visible" in the tree: its
                    // tile is never released, and switching workspaces makes
                    // apply_layout() map the window again even though the
                    // client has stopped painting it, leaving an empty frame.
                    self.set_hidden(e.window, true)?;
                    self.arrange()?;
                    self.bar_dirty = true;
                }
            }
            Event::DestroyNotify(e) => {
                self.tray_menus.borrow_mut().retain(|&w| w != e.window);
                self.popup_windows.borrow_mut().retain(|&w| w != e.window);
                self.overlay_windows.borrow_mut().retain(|&w| w != e.window);
                if self.tray.undock(e.window) {
                    self.relayout_tray()?;
                } else {
                    self.unmanage(e.window)?;
                }
                self.bar_dirty = true;
            }
            Event::ConfigureNotify(e) if e.window == self.root => {
                self.updategeom()?;
            }
            Event::ConfigureNotify(e) if e.event == self.root && e.window != self.root => {
                // SubstructureNotify also reports stacking changes of other
                // override-redirect root children (menus, tooltips, OSDs).
                // They can raise themselves without asking the WM, so use the
                // notification to put the bar back on top. Our own windows and
                // clients are stacked by the layout paths above.
                if !self.is_our_window(e.window) {
                    self.raise_bars()?;
                    self.conn.flush()?;
                }
                return Ok(());
            }
            Event::MappingNotify(e) => {
                // A new layout (e.g. setxkbmap) changes both the keymap used for
                // grabs and the layout names shown in the bar.
                if e.request == x11rb::protocol::xproto::Mapping::KEYBOARD
                    || e.request == x11rb::protocol::xproto::Mapping::MODIFIER
                {
                    let _ = self.refresh_keysyms();
                    self.update_kb();
                    self.bar_dirty = true;
                }
            }
            Event::XkbStateNotify(e) => {
                // Switching the XKB group (Win+Space or another app's input
                // switcher) only changes state: no core MappingNotify is sent.
                // Modifier-only state changes arrive here too, so re-read the
                // layout only when a group component actually changed.
                let group_parts = u16::from(xkb::StatePart::GROUP_STATE)
                    | u16::from(xkb::StatePart::GROUP_BASE)
                    | u16::from(xkb::StatePart::GROUP_LATCH)
                    | u16::from(xkb::StatePart::GROUP_LOCK);
                if u16::from(e.changed) & group_parts != 0 {
                    self.update_kb();
                    self.bar_dirty = true;
                }
            }
            Event::XkbMapNotify(_) | Event::XkbNewKeyboardNotify(_) => {
                let _ = self.refresh_keysyms();
                self.update_kb();
                self.bar_dirty = true;
            }
            Event::RandrScreenChangeNotify(_) | Event::RandrNotify(_) => {
                self.updategeom()?;
            }
            Event::ConfigureRequest(e) => {
                if self.is_tray_icon(e.window) {
                    // Icons do not choose their own cell; re-apply our geometry.
                    self.relayout_tray()?;
                    return Ok(());
                }
                if let Some((idx, mi, floating)) = self
                    .clients
                    .iter()
                    .enumerate()
                    .find_map(|(i, c)| (c.win == e.window).then_some((i, c.mon, c.floating)))
                {
                    if floating {
                        // C's configurerequest(): accept geometry changes for a
                        // floating client, then place only that client.
                        let geom = self.clients[idx].geom;
                        let mask = u16::from(e.value_mask);
                        let mut rect = Rect {
                            x: if mask & u16::from(ConfigWindow::X) != 0 {
                                e.x as i32
                            } else {
                                geom.x
                            },
                            y: if mask & u16::from(ConfigWindow::Y) != 0 {
                                e.y as i32
                            } else {
                                geom.y
                            },
                            w: if mask & u16::from(ConfigWindow::WIDTH) != 0 {
                                e.width as u32
                            } else {
                                geom.w
                            },
                            h: if mask & u16::from(ConfigWindow::HEIGHT) != 0 {
                                e.height as u32
                            } else {
                                geom.h
                            },
                        };
                        let m = self.monitors[mi].rect;
                        if rect.x >= m.x + m.w as i32 {
                            rect.x = m.x + m.w as i32 - rect.w as i32;
                        }
                        if rect.y >= m.y + m.h as i32 {
                            rect.y = m.y + m.h as i32 - rect.h as i32;
                        }
                        if rect.x + rect.w as i32 <= m.x {
                            rect.x = m.x;
                        }
                        if rect.y + rect.h as i32 <= m.y {
                            rect.y = m.y;
                        }
                        let pos_mask = u16::from(ConfigWindow::X) | u16::from(ConfigWindow::Y);
                        let asked_position = mask & pos_mask != 0;
                        // Ignore the (0,0) default many toolkits send: they
                        // still expect the WM to center a fresh dialog.
                        let placeholder = asked_position
                            && e.x == 0
                            && e.y == 0
                            && !self.clients[idx].hints.user_position;
                        if asked_position && !placeholder {
                            // The client (or the user via a launcher) picked a
                            // position: stop auto-centering this window.
                            self.clients[idx].auto_place = false;
                        } else if self.clients[idx].auto_place {
                            // Size-only request: keep the dialog centered at
                            // its new size, or over its transient parent.
                            let (x, y) = self.auto_float_origin(
                                &self.clients[idx],
                                rect.w as i32,
                                rect.h as i32,
                            );
                            rect.x = x;
                            rect.y = y;
                        }
                        self.clients[idx].geom = rect;
                        self.place_floating(e.window)?;
                    } else if let Some(rect) = self.geometry(mi, e.window) {
                        // A tiled client cannot resize itself. Tell it the
                        // geometry dwm chose instead of relaying the request.
                        let border = self
                            .clients
                            .iter()
                            .find(|c| c.win == e.window)
                            .map(client_border)
                            .unwrap_or(BORDERPX);
                        let inner_w = (rect.w as i32 - 2 * border).max(1) as u32;
                        let inner_h = (rect.h as i32 - 2 * border).max(1) as u32;
                        self.send_configure(e.window, rect, inner_w, inner_h, border as u32)?;
                        self.conn.flush()?;
                    }
                } else {
                    let mask = u16::from(e.value_mask);
                    let mut aux = ConfigureWindowAux::new();
                    if mask & u16::from(ConfigWindow::X) != 0 {
                        aux = aux.x(e.x as i32);
                    }
                    if mask & u16::from(ConfigWindow::Y) != 0 {
                        aux = aux.y(e.y as i32);
                    }
                    if mask & u16::from(ConfigWindow::WIDTH) != 0 {
                        aux = aux.width(e.width as u32);
                    }
                    if mask & u16::from(ConfigWindow::HEIGHT) != 0 {
                        aux = aux.height(e.height as u32);
                    }
                    if mask & u16::from(ConfigWindow::BORDER_WIDTH) != 0 {
                        aux = aux.border_width(e.border_width as u32);
                    }
                    if mask & u16::from(ConfigWindow::SIBLING) != 0 {
                        aux = aux.sibling(e.sibling);
                    }
                    let restacked = mask & u16::from(ConfigWindow::STACK_MODE) != 0;
                    if restacked {
                        aux = aux.stack_mode(e.stack_mode);
                    }
                    self.conn.configure_window(e.window, &aux)?;
                    if restacked {
                        // An unredirected window may have asked to be raised
                        // above everything, including the bar.
                        self.raise_bars()?;
                    }
                    self.conn.flush()?;
                }
            }
            Event::FocusIn(e) => {
                self.focus_in(&e)?;
            }
            Event::EnterNotify(e) => {
                // The Finder popup and its marker are separate override-redirect
                // windows. Crossing between them must not dirty the bars: that
                // made the final `stack_finder()` restack them on every crossing,
                // so the hover produced an endless enter/leave/flicker loop.
                let finder_crossing = self.finder.is_active()
                    && self
                        .monitors
                        .iter()
                        .any(|m| m.barcenterwin == e.event || m.finder_markerwin == e.event);
                if finder_crossing {
                    return Ok(());
                }
                // A pointer grab keeps focus on the client being moved or
                // resized even when the pointer crosses a window stacked over
                // it. The same hold protects an explicit Alt+Tab focus from the
                // synthetic crossing generated by its pointer warp.
                if self.pointer_grabbed || Instant::now() < self.focus_hold_until {
                    return Ok(());
                }
                if self.notification_enter(&e)? {
                    return Ok(());
                }
                // Moving the pointer to another monitor selects it and unfocuses
                // the previously focused monitor's window.
                if !self.finder.is_active() {
                    self.activate_monitor_at(e.root_x as i32, e.root_y as i32)?;
                }
                if let Some(mi) = self
                    .monitors
                    .iter()
                    .position(|m| m.barrightwin == e.event || m.mpris_markerwin == e.event)
                {
                    if mi == self.selmon && self.mpris.present {
                        if self.monitors[mi].mpris_markerwin == e.event {
                            if !self.mpris_marker_hovered {
                                self.mpris_marker_hovered = true;
                                self.bar_dirty = true;
                                self.update_mpris_marker_class(mi)?;
                            }
                        } else if !self.mpris_hovered {
                            self.mpris_hovered = true;
                            self.bar_dirty = true;
                            self.resize_bar_win(mi)?;
                        }
                    }
                    return Ok(());
                }
                // While Finder is modal, a pointer crossing must not change the
                // selected client or focus it. The popup keeps keyboard focus
                // until Finder closes and restores the saved window.
                if self.finder.is_active() {
                    return Ok(());
                }
                let found = self
                    .clients
                    .iter()
                    .find(|c| c.win == e.event && self.is_visible(c))
                    .map(|c| (c.win, c.mon));
                if let Some((win, mon)) = found {
                    if self.keep_selection_entering_fullscreen(win, mon) {
                        return Ok(());
                    }
                    let selection_changed =
                        self.selmon != mon || self.monitors[mon].sel != Some(win);
                    self.selmon = mon;
                    self.monitors[mon].sel = Some(win);
                    self.focus()?;
                    if selection_changed {
                        self.bar_dirty = true;
                    }
                }
            }
            Event::LeaveNotify(e) => {
                let finder_crossing = self.finder.is_active()
                    && self
                        .monitors
                        .iter()
                        .any(|m| m.barcenterwin == e.event || m.finder_markerwin == e.event);
                if finder_crossing {
                    return Ok(());
                }
                if self.notification_leave(&e)? {
                    return Ok(());
                }
                if let Some(mi) = self
                    .monitors
                    .iter()
                    .position(|m| m.barrightwin == e.event || m.mpris_markerwin == e.event)
                {
                    let root_x = e.root_x as i32;
                    let root_y = e.root_y as i32;
                    let mut dirty = false;
                    if self.monitors[mi].mpris_markerwin == e.event && self.mpris_marker_hovered {
                        self.mpris_marker_hovered = false;
                        dirty = true;
                        self.update_mpris_marker_class(mi)?;
                    }
                    let over_marker = self.mpris_marker_rect.is_some_and(|(x, y, w, h)| {
                        root_x >= x && root_x < x + w && root_y >= y && root_y < y + h
                    });
                    if !self.pointer_over_mpris_bar(mi, root_x, root_y)
                        && !over_marker
                        && !self.mpris_volume_drag
                        && (self.mpris_hovered || self.mpris_marker_hovered)
                    {
                        self.mpris_hovered = false;
                        self.mpris_marker_hovered = false;
                        dirty = true;
                        self.resize_bar_win(mi)?;
                    }
                    if dirty {
                        self.bar_dirty = true;
                    }
                    return Ok(());
                }
            }
            Event::ButtonPress(e) => {
                if self.notification_button(&e)? {
                    return Ok(());
                }
                if self.tags_button(&e)? {
                    return Ok(());
                }
                self.bar_dirty = true;
                let state = u16::from(e.state) & CLEAN_MASK;
                let at = (e.root_x as i32, e.root_y as i32);
                let owner = self.clients.iter().find_map(|c| {
                    if c.win == e.event {
                        return Some((c.win, None));
                    }
                    let zone = c.edge_wins.iter().position(|w| *w == e.event)?;
                    Some((c.win, Some(tree::ZONE_EDGES[zone])))
                });
                if let Some((win, zone)) = owner {
                    match (state, e.detail, zone) {
                        (0, 1, Some(edges)) => return self.resizemouse(win, at, Some(edges)),
                        (MOD_4, 1, _) => return self.movemouse(win, at),
                        (MOD_4, 3, _) => return self.resizemouse(win, at, None),
                        _ => {}
                    }
                }
                if let Some(mi) = self
                    .monitors
                    .iter()
                    .position(|m| m.barrightwin == e.event || m.mpris_markerwin == e.event)
                {
                    if self.monitors[mi].mpris_markerwin == e.event {
                        self.mpris_marker_hovered = false;
                        let x = e.root_x as i32 - self.rightbar_x(mi);
                        let y = e.root_y as i32 - self.monitors[mi].by;
                        self.mpris_panel_button(mi, x, y, e.detail);
                        return Ok(());
                    }
                    if self.mpris_hovered {
                        self.mpris_panel_button(mi, e.event_x as i32, e.event_y as i32, e.detail);
                        return Ok(());
                    }
                }
            }
            Event::ButtonRelease(e) => {
                self.bar_dirty = true;
                if self
                    .monitors
                    .iter()
                    .any(|m| m.barrightwin == e.event || m.mpris_markerwin == e.event)
                {
                    self.mpris_volume_drag = false;
                    return Ok(());
                }
            }
            Event::MotionNotify(e) => {
                if self.notification_motion(&e)? {
                    return Ok(());
                }
                if self.mpris_volume_drag {
                    if let Some(mi) = self
                        .monitors
                        .iter()
                        .position(|m| m.barrightwin == e.event || m.mpris_markerwin == e.event)
                    {
                        let x = e.root_x as i32 - self.rightbar_x(mi);
                        self.set_mpris_volume_from_x(mi, x);
                        self.bar_dirty = true;
                    }
                } else {
                    self.activate_monitor_at(e.root_x as i32, e.root_y as i32)?;
                }
            }
            Event::KeyPress(e) => {
                if self.notification_keypress(&e)? {
                    return Ok(());
                }
                self.key_press(e)?;
                self.bar_dirty = true;
            }
            Event::PropertyNotify(e)
                if e.atom == self.atoms.xembed_info && self.is_tray_icon(e.window) =>
            {
                if self.tray.read_info(&self.conn, e.window) {
                    self.relayout_tray()?;
                }
            }
            Event::PropertyNotify(e) if e.atom == self.atoms.net_wm_icon => {
                // A client changed its app icon; drop the decoded pixels so the
                // next bar frame reads the new property (AnDWM's `updateicon`).
                self.icon_cache.borrow_mut().remove(&e.window);
                self.bar_dirty = true;
            }
            Event::PropertyNotify(e)
                if e.atom == u32::from(AtomEnum::WM_NAME) || e.atom == self.atoms.net_wm_name =>
            {
                if e.window == self.root {
                    let prop = self
                        .conn
                        .get_property(false, self.root, e.atom, AtomEnum::ANY, 0, 1024)
                        .ok()
                        .and_then(|c| c.reply().ok());
                    if let Some(r) = prop {
                        let text = String::from_utf8_lossy(&r.value).into_owned();
                        let text = text.trim();
                        if !text.is_empty() {
                            self.status.set_custom(Some(text.to_string()));
                        } else {
                            self.status.set_custom(None);
                        }
                        self.update_status();
                    }
                } else {
                    // A client renamed itself; drop the cached title and let
                    // the next frame show the new name.
                    self.name_cache.borrow_mut().remove(&e.window);
                }
                self.bar_dirty = true;
            }
            Event::PropertyNotify(e) if e.atom == u32::from(AtomEnum::WM_NORMAL_HINTS) => {
                if let Some(idx) = self.clients.iter().position(|c| c.win == e.window) {
                    let hints = self.read_size_hints(e.window).unwrap_or_default();
                    let (mon, transient, win_type, is_modal, auto_place, fullscreen, old_hints) = {
                        let c = &self.clients[idx];
                        (
                            c.mon,
                            c.transient_for,
                            c.win_type,
                            c.is_modal,
                            c.auto_place,
                            c.fullscreen,
                            c.hints,
                        )
                    };
                    let old_float = wants_floating(win_type, transient, is_modal, &old_hints);
                    let new_float = wants_floating(win_type, transient, is_modal, &hints);
                    self.clients[idx].hints = hints;
                    // A client may publish its fixed size only after mapping;
                    // move it out of (or back into) the tiling tree then. A
                    // hint refresh that leaves the policy unchanged must not
                    // re-evaluate it at all (that used to undo Super+W).
                    let changed = if fullscreen || old_float == new_float {
                        false
                    } else {
                        self.set_client_floating(idx, new_float)
                    };
                    // Toolkits often publish size hints after mapping. Resize
                    // and re-center a still auto-placed floating window around
                    // them, including one that just became floating here.
                    if self.clients[idx].floating
                        && auto_place
                        && self.is_visible(&self.clients[idx])
                    {
                        let parent = self.transient_geometry(transient, mon);
                        self.clients[idx].geom =
                            floating_geometry(&hints, self.work(mon), parent, BORDERPX);
                        self.place_floating(e.window)?;
                    }
                    if changed {
                        self.arrange()?;
                    }
                }
            }
            Event::PropertyNotify(e) if e.atom == u32::from(AtomEnum::WM_HINTS) => {
                if let Some(idx) = self.clients.iter().position(|c| c.win == e.window) {
                    let (wants_input, urgent) = self.read_wm_hints(e.window);
                    self.clients[idx].wants_input = wants_input;
                    self.clients[idx].urgent = urgent;
                    self.clients[idx].demands_attention = urgent;
                    if urgent {
                        let _ = self.sync_client_wm_state(&self.clients[idx]);
                    }
                    self.bar_dirty = true;
                }
            }
            Event::PropertyNotify(e)
                if e.atom == self.atoms.wm_transient_for
                    || e.atom == self.atoms.net_wm_window_type
                    || e.atom == self.atoms.net_wm_state =>
            {
                if let Some(idx) = self.clients.iter().position(|c| c.win == e.window) {
                    let win = e.window;
                    // Honor fullscreen requested by writing _NET_WM_STATE
                    // directly, without a _NET_WM_STATE ClientMessage.
                    let wants_fullscreen = self
                        .read_net_wm_state(win)
                        .contains(&self.atoms.net_wm_state_fullscreen);
                    if wants_fullscreen != self.clients[idx].fullscreen {
                        self.toggle_fullscreen_for(win)?;
                    }
                    let transient_for = self.read_transient_for(win);
                    let win_type = self.read_win_type(win);
                    let is_modal = self.read_net_wm_state_modal(win);
                    let (mon, old_transient, was_modal, fullscreen) = {
                        let c = &self.clients[idx];
                        (c.mon, c.transient_for, c.is_modal, c.fullscreen)
                    };
                    self.clients[idx].transient_for = transient_for;
                    self.clients[idx].win_type = win_type;
                    self.clients[idx].is_modal = is_modal;
                    let want_float =
                        wants_floating(win_type, transient_for, is_modal, &self.clients[idx].hints)
                            || matches!(win_type, WinType::Dock | WinType::Desktop);
                    // rwm writes HIDDEN (and the other WM-owned state atoms)
                    // itself whenever a tag switch maps or unmaps a client.
                    // That generates a PropertyNotify back to us; treating it
                    // as a new float decision would undo a manual float just
                    // because the window left its workspace. Of all the
                    // _NET_WM_STATE atoms, only MODAL affects floating, so
                    // recheck the policy only when it really changed (or when
                    // the type/transient property itself changed).
                    let recheck = e.atom != self.atoms.net_wm_state || is_modal != was_modal;
                    // Leave the saved layout state of a fullscreen client alone.
                    let changed = if fullscreen || !recheck {
                        false
                    } else {
                        self.set_client_floating(idx, want_float)
                    };
                    // pkexec-style dialogs often set _NET_WM_WINDOW_TYPE after
                    // mapping. Give those windows a real floating placement
                    // instead of freezing their temporary tiling tile.
                    let reposition = want_float
                        && self.clients[idx].auto_place
                        && (changed || transient_for != old_transient);
                    if reposition {
                        let parent = self.transient_geometry(transient_for, mon);
                        self.clients[idx].geom = floating_geometry(
                            &self.clients[idx].hints,
                            self.work(mon),
                            parent,
                            BORDERPX,
                        );
                        self.place_floating(win)?;
                    }
                    if changed || reposition {
                        self.arrange()?;
                    } else {
                        self.bar_dirty = true;
                    }
                }
            }
            Event::ClientMessage(e) => {
                self.client_message(e)?;
            }
            Event::SelectionRequest(e) => {
                self.tray.selection_request(&self.conn, &e)?;
                self.conn.flush()?;
            }
            Event::SelectionClear(e) if e.selection == self.tray.selection => {
                // Another tray took over. Hide our icons so their windows are
                // not stranded as visible children of an inert tray.
                self.tray.release(&self.conn);
                self.bar_dirty = true;
            }
            Event::Expose(e) => {
                // Like dwm's expose(), only the last event in a batch needs a
                // repaint, and only the window that was actually exposed. A
                // global force here makes every GL section swap during a drag.
                if e.count == 0
                    && self.monitors.iter().any(|m| {
                        [
                            m.barwin,
                            m.bartitlewin,
                            m.barkbwin,
                            m.barcenterwin,
                            m.barrightwin,
                        ]
                        .contains(&e.window)
                    })
                {
                    self.force_windows.borrow_mut().insert(e.window);
                    if self.notification.is_center_active()
                        && self.monitors[self.selmon].barcenterwin == e.window
                    {
                        self.notification_force.set(true);
                    }
                    self.bar_dirty = true;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn client_message(&mut self, e: ClientMessageEvent) -> Result {
        if e.type_ == self.atoms.net_system_tray_opcode {
            // Freedesktop sends the message to the selection owner, with the
            // icon window both in `window` and in data.l[1]. Accept either
            // convention so different toolkits can dock.
            let data = e.data.as_data32();
            let icon = data.get(2).copied().or_else(|| data.get(1).copied()).unwrap_or(0);
            if e.window == self.tray.window || icon == e.window
                || data.get(1).copied().unwrap_or(0) == e.window
            {
                if self.tray.opcode(&self.conn, self.tray.window, &data)? {
                    // A newly docked icon must be placed and mapped now; apps
                    // do not necessarily follow the dock request with a map.
                    self.relayout_tray()?;
                    self.conn.flush()?;
                }
                return Ok(());
            }
        }
        if self.tray.is_xembed_message(&e) {
            self.tray.handle_xembed(&self.conn, &e)?;
            self.conn.flush()?;
            return Ok(());
        }
        if e.type_ == self.atoms.net_active_window {
            let win = e.window;
            if let Some(ci) = self.clients.iter().position(|c| c.win == win) {
                let mon = self.clients[ci].mon;
                self.selmon = mon;
                self.monitors[mon].sel = Some(win);
                self.focus()?;
                self.focus_hold_until = Instant::now() + Duration::from_millis(120);
                self.bar_dirty = true;
            }
        } else if e.type_ == self.atoms.net_close_window {
            let win = e.window;
            if self.is_managed(win) {
                if self.supports_delete(win) {
                    let ev = ClientMessageEvent::new(
                        32,
                        win,
                        self.atoms.wm_protocols,
                        [self.atoms.wm_delete, CURRENT_TIME, 0, 0, 0],
                    );
                    self.conn.send_event(false, win, EventMask::NO_EVENT, ev)?;
                } else {
                    self.conn.kill_client(win)?;
                }
                self.conn.flush()?;
            }
        } else if e.type_ == self.atoms.net_current_desktop {
            let idx = e.data.as_data32()[0] as usize;
            if idx < TAG_COUNT as usize {
                let tag = 1u32 << idx;
                self.view(tag)?;
            }
        } else if e.type_ == self.atoms.net_wm_desktop {
            // A client is not allowed to decide which workspace the user
            // wants it on. Firefox-based browsers (and other apps with
            // session restore) replay the desktop their last window was on
            // as soon as a new window is mapped, which yanks the new window
            // off the workspace it was spawned on. EWMH explicitly lets a
            // WM treat application requests differently from direct user
            // actions: only honor a move when a pager asks for it (source
            // indication 2). Source 0/1 is an application or an old client.
            if e.data.as_data32()[1] != 2 {
                return Ok(());
            }
            let desk = e.data.as_data32()[0];
            if desk == 0xFFFFFFFF {
                // sticky: mark as all tags (best effort) - not fully modeled; skip
            } else {
                let idx = desk as usize;
                if idx < TAG_COUNT as usize {
                    let tag = 1u32 << idx;
                    if let Some(ci) = self.clients.iter().position(|c| c.win == e.window) {
                        self.clients[ci].tags = tag;
                        let _ = self.set_client_desktop(self.clients[ci].win, tag);
                        self.arrange()?;
                    }
                }
            }
        } else if e.type_ == self.atoms.net_wm_state {
            let data = e.data.as_data32();
            let action = data[0];
            let atom1 = data[1];
            let atom2 = data[2];
            let win = e.window;
            if self.is_managed(win) {
                let mut changed = false;
                for atom in [atom1, atom2] {
                    if atom == 0 { continue; }
                    if let Some(idx) = self.clients.iter().position(|c| c.win == win) {
                        if atom == self.atoms.net_wm_state_fullscreen {
                            let is_fs = self.clients[idx].fullscreen;
                            let want = match action { 0 => false, 1 => true, 2 => !is_fs, _ => is_fs };
                            if want != is_fs {
                                self.toggle_fullscreen_for(win)?;
                                changed = true;
                            }
                        } else if atom == self.atoms.net_wm_state_maximized_horz || atom == self.atoms.net_wm_state_maximized_vert {
                            self.apply_maximize_request(win, atom, action)?;
                            changed = true;
                        } else {
                            let cur = if atom == self.atoms.net_wm_state_above { self.clients[idx].above }
                                else if atom == self.atoms.net_wm_state_below { self.clients[idx].below }
                                else if atom == self.atoms.net_wm_state_modal { self.clients[idx].is_modal }
                                else if atom == self.atoms.net_wm_state_demands_attention { self.clients[idx].demands_attention }
                                else if atom == self.atoms.net_wm_state_hidden { self.clients[idx].hidden }
                                else if atom == self.atoms.net_wm_state_sticky { self.clients[idx].sticky }
                                else if atom == self.atoms.net_wm_state_skip_taskbar { self.clients[idx].skip_taskbar }
                                else if atom == self.atoms.net_wm_state_skip_pager { self.clients[idx].skip_pager }
                                else { false };
                            let want = match action { 0 => false, 1 => true, 2 => !cur, _ => cur };
                            if atom == self.atoms.net_wm_state_above { self.clients[idx].above = want; }
                            else if atom == self.atoms.net_wm_state_below { self.clients[idx].below = want; }
                            else if atom == self.atoms.net_wm_state_modal { self.clients[idx].is_modal = want; }
                            else if atom == self.atoms.net_wm_state_demands_attention { self.clients[idx].demands_attention = want; }
                            else if atom == self.atoms.net_wm_state_hidden {
                                // Use the same path as Super+H/Shift+H so the
                                // restore stack and ICCCM state stay in sync.
                                if want { self.set_hidden(win, true)?; }
                                else { self.restore_client(win)?; }
                            }
                            else if atom == self.atoms.net_wm_state_sticky { self.clients[idx].sticky = want; }
                            else if atom == self.atoms.net_wm_state_skip_taskbar { self.clients[idx].skip_taskbar = want; }
                            else if atom == self.atoms.net_wm_state_skip_pager { self.clients[idx].skip_pager = want; }
                            if let Some(c) = self.clients.get(idx) {
                                let _ = self.sync_client_wm_state(c);
                            }
                            changed = true;
                        }
                    }
                }
                if changed { self.arrange()?; }
            }
        } else if e.type_ == self.atoms.wm_change_state {
            // ICCCM WM_CHANGE_STATE
            let state = e.data.as_data32()[0];
            if state == WM_STATE_ICONIC {
                self.set_hidden(e.window, true)?;
                self.arrange()?;
            } else if state == WM_STATE_NORMAL {
                self.restore_client(e.window)?;
            } else if state == WM_STATE_WITHDRAWN {
                // WithdrawnState: the client gives up being shown. Hide it like
                // an iconified window so its tile collapses and a later tag
                // switch does not remap an empty, withdrawn window.
                self.set_hidden(e.window, true)?;
                self.arrange()?;
            }
        } else if e.type_ == self.atoms.net_wm_ping {
            // Reply to ping
            let mut ev = e;
            ev.response_type = x11rb::protocol::xproto::CLIENT_MESSAGE_EVENT;
            let _ = self.conn.send_event(false, self.root, EventMask::SUBSTRUCTURE_REDIRECT | EventMask::SUBSTRUCTURE_NOTIFY, ev);
            self.conn.flush()?;
        }
        Ok(())
    }

    fn apply_maximize_request(&mut self, win: Window, atom: u32, action: u32) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else { return Ok(()); };
        let mi = self.clients[idx].mon;
        let is_horz = atom == self.atoms.net_wm_state_maximized_horz;
        let cur = if is_horz { self.clients[idx].maximized_horz } else { self.clients[idx].maximized_vert };
        let want = match action { 0 => false, 1 => true, 2 => !cur, _ => cur };
        if want == cur { return Ok(()); }
        if self.clients[idx].saved_geom.is_none() && !self.clients[idx].fullscreen {
            self.clients[idx].saved_geom = Some(self.clients[idx].geom);
            self.clients[idx].saved_floating = self.clients[idx].floating;
        }
        if is_horz { self.clients[idx].maximized_horz = want; } else { self.clients[idx].maximized_vert = want; }
        let mrect = self.monitors[mi].rect;
        let any_max = self.clients[idx].maximized_horz || self.clients[idx].maximized_vert;
        if any_max {
            let mut g = self.clients[idx].saved_geom.unwrap_or(self.clients[idx].geom);
            if self.clients[idx].maximized_horz {
                g.x = mrect.x;
                g.w = mrect.w;
            } else if let Some(saved) = self.clients[idx].saved_geom {
                g.x = saved.x; g.w = saved.w;
            }
            if self.clients[idx].maximized_vert {
                g.y = mrect.y;
                g.h = mrect.h;
            } else if let Some(saved) = self.clients[idx].saved_geom {
                g.y = saved.y; g.h = saved.h;
            }
            self.clients[idx].floating = true;
            self.clients[idx].geom = g;
            // Maximizing chooses an explicit geometry; stop auto-placing.
            self.clients[idx].auto_place = false;
        } else {
            // restore
            if let Some(saved) = self.clients[idx].saved_geom.take() {
                self.clients[idx].geom = saved;
            }
            self.clients[idx].floating = self.clients[idx].saved_floating;
            self.clients[idx].saved_floating = false;
            if !self.clients[idx].floating {
                if !self.monitors[mi].tree.as_ref().is_some_and(|t| t.has_leaf(win)) {
                    let area = self.tile_area(mi);
                    let tree = &mut self.monitors[mi].tree;
                    *tree = Some(tree::append(tree.take(), win, area));
                }
            }
        }
        let _ = self.sync_client_wm_state(&self.clients[idx]);
        Ok(())
    }

    fn key_press(&mut self, e: KeyPressEvent) -> Result {
        let Some(&sym) = self.keysyms.get((e.detail - self.min_keycode) as usize) else {
            return Ok(());
        };
        let state = u16::from(e.state) & CLEAN_MASK;
        let actions: Vec<Action> = self
            .keys
            .iter()
            .filter(|k| k.keysym == sym && k.mods == state)
            .map(|k| k.action)
            .collect();
        if !actions.is_empty() {
            self.sync_selmon_to_pointer()?;
        }
        for action in actions {
            self.run(action)?;
        }
        Ok(())
    }

    fn run(&mut self, action: Action) -> Result {
        match action {
            Action::View(t) => self.view(t),
            Action::ToggleView(t) => self.toggleview(t),
            Action::Tag(t) => self.tag(t),
            Action::ToggleTag(t) => self.toggletag(t),
            Action::ViewAll => self.view(!0),
            Action::TagAll => self.tag(!0),
            Action::ViewPrev => self.view(0),
            Action::ShiftView(d) => self.shiftview(d),
            Action::FocusStack(d) => self.focusstack(d),
            Action::MoveStack(d) => self.movestack(d),
            Action::Zoom => self.zoom(),
            Action::ToggleFloating => self.togglefloating(),
            Action::ToggleFullScreen => self.toggle_fullscreen(),
            Action::Iconify => self.iconify(),
            Action::Deiconify => self.deiconify(),
            Action::KillClient => self.killclient(),
            Action::ForceKillClient => self.forcekillclient(),
            Action::FocusMon(d) => self.focusmon(d),
            Action::TagMon(d) => self.tagmon(d),
            Action::ToggleBar => self.togglebar(),
            Action::ToggleGaps => self.togglegaps(),
            Action::DefaultGaps => self.defaultgaps(),
            Action::IncrGaps(scope, d) => self.incrgaps(scope, d),
            Action::Finder => return self.finder_toggle(),
            Action::FinderOcr => {
                // Like dwm, OCR selects a region before Finder opens; the
                // worker's result becomes the initial query. Pressing it while
                // Finder is already modal is a no-op.
                if self.finder.is_active() {
                    return Ok(());
                }
                let dpy = self.drw.dpy();
                if let Err(err) = self.finder.ocr(dpy) {
                    self.finder.clear_ocr();
                    return Err(err);
                }
                return Ok(());
            }
            Action::Restart => {
                self.restart = true;
                Ok(())
            }
            Action::Spawn(cmd) => spawn(cmd),
        }
    }

    /// Grabs the pointer and calls `on_motion` with the newest position once
    /// the queued motion events are drained, so a burst of moves costs one
    /// update. `win` carries `_NO_ANIMATION` for the length of the drag. Returns
    /// the release position, or `None` if the grab failed.
    fn drag_pointer(
        &mut self,
        win: Window,
        cursor: u32,
        throttle_motion: bool,
        mut on_motion: impl FnMut(&mut Wm, i32, i32) -> Result,
    ) -> Result<Option<(i32, i32)>> {
        let reply = self
            .conn
            .grab_pointer(
                false,
                self.root,
                EventMask::BUTTON_MOTION | EventMask::BUTTON_RELEASE,
                GrabMode::ASYNC,
                GrabMode::ASYNC,
                NONE,
                cursor,
                CURRENT_TIME,
            )?
            .reply()?;
        if reply.status != GrabStatus::SUCCESS {
            return Ok(None);
        }
        self.set_no_animation(win, true)?;
        self.pointer_grabbed = true;
        let mut last_frame = Instant::now();
        let mut last_bar_tick = Instant::now();
        let mut latest = None;
        let mut end: Option<(i32, i32)> = None;
        let result = (|| -> Result {
            loop {
                // dwm's drag_next_event() blocks on the X connection until an event
                // arrives or the next bar tick is due. Sleeping and polling at a
                // fixed 5 ms here burns CPU and adds a wakeup of latency to every
                // pointer update.
                let mut pending = self.conn.poll_for_event()?;
                if pending.is_none() {
                    self.wait_event(DRAG_FRAME.saturating_sub(last_frame.elapsed()))?;
                    pending = self.conn.poll_for_event()?;
                }
                while let Some(event) = pending {
                    match event {
                        Event::MotionNotify(e) => latest = Some((e.root_x as i32, e.root_y as i32)),
                        Event::ButtonRelease(e) => {
                            let pos = (e.root_x as i32, e.root_y as i32);
                            on_motion(self, pos.0, pos.1)?;
                            end = Some(pos);
                            return Ok(());
                        }
                        other => self.handle(other)?,
                    }
                    pending = self.conn.poll_for_event()?;
                }
                // dwm's movemouse() applies the newest queued position right after
                // draining the motion burst; only resizemouse() uses the 60 Hz gate.
                if !throttle_motion && let Some((x, y)) = latest.take() {
                    on_motion(self, x, y)?;
                }
                // Apply only the newest resize position, at most once per frame.
                if last_frame.elapsed() >= DRAG_FRAME {
                    if throttle_motion && let Some((x, y)) = latest.take() {
                        on_motion(self, x, y)?;
                    }
                    last_frame = Instant::now();
                }
                // Bar animation uses the main loop's 16.67 ms grid, not the
                // 16 ms pointer gate, so drags cannot run a second clock.
                if last_bar_tick.elapsed() >= BAR_TICK {
                    self.refresh()?;
                    last_bar_tick = Instant::now();
                }
            }
        })();
        self.pointer_grabbed = false;
        let _ = self.conn.ungrab_pointer(CURRENT_TIME);
        let _ = self.set_no_animation(win, false);
        let _ = self.conn.flush();
        result.map(|_| end)
    }

    /// Waits until the X connection has an event or `timeout` expires. The
    /// main loop uses this instead of an unconditional sleep, so an event is
    /// handled as soon as it arrives like C dwm's blocking `XNextEvent`.
    /// Round up: truncating a fractional-millisecond deadline made the 60 fps
    /// clock cadence slightly slower than the requested 16.67 ms interval.
    pub fn wait_event(&self, timeout: Duration) -> Result {
        let mut pfd = libc::pollfd {
            fd: self.conn.stream().as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        let nanos = timeout.as_nanos();
        let mut ms = nanos / 1_000_000;
        if !nanos.is_multiple_of(1_000_000) {
            ms += 1;
        }
        let ms = ms.min(i32::MAX as u128) as i32;
        if unsafe { libc::poll(&mut pfd, 1, ms) } < 0 {
            let err = std::io::Error::last_os_error();
            if err.kind() != std::io::ErrorKind::Interrupted {
                return Err(err.into());
            }
        }
        Ok(())
    }

    fn set_no_animation(&self, win: Window, on: bool) -> Result {
        if on {
            self.conn.change_property32(
                PropMode::REPLACE,
                win,
                self.atoms.no_animation,
                AtomEnum::CARDINAL,
                &[1],
            )?;
        } else {
            self.conn.delete_property(win, self.atoms.no_animation)?;
        }
        Ok(())
    }

    /// Puts the floating window `win` on top, with its hover zones right above
    /// it.
    fn raise_floating(&mut self, win: Window) -> Result {
        let Some(i) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let client = self.clients.remove(i);
        self.clients.insert(0, client);
        self.conn
            .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE))?;
        // Raising a floating client must not bury a menu that was already open.
        self.raise_bars()?;
        self.invalidate_finder_stacking();
        self.place_floating(win)
    }

    /// Moves one floating window and its hover zones to their current
    /// geometry, leaving the tiled windows alone.
    fn place_floating(&mut self, win: Window) -> Result {
        self.place_floating_inner(win, true)
    }

    /// The drag path uses this with `restack = false`: raising the window once
    /// at the start of the drag already put its zones above it, so repeating
    /// eight stack requests per frame only delays the client's redraw.
    fn place_floating_inner(&mut self, win: Window, restack: bool) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let (rect, _) = self.place_client(&self.clients[idx], self.clients[idx].geom)?;
        let zones = self.clients[idx].edge_wins;
        self.clients[idx].geom = rect;
        self.place_edge_zones(zones, win, rect, restack)?;
        if restack {
            // raise_floating()/client ConfigureRequest put this window and its
            // zones on top; the bars must follow them back into the top layer.
            self.raise_bars()?;
        }
        self.conn.flush()?;
        Ok(())
    }

    /// Geometry while dragging. The grab offset stays under the pointer and
    /// the window keeps its size, exactly like a floating drag.
    fn drag_geom((x, y): (i32, i32), (ox, oy): (i32, i32), current: Rect) -> Rect {
        Rect {
            x: x - ox,
            y: y - oy,
            w: current.w,
            h: current.h,
        }
    }

    /// Center of a window's current box. Used when a floating window returns
    /// to tiling with no pointer involved, so it lands where it is drawn.
    fn window_center(geom: Rect) -> (i32, i32) {
        (geom.x + geom.w as i32 / 2, geom.y + geom.h as i32 / 2)
    }

    /// Nearest tile to a point. A drop can land in a gap or on the bar, where no
    /// tile contains the pointer; Hyprland falls back to the closest node.
    fn nearest_tile<'a>(
        leaves: &'a [(Window, Rect)],
        (px, py): (i32, i32),
    ) -> Option<&'a (Window, Rect)> {
        let px = px as i64;
        let py = py as i64;
        leaves.iter().min_by_key(|(_, r)| {
            let (left, right) = (r.x as i64, r.x as i64 + r.w as i64);
            let (top, bottom) = (r.y as i64, r.y as i64 + r.h as i64);
            let dx = if px < left {
                left - px
            } else if px >= right {
                px - right
            } else {
                0
            };
            let dy = if py < top {
                top - py
            } else if py >= bottom {
                py - bottom
            } else {
                0
            };
            dx * dx + dy * dy
        })
    }

    /// Insert `win` into the tiling tree at `point` the same way a tile-mode
    /// drop does. A point on an inner gap becomes a tile of its own between the
    /// two neighbours; a point in an outer margin (or on the bar) adds a
    /// row/column on that edge. Neighbours shrink to make room in both cases.
    /// Otherwise split the tile under the point (or the closest tile). The old
    /// leaf is removed first, so a window returning from floating lands where
    /// it is actually drawn instead of in its former tile.
    fn tile_at(&mut self, win: Window, point: (i32, i32)) -> Result {
        let tm = self.monitor_at(point.0, point.1);
        let from = self.clients.iter().find(|c| c.win == win).map(|c| c.mon);
        if Some(tm) != from {
            self.sendmon(win, tm)?;
        }
        self.selmon = tm;
        self.monitors[tm].sel = Some(win);
        // Remove the leaf before reading the layout, just like a drop. The
        // pre-move half's aspect ratio would otherwise flip the split axis and
        // make repeated retile/drop operations alternate directions.
        {
            let tree = &mut self.monitors[tm].tree;
            *tree = tree.take().and_then(|t| t.remove(win));
        }
        let leaves: Vec<(Window, Rect)> = self.layout_mon(tm).into_iter().collect();
        // Try the gaps first. The visible leaves are exactly the ones the tree
        // layout used above, so a strip that contains the pointer is a real
        // boundary between two tiles on this monitor.
        let vis: HashSet<Window> = leaves.iter().map(|(w, _)| *w).collect();
        let area = self.tile_area(tm);
        let gaps = self.effective_gaps(tm);
        if let Some(tree) = self.monitors[tm].tree.as_mut()
            && tree.insert_in_gap(area, &vis, &gaps, point, win)
        {
            return Ok(());
        }
        // Outer margins, including the bar strip above the work area, are
        // edges rather than splits: add a row/column there instead of
        // splitting the nearest tile.
        let outer = self.monitors[tm].rect;
        if let Some(tree) = self.monitors[tm].tree.as_mut()
            && tree.insert_at_edge(outer, area, &vis, &gaps, point, win)
        {
            return Ok(());
        }
        let target = leaves
            .iter()
            .copied()
            .find(|(_, r)| r.contains(point.0, point.1))
            .or_else(|| Self::nearest_tile(&leaves, point).copied());
        match target {
            Some((target, rect)) => {
                let (new_first, side_by_side) = tree::split_for_drop(rect, point);
                if let Some(t) = self.monitors[tm].tree.as_mut() {
                    t.insert(target, win, new_first, side_by_side);
                }
            }
            None => {
                // No tile available: append beside what's left of the tree.
                // Replacing it with a single leaf would drop the hidden leaves
                // of other tags and break those tags on return.
                let area = self.tile_area(tm);
                let tree = &mut self.monitors[tm].tree;
                *tree = Some(tree::append(tree.take(), win, area));
            }
        }
        Ok(())
    }

    /// dwm's `movemouse()` with Hyprland-style dwindle dragging. A floating
    /// window follows the pointer. A tiled window is temporarily taken out of
    /// the tree at its current size, so its siblings expand while it follows
    /// the pointer. On release it is removed
    /// first, then reinserted as an even split into the tile under the pointer
    /// in the expanded layout, the same order `onWindowCreatedTiling` uses.
    /// A drop in a gap places the window between the two neighbours there.
    fn movemouse(&mut self, win: Window, (px, py): (i32, i32)) -> Result {
        let Some(client) = self.clients.iter().find(|c| c.win == win) else {
            return Ok(());
        };
        // A fullscreen window owns the whole monitor; dragging it would break
        // that, so ignore Super+drag until it leaves fullscreen.
        if client.fullscreen {
            return Ok(());
        }
        let (mi, floating) = (client.mon, client.floating);
        let Some(start) = self.geometry(mi, win) else {
            return Ok(());
        };
        self.selmon = mi;
        self.monitors[mi].sel = Some(win);
        self.focus()?;
        if floating {
            self.raise_floating(win)?;
        } else {
            // Hide the tiled leaf so siblings expand into the whole workspace,
            // but keep the client visible and movable at its current size.
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == win) {
                c.dragging = true;
                c.geom = start;
            }
            // Remove the dragged window from the tree and even out its
            // row/column so both neighbours grow. Otherwise a dwindle tree
            // gives all the freed space to one sibling, and dropping the
            // window back into a gap makes the other windows jump sideways.
            let vis: HashSet<Window> = self.tiled_order(mi).into_iter().collect();
            let area = self.tile_area(mi);
            let gaps = self.effective_gaps(mi);
            if let Some(tree) = self.monitors[mi].tree.as_mut() {
                tree.prepare_for_drag(win, &vis, area, &gaps);
            }
            // Raise once at drag start. apply_layout() only restacks the zones;
            // repeated stack requests per frame delay the client's redraw.
            self.conn
                .configure_window(win, &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE))?;
            self.apply_layout()?;
        }
        let (ox, oy) = (px - start.x, py - start.y);
        let drag = self.drag_pointer(win, self.resize_cursors.moving, false, |wm, x, y| {
            if let Some(c) = wm.clients.iter_mut().find(|c| c.win == win) {
                c.geom = Self::drag_geom((x, y), (ox, oy), c.geom);
            }
            wm.place_floating_inner(win, false)
        });
        // Clear the temporary state before any layout decision, including when
        // the drag failed or the pointer grab never succeeded.
        if !floating {
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == win) {
                c.dragging = false;
            }
        }
        let end = match drag {
            Ok(end) => end,
            Err(err) => {
                self.arrange()?;
                return Err(err);
            }
        };
        // The pointer decides where the window lands, including which gap it
        // drops into (tile_at() handles the gap case for tiled windows).
        let Some(point) = end else {
            return self.arrange();
        };
        if floating {
            // A user-placed window keeps its spot across property updates.
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == win) {
                c.auto_place = false;
            }
            let tm = self.monitor_at(point.0, point.1);
            if tm != mi {
                self.sendmon(win, tm)?;
                self.selmon = tm;
                self.monitors[tm].sel = Some(win);
            }
            return self.arrange();
        }
        self.tile_at(win, point)?;
        self.arrange()
    }

    /// dwm's `resizemouse()`. A press on an edge zone resizes the tiling tree
    /// boundaries. A tiled window always stays tiled; a floating one follows
    /// the pointer at the same 60 Hz gate dwm uses.
    fn resizemouse(
        &mut self,
        win: Window,
        (mx, my): (i32, i32),
        zone: Option<(bool, bool, bool, bool)>,
    ) -> Result {
        let Some(client) = self.clients.iter().find(|c| c.win == win) else {
            return Ok(());
        };
        if client.fullscreen {
            return Ok(());
        }
        let (mi, floating) = (client.mon, client.floating);
        let Some(rect) = self.geometry(mi, win) else {
            return Ok(());
        };
        self.selmon = mi;
        self.monitors[mi].sel = Some(win);
        self.focus()?;
        let edges = zone.unwrap_or_else(|| tree::resize_edges(rect, (mx, my)));
        let cursor = self.resize_cursor(Some(edges));
        if floating {
            self.raise_floating(win)?;
            self.drag_pointer(win, cursor, true, |wm, x, y| {
                let geom = tree::resize_rect(rect, edges, (x - mx, y - my));
                if let Some(c) = wm.clients.iter_mut().find(|c| c.win == win) {
                    c.geom = geom;
                }
                wm.place_floating_inner(win, false)
            })?;
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == win) {
                c.auto_place = false;
            }
            return self.arrange();
        }
        let (mut lx, mut ly) = (mx, my);
        self.drag_pointer(win, cursor, true, |wm, x, y| {
            wm.resize_tiled(mi, win, edges, (x - lx, y - ly));
            (lx, ly) = (x, y);
            wm.apply_layout()
        })?;
        self.arrange()
    }

    /// Moves the tree boundaries next to the tiled window `win` on `edges`.
    fn resize_tiled(
        &mut self,
        mi: usize,
        win: Window,
        edges: (bool, bool, bool, bool),
        delta: (i32, i32),
    ) {
        let vis: HashSet<Window> = self.tiled_order(mi).into_iter().collect();
        let gaps = self.effective_gaps(mi);
        let area = self.tile_area(mi);
        if let Some(tree) = self.monitors[mi].tree.as_mut() {
            tree::resize_tiled(tree, area, &vis, &gaps, win, edges, delta);
        }
    }

    /// Reconcile an already managed client with a new floating decision, for
    /// example when a client publishes `_NET_WM_WINDOW_TYPE` or fixed size
    /// hints only after mapping. Returns true if its state changed.
    fn set_client_floating(&mut self, idx: usize, float: bool) -> bool {
        if !should_apply_float_policy(
            self.clients[idx].float_override,
            float,
            self.clients[idx].floating,
        ) {
            return false;
        }
        let win = self.clients[idx].win;
        let mi = self.clients[idx].mon;
        let stack_seq = self.next_stack_seq();
        if float {
            let geom = if self.clients[idx].auto_place {
                let hints = self.clients[idx].hints;
                let parent = self.transient_geometry(self.clients[idx].transient_for, mi);
                floating_geometry(&hints, self.work(mi), parent, BORDERPX)
            } else {
                self.geometry(mi, win).unwrap_or(self.clients[idx].geom)
            };
            self.clients[idx].floating = true;
            self.clients[idx].geom = geom;
            self.clients[idx].stack_seq = stack_seq;
        } else {
            self.clients[idx].floating = false;
            self.clients[idx].stack_seq = stack_seq;
            // Windows that were floating from the start never had a tile.
            // Put one back so the layout has a box to draw them in.
            if !self.monitors[mi]
                .tree
                .as_ref()
                .is_some_and(|t| t.has_leaf(win))
            {
                let area = self.tile_area(mi);
                let tree = &mut self.monitors[mi].tree;
                *tree = Some(tree::append(tree.take(), win, area));
            }
        }
        true
    }

    fn togglefloating(&mut self) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        let Some((fullscreen, floating, geom)) = self
            .clients
            .iter()
            .find(|c| c.win == sel)
            .map(|c| (c.fullscreen, c.floating, c.geom))
        else {
            return Ok(());
        };
        if fullscreen {
            return Ok(()); // don't toggle floating while fullscreen
        }
        let stack_seq = self.next_stack_seq();
        if floating {
            let point = Self::window_center(geom);
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
                c.floating = false;
                c.float_override = Some(false);
                c.stack_seq = stack_seq;
            }
            // Insert where the window is currently floating, using the same
            // split-and-insert as dropping a window in tile mode. Its old leaf
            // is removed, so it does not pop back into its former tile.
            self.tile_at(sel, point)?;
        } else {
            let Some(rect) = self.geometry(mi, sel) else {
                return Ok(());
            };
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
                c.floating = true;
                c.float_override = Some(true);
                c.stack_seq = stack_seq;
                c.geom = rect;
                // The user chose this geometry; property updates must not
                // recenter it behind their back.
                c.auto_place = false;
            }
        }
        self.arrange()
    }

    fn toggle_fullscreen(&mut self) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        self.toggle_fullscreen_for(sel)
    }

    fn sync_client_wm_state(&self, c: &Client) -> Result {
        let mut atoms: Vec<u32> = Vec::new();
        if c.fullscreen { atoms.push(self.atoms.net_wm_state_fullscreen); }
        if c.maximized_horz { atoms.push(self.atoms.net_wm_state_maximized_horz); }
        if c.maximized_vert { atoms.push(self.atoms.net_wm_state_maximized_vert); }
        if c.above { atoms.push(self.atoms.net_wm_state_above); }
        if c.below { atoms.push(self.atoms.net_wm_state_below); }
        if c.is_modal { atoms.push(self.atoms.net_wm_state_modal); }
        if c.demands_attention { atoms.push(self.atoms.net_wm_state_demands_attention); }
        // Hidden follows the same rule as WM_STATE: every window the WM keeps
        // unmapped is hidden, not only one iconified with Super+H.
        if self.is_iconic(c.win) { atoms.push(self.atoms.net_wm_state_hidden); }
        if c.sticky { atoms.push(self.atoms.net_wm_state_sticky); }
        if c.skip_taskbar { atoms.push(self.atoms.net_wm_state_skip_taskbar); }
        if c.skip_pager { atoms.push(self.atoms.net_wm_state_skip_pager); }
        if atoms.is_empty() {
            let _ = self.conn.delete_property(c.win, self.atoms.net_wm_state);
        } else {
            let _ = self.conn.change_property32(
                PropMode::REPLACE,
                c.win,
                self.atoms.net_wm_state,
                AtomEnum::ATOM,
                &atoms,
            );
        }
        Ok(())
    }

    fn toggle_fullscreen_for(&mut self, win: Window) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let mi = self.clients[idx].mon;
        // A fullscreen request is an explicit "on top" request, even if the
        // window was created earlier and dialogs have opened over it since.
        let stack_seq = self.next_stack_seq();
        if self.clients[idx].fullscreen {
            // exit fullscreen: restore
            let saved_geom = self.clients[idx].saved_geom.take();
            let saved_floating = self.clients[idx].saved_floating;
            self.clients[idx].fullscreen = false;
            self.clients[idx].stack_seq = stack_seq;
            self.clients[idx].floating = saved_floating;
            if let Some(g) = saved_geom {
                self.clients[idx].geom = g;
            }
            // If it was tiled before, ensure it's in tree
            if !saved_floating {
                if !self.monitors[mi].tree.as_ref().is_some_and(|t| t.has_leaf(win)) {
                    let area = self.tile_area(mi);
                    let tree = &mut self.monitors[mi].tree;
                    *tree = Some(tree::append(tree.take(), win, area));
                }
            }
            let _ = self.sync_client_wm_state(&self.clients[idx]);
        } else {
            // enter fullscreen: keep current tiling/floating state but cover screen
            let cur_geom = self.geometry(mi, win).unwrap_or(self.clients[idx].geom);
            let was_floating = self.clients[idx].floating;
            self.clients[idx].saved_geom = Some(cur_geom);
            self.clients[idx].saved_floating = was_floating;
            self.clients[idx].fullscreen = true;
            self.clients[idx].stack_seq = stack_seq;
            // Do NOT force floating; keep layout state. Just make it cover monitor.
            let mrect = self.monitors[mi].rect;
            self.clients[idx].geom = Rect {
                x: mrect.x,
                y: mrect.y,
                w: mrect.w,
                h: mrect.h,
            };
            let _ = self.sync_client_wm_state(&self.clients[idx]);
        }
        self.arrange()
    }

    fn view(&mut self, ui: u32) -> Result {
        let mi = self.selmon;
        let m = &mut self.monitors[mi];
        if ui & TAGMASK == m.tagset[m.seltags] {
            return Ok(());
        }
        m.seltags ^= 1;
        if ui & TAGMASK != 0 {
            m.prevtag = m.curtag;
            m.tagset[m.seltags] = ui & TAGMASK;
            m.curtag = if ui == !0 {
                0
            } else {
                ui.trailing_zeros() as usize + 1
            };
        } else {
            std::mem::swap(&mut m.prevtag, &mut m.curtag);
        }
        let showbar_changed = m.showbar != m.showbars[m.curtag];
        let tags = m.tagset[m.seltags];
        // dwm's view() publishes the new desktop before the windows are moved.
        self.update_current_desktop(tags)?;
        if showbar_changed {
            self.togglebar()?;
        }
        self.arrange()
    }

    fn toggleview(&mut self, ui: u32) -> Result {
        let mi = self.selmon;
        let m = &mut self.monitors[mi];
        let newtagset = m.tagset[m.seltags] ^ (ui & TAGMASK);
        if newtagset == 0 {
            return Ok(());
        }
        m.tagset[m.seltags] = newtagset;
        if newtagset == !0 {
            m.prevtag = m.curtag;
            m.curtag = 0;
        }
        // Same bit test as dwm's `1 << (curtag - 1)`, wrapping like x86 shifts.
        let bit = 1u32.wrapping_shl((m.curtag as u32).wrapping_sub(1));
        if newtagset & bit == 0 {
            m.prevtag = m.curtag;
            m.curtag = newtagset.trailing_zeros() as usize + 1;
        }
        if m.showbar != m.showbars[m.curtag] {
            self.togglebar()?;
        }
        self.arrange()
    }

    fn tag(&mut self, ui: u32) -> Result {
        let t = ui & TAGMASK;
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        if t == 0 {
            return Ok(());
        }
        let mut changed: Option<(Window, u32)> = None;
        if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
            c.tags = t;
            changed = Some((c.win, c.tags));
        }
        if let Some((win, tags)) = changed {
            let _ = self.set_client_desktop(win, tags);
        }
        self.arrange()
    }

    fn toggletag(&mut self, ui: u32) -> Result {
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        let mut changed: Option<(Window, u32)> = None;
        if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
            let newtags = c.tags ^ (ui & TAGMASK);
            if newtags != 0 {
                c.tags = newtags;
                changed = Some((c.win, newtags));
            }
        }
        if let Some((win, tags)) = changed {
            let _ = self.set_client_desktop(win, tags);
            self.arrange()?;
        }
        Ok(())
    }

    fn shiftview(&mut self, d: i32) -> Result {
        let cur = self.tags_of(self.selmon);
        let n = TAG_COUNT as i32;
        let shifted = if d > 0 {
            (cur << d) | (cur >> (n - d))
        } else {
            (cur >> -d) | (cur << (n + d))
        };
        self.view(shifted)
    }

    fn focusstack(&mut self, d: i32) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        let has_fullscreen = !self.fullscreen_windows(mi).is_empty();
        // Tiled windows are unmapped behind the fullscreen stack, so Alt+Tab
        // cycles through every fullscreen window (newest first) and floating
        // overlays. Older fullscreen clients stay mapped underneath.
        let order: Vec<Window> = if has_fullscreen {
            self.clients
                .iter()
                .filter(|c| c.mon == mi && self.is_visible(c) && (c.fullscreen || c.floating))
                .map(|c| c.win)
                .collect()
        } else {
            self.stack_order(mi)
        };
        if order.is_empty() {
            return Ok(());
        }
        let next = match order.iter().position(|&w| w == sel) {
            Some(idx) if d > 0 => (idx + 1) % order.len(),
            Some(idx) => (idx + order.len() - 1) % order.len(),
            // The current selection is hidden behind fullscreen (e.g. a tiled
            // window selected before fullscreen was entered): start at the top.
            None if d > 0 => 0,
            None => order.len() - 1,
        };
        let c = order[next];
        self.monitors[mi].sel = Some(c);
        if has_fullscreen {
            // Re-run the fullscreen map/stack gate so an overlay picked with
            // Alt+Tab gets raised. Tiled windows are never in `order` here and
            // stay unmapped behind the fullscreen stack.
            self.apply_layout()?;
        }
        self.focus()?;
        // Warping generates a synthetic crossing. When another floating
        // window covers the target's centre, that crossing used to reselect
        // the covering window and undo this explicit focus. Hold the Alt+Tab
        // selection briefly; normal focus-follows-mouse resumes afterwards.
        self.focus_hold_until = Instant::now() + Duration::from_millis(120);
        if let Some(r) = self.geometry(mi, c) {
            self.conn
                .warp_pointer(NONE, c, 0, 0, 0, 0, (r.w / 2) as i16, (r.h / 2) as i16)?;
        }
        self.conn.flush()?;
        Ok(())
    }

    fn movestack(&mut self, d: i32) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        let order = self.tiled_order(mi);
        let (Some(idx), n) = (order.iter().position(|&w| w == sel), order.len()) else {
            return Ok(());
        };
        if n < 2 {
            return Ok(());
        }
        let target = if d > 0 {
            (idx + 1) % n
        } else {
            (idx + n - 1) % n
        };
        let c = order[target];
        let sel_pos = self.clients.iter().position(|x| x.win == sel);
        let c_pos = self.clients.iter().position(|x| x.win == c);
        if let (Some(a), Some(b)) = (sel_pos, c_pos) {
            self.clients.swap(a, b);
        }
        if let Some(t) = self.monitors[mi].tree.as_mut() {
            t.swap(sel, c);
        }
        self.arrange()
    }

    fn zoom(&mut self) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        if self.clients.iter().any(|c| c.win == sel && c.floating) {
            return Ok(());
        }
        let order = self.tiled_order(mi);
        let Some(&first) = order.first() else {
            return Ok(());
        };
        let c = if sel == first {
            match order.get(1) {
                Some(&next) => next,
                None => return Ok(()),
            }
        } else {
            sel
        };
        if let Some(i) = self.clients.iter().position(|x| x.win == c) {
            let client = self.clients.remove(i);
            self.clients.insert(0, client);
        }
        let master = self.layout_mon(mi).first().map(|(w, _)| *w);
        if let (Some(master), Some(t)) = (master, self.monitors[mi].tree.as_mut())
            && master != c
        {
            t.swap(c, master);
        }
        self.monitors[mi].sel = Some(c);
        self.arrange()
    }

    fn supports_delete(&self, win: Window) -> bool {
        self.conn
            .get_property(false, win, self.atoms.wm_protocols, AtomEnum::ATOM, 0, 64)
            .ok()
            .and_then(|c| c.reply().ok())
            .and_then(|r| {
                r.value32()
                    .map(|mut it| it.any(|a| a == self.atoms.wm_delete))
            })
            .unwrap_or(false)
    }

    fn supports_take_focus(&self, win: Window) -> bool {
        self.conn
            .get_property(false, win, self.atoms.wm_protocols, AtomEnum::ATOM, 0, 64)
            .ok()
            .and_then(|c| c.reply().ok())
            .and_then(|r| {
                r.value32()
                    .map(|mut it| it.any(|a| a == self.atoms.wm_take_focus))
            })
            .unwrap_or(false)
    }

    fn killclient(&self) -> Result {
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        if self.supports_delete(sel) {
            let ev = ClientMessageEvent::new(
                32,
                sel,
                self.atoms.wm_protocols,
                [self.atoms.wm_delete, CURRENT_TIME, 0, 0, 0],
            );
            self.conn.send_event(false, sel, EventMask::NO_EVENT, ev)?;
        } else {
            self.conn.kill_client(sel)?;
        }
        self.conn.flush()?;
        Ok(())
    }

    fn forcekillclient(&self) -> Result {
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        self.conn.kill_client(sel)?;
        self.conn.flush()?;
        Ok(())
    }

    fn dirtomon(&self, d: i32) -> usize {
        let n = self.monitors.len();
        if d > 0 {
            (self.selmon + 1) % n
        } else {
            (self.selmon + n - 1) % n
        }
    }

    fn focusmon(&mut self, d: i32) -> Result {
        if self.monitors.len() < 2 {
            return Ok(());
        }
        let m = self.dirtomon(d);
        if m == self.selmon {
            return Ok(());
        }
        self.selmon = m;
        self.ensure_sel(m);
        self.focus()
    }

    fn tagmon(&mut self, d: i32) -> Result {
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        if self.monitors.len() < 2 {
            return Ok(());
        }
        let target = self.dirtomon(d);
        self.sendmon(sel, target)
    }

    fn sendmon(&mut self, win: Window, target: usize) -> Result {
        let Some(ci) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let from = self.clients[ci].mon;
        let m = &mut self.monitors[from];
        m.tree = m.tree.take().and_then(|t| t.remove(win));
        if m.sel == Some(win) {
            m.sel = None;
        }

        let area = self.tile_area(target);
        let tags = self.tags_of(target);
        {
            let t = &mut self.monitors[target];
            t.tree = Some(tree::append(t.tree.take(), win, area));
        }
        self.clients[ci].mon = target;
        self.clients[ci].tags = tags;
        let _ = self.set_client_desktop(win, tags);
        let _ = self.set_rwm_monitor(win, target);
        self.arrange()
    }

    fn togglebar(&mut self) -> Result {
        let m = &mut self.monitors[self.selmon];
        m.showbar = !m.showbar;
        m.showbars[m.curtag] = m.showbar;
        self.arrange()
    }

    /// dwm's `setgaps()`: sets the selected monitor's gaps, clamped at zero.
    fn setgaps(&mut self, oh: i32, ov: i32, ih: i32, iv: i32) -> Result {
        self.monitors[self.selmon].gaps = Gaps {
            oh: oh.max(0),
            ov: ov.max(0),
            ih: ih.max(0),
            iv: iv.max(0),
        };
        self.arrange()
    }

    fn togglegaps(&mut self) -> Result {
        self.gaps_enabled = !self.gaps_enabled;
        self.arrange()
    }

    fn defaultgaps(&mut self) -> Result {
        self.setgaps(
            config::GAPPOH,
            config::GAPPOV,
            config::GAPPIH,
            config::GAPPIV,
        )
    }

    fn incrgaps(&mut self, scope: GapScope, d: i32) -> Result {
        let g = self.monitors[self.selmon].gaps;
        let (mut oh, mut ov, mut ih, mut iv) = (g.oh, g.ov, g.ih, g.iv);
        match scope {
            GapScope::All => {
                oh += d;
                ov += d;
                ih += d;
                iv += d;
            }
            GapScope::Inner => {
                ih += d;
                iv += d;
            }
            GapScope::Outer => {
                oh += d;
                ov += d;
            }
            GapScope::InnerH => ih += d,
            GapScope::InnerV => iv += d,
            GapScope::OuterH => oh += d,
            GapScope::OuterV => ov += d,
        }
        self.setgaps(oh, ov, ih, iv)
    }

    /// dwm's `cleanup()`: release modal grabs, all bar windows and colormaps.
    /// `main` calls this before `exec()` on restart, since an exec skips Drop.
    pub fn shutdown(&mut self) {
        if self.finder.is_active() {
            self.finder.close();
        }
        if self.finder_grabbed {
            self.finder_grabbed = false;
            let _ = self.conn.ungrab_keyboard(CURRENT_TIME);
            let _ = self.conn.ungrab_pointer(CURRENT_TIME);
        }
        let _ = self
            .conn
            .set_input_focus(InputFocus::PARENT, self.root, CURRENT_TIME);
        for m in &self.monitors {
            let windows = [
                m.barwin,
                m.bartitlewin,
                m.barcenterwin,
                m.barkbwin,
                m.barrightwin,
                m.mpris_markerwin,
                m.finder_markerwin,
            ];
            for win in windows.into_iter().filter(|w| *w != 0) {
                let _ = self.conn.unmap_window(win);
                let _ = self.conn.destroy_window(win);
            }
            if m.colormap != 0 {
                let _ = self.conn.free_colormap(m.colormap);
            }
        }
        if self.finder_argb_colormap != 0 {
            let _ = self.conn.free_colormap(self.finder_argb_colormap);
            self.finder_argb_colormap = 0;
        }
        self.tray.destroy(&self.conn);
        let _ = self.conn.flush();
    }
}

impl Drop for Wm {
    fn drop(&mut self) {
        self.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn box_(w: u32, h: u32) -> Rect {
        Rect { x: 10, y: 20, w, h }
    }

    #[test]
    fn clock_animation_uses_60fps_deadline_without_finder() {
        let now = Instant::now();
        let status_next = now + Duration::from_secs(1);

        let animated = Wm::bar_next_tick(now, status_next, true, false, false, false, now, None, false);
        assert_eq!(animated, now + BAR_TICK);
        assert_eq!(BAR_TICK, Duration::from_micros(16_667));

        let idle = Wm::bar_next_tick(now, status_next, false, false, false, false, now, None, false);
        assert_eq!(idle, now + IDLE_POLL);

        let finder_next = now + Duration::from_millis(10);
        let finder = Wm::bar_next_tick(now, status_next, true, true, false, false, now, Some(finder_next), false);
        assert_eq!(finder, finder_next);

        let notification = Wm::bar_next_tick(now, status_next, true, false, true, false, now, None, false);
        assert_eq!(notification, now + IDLE_POLL);
    }

    #[test]
    fn fullscreen_idle_stops_the_60fps_bar_tick() {
        let now = Instant::now();
        let status_next = now + Duration::from_millis(1);
        let finder_next = now + Duration::from_millis(1);

        // Even every other animation source is due: a fullscreen pointer wins,
        // so the main loop wakes only at the slow housekeeping cadence.
        let idle = Wm::bar_next_tick(
            now,
            status_next,
            true,
            false,
            false,
            true,
            now,
            Some(finder_next),
            true,
        );
        assert_eq!(idle, now + FULLSCREEN_IDLE_POLL);
        assert!(FULLSCREEN_IDLE_POLL > BAR_TICK * 10);
    }

    #[test]
    fn adaptive_gain_targets_rms_and_smooths_in_log_space() {
        let rms = 0.008;
        let desired = config::CLOCK_RMS_TARGET / rms;
        let alpha = 1.0 - (-1.0_f32).exp(); // one time constant
        let expected = (desired.ln() * alpha).exp();
        let gained = Wm::adaptive_gain(1.0, rms, config::CLOCK_GAIN_ADAPT_SECS);
        assert!((gained - expected).abs() < 1e-4);
        assert!(gained > 1.0 && gained < desired);

        // Given enough time it settles at the gain that hits the target RMS.
        let settled = Wm::adaptive_gain(gained, rms, 10.0);
        assert!((settled - desired).abs() < 0.01);
    }

    #[test]
    fn adaptive_gain_holds_near_silence_and_is_bounded() {
        let held = Wm::adaptive_gain(7.5, config::CLOCK_RMS_GATE / 2.0, 1.0);
        assert!((held - 7.5).abs() < 1e-4);

        let quiet = Wm::adaptive_gain(1.0, 0.0009, 1.0);
        assert!(quiet > 1.0 && quiet <= config::CLOCK_GAIN_MAX);
        let loud = Wm::adaptive_gain(1.0, 1.0, 1.0);
        assert!(loud >= config::CLOCK_GAIN_MIN && loud < 1.0);
    }

    #[test]
    fn adaptive_gain_equalizes_quiet_and_loud_sources() {
        let mut quiet = 1.0;
        let mut loud = 1.0;
        for _ in 0..600 {
            quiet = Wm::adaptive_gain(quiet, 0.01, BAR_TICK.as_secs_f32());
            loud = Wm::adaptive_gain(loud, 0.5, BAR_TICK.as_secs_f32());
        }
        assert!((0.01 * quiet - config::CLOCK_RMS_TARGET).abs() < 0.001);
        assert!((0.5 * loud - config::CLOCK_RMS_TARGET).abs() < 0.001);
    }

    #[test]
    fn clock_extra_maps_dbfs_to_quantized_pixels() {
        assert_eq!(Wm::clock_extra_from_rms(0.0), 0);
        assert_eq!(Wm::clock_extra_from_rms(0.001), 0); // below the meter floor
        assert_eq!(Wm::clock_extra_from_rms(1.0), config::CLOCK_ANIM_EXTRA);

        let target = Wm::clock_extra_from_rms(config::CLOCK_RMS_TARGET);
        assert!(target > 0 && target < config::CLOCK_ANIM_EXTRA);
        assert_eq!(target % config::CLOCK_ANIM_STEP, 0);

        // Expansion must spread quiet and loud levels across the meter rather
        // than keep them bunched near one width.
        let quiet = Wm::clock_extra_from_rms(0.02);
        let loud = Wm::clock_extra_from_rms(0.3);
        assert!(quiet < config::CLOCK_ANIM_EXTRA / 2);
        assert!(loud > quiet + config::CLOCK_ANIM_EXTRA / 2);
    }

    #[test]
    fn clock_follows_the_right_bar_when_the_tray_takes_space() {
        let title_right = 200;
        let cw = 100;
        let right_bar = 1592; // 1920 - outer gap - right bar width
        let plain = centered_bar_x(title_right, right_bar, cw, cw).unwrap();
        assert_eq!(plain + cw / 2, title_right + (right_bar - title_right) / 2);

        // A docked tray pushes the right bar left by its width plus the gap.
        let tray = 60 + BARGAP;
        let with_tray = centered_bar_x(title_right, right_bar - tray, cw, cw).unwrap();
        assert_eq!(
            with_tray + cw / 2,
            title_right + (right_bar - tray - title_right) / 2
        );
        assert_eq!(plain - with_tray, tray / 2);
    }

    #[test]
    fn animated_clock_grows_around_the_same_center() {
        let cw = 100;
        let grown = cw + 60;
        let normal_x = centered_bar_x(200, 1000, cw, cw).unwrap();
        let grown_x = centered_bar_x(200, 1000, cw, grown).unwrap();
        assert_eq!(normal_x + cw / 2, grown_x + grown / 2);
    }

    #[test]
    fn clock_is_hidden_when_the_bar_gap_cannot_hold_its_reserve() {
        let cw = 100;
        assert_eq!(centered_bar_x(200, 200 + cw + 2 * BARGAP - 1, cw, cw), None);
        assert!(centered_bar_x(200, 200 + cw + 2 * BARGAP, cw, cw).is_some());
    }

    #[test]
    fn map_allowed_keeps_every_fullscreen_window_and_floating_overlays() {
        // No fullscreen client: every visible window may map.
        assert!(Wm::map_allowed(1, false, false, None));
        assert!(Wm::map_allowed(2, true, false, None));
        // With a fullscreen stack, all fullscreen clients stay mapped (the
        // newest one is the owner), plus floating overlays. Tiled windows do not.
        assert!(Wm::map_allowed(1, false, true, Some(1)));
        assert!(Wm::map_allowed(2, false, true, Some(1)));
        assert!(Wm::map_allowed(2, true, false, Some(1)));
        assert!(!Wm::map_allowed(2, false, false, Some(1)));
    }

    #[test]
    fn own_unmaps_are_not_mistaken_for_a_client_withdraw() {
        let mut state = MapTracking {
            mapped: true,
            ..Default::default()
        };
        assert!(state.unmap());
        assert!(!state.consume_unmap());
        assert_eq!(state.pending_unmaps, 0);
        // Unmapping an already unmapped client sends no event, so it must not
        // leave a marker that would swallow a later real withdraw.
        assert!(!state.unmap());
        assert_eq!(state.pending_unmaps, 0);
    }

    #[test]
    fn unmap_notify_in_flight_when_we_remap_still_belongs_to_us() {
        let mut state = MapTracking {
            mapped: true,
            ..Default::default()
        };
        assert!(state.unmap());
        state.map(); // a second arrange before the UnmapNotify was read
        assert!(!state.consume_unmap());
        assert!(state.mapped);
        // A genuine withdraw after that is still recognized.
        assert!(state.consume_unmap());
        assert!(!state.mapped);
    }

    #[test]
    fn client_withdraw_is_recognized_and_not_reported_twice() {
        let mut state = MapTracking {
            mapped: true,
            ..Default::default()
        };
        assert!(state.consume_unmap());
        assert!(!state.mapped);
        assert!(!state.consume_unmap());
    }

    #[test]
    fn size_hints_enforce_minimum() {
        let hints = SizeHints {
            min_w: 200,
            min_h: 100,
            base_w: 200,
            base_h: 100,
            ..Default::default()
        };
        let got = constrain_size(&hints, box_(110, 70), 2, 0);
        assert_eq!((got.w, got.h), (204, 104));
        assert_eq!((got.x, got.y), (10, 20));
    }

    #[test]
    fn size_hints_apply_base_and_increment() {
        let hints = SizeHints {
            base_w: 10,
            base_h: 20,
            inc_w: 10,
            inc_h: 10,
            ..Default::default()
        };
        let got = constrain_size(&hints, box_(123, 133), 0, 0);
        assert_eq!((got.w, got.h), (120, 130));
    }

    #[test]
    fn size_hints_enforce_maximum() {
        let hints = SizeHints {
            max_w: 300,
            max_h: 200,
            ..Default::default()
        };
        let got = constrain_size(&hints, box_(500, 500), 0, 0);
        assert_eq!((got.w, got.h), (300, 200));
    }

    #[test]
    fn fixed_size_hints_mean_equal_positive_min_and_max() {
        let fixed = SizeHints {
            min_w: 300,
            min_h: 350,
            max_w: 300,
            max_h: 350,
            ..Default::default()
        };
        assert!(has_fixed_size(&fixed));
        assert!(!has_fixed_size(&SizeHints {
            max_w: 0,
            max_h: 0,
            ..fixed
        }));
        assert!(!has_fixed_size(&SizeHints {
            max_w: 600,
            ..fixed
        }));
        // Zero means "unspecified" in ICCCM, not a fixed size.
        assert!(!has_fixed_size(&SizeHints::default()));
    }

    #[test]
    fn manual_float_toggle_outranks_automatic_policy_updates() {
        // No manual choice: an automatic policy change is applied, a no-op is not.
        assert!(should_apply_float_policy(None, true, false));
        assert!(should_apply_float_policy(None, false, true));
        assert!(!should_apply_float_policy(None, true, true));
        assert!(!should_apply_float_policy(None, false, false));

        // The user pressed Super+W: later WM_NORMAL_HINTS / _NET_WM_STATE
        // notifications must not flip the window back, in either direction.
        assert!(!should_apply_float_policy(Some(true), false, true));
        assert!(!should_apply_float_policy(Some(false), true, false));
    }

    #[test]
    fn fixed_size_normal_window_wants_floating_without_any_app_rule() {
        let fixed = SizeHints {
            min_w: 300,
            min_h: 350,
            max_w: 300,
            max_h: 350,
            ..Default::default()
        };
        assert!(wants_floating(WinType::Normal, None, false, &fixed));
        // A normal window with only a minimum stays tiled.
        assert!(!wants_floating(
            WinType::Normal,
            None,
            false,
            &SizeHints {
                min_w: 940,
                min_h: 500,
                ..Default::default()
            }
        ));
    }

    #[test]
    fn fixed_size_floating_window_uses_its_hinted_size_and_position() {
        let hints = SizeHints {
            min_w: 300,
            min_h: 350,
            max_w: 300,
            max_h: 350,
            base_w: 300,
            base_h: 350,
            requested_size: Some((300, 350)),
            requested_pos: Some((810, 209)),
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!(
            geom,
            Rect {
                x: 810,
                y: 209,
                w: 304,
                h: 354
            }
        );
    }

    #[test]
    fn drag_geom_keeps_grab_offset_and_size_instead_of_centering_on_pointer() {
        let start = Rect {
            x: 100,
            y: 200,
            w: 1000,
            h: 500,
        };
        let (ox, oy) = (300, 120); // grabbed at (400, 320)

        // First motion without moving the pointer: no jump and no resize.
        assert_eq!(Wm::drag_geom((400, 320), (ox, oy), start), start);
        // Moving the pointer moves the top-left by the same amount, size intact.
        assert_eq!(
            Wm::drag_geom((700, 520), (ox, oy), start),
            Rect {
                x: 400,
                y: 400,
                w: 1000,
                h: 500
            }
        );
    }

    fn work_area() -> Rect {
        Rect {
            x: 0,
            y: 30,
            w: 1920,
            h: 1050,
        }
    }

    #[test]
    fn dialog_centers_in_work_area_below_the_bar() {
        let geom = floating_geometry(&SizeHints::default(), work_area(), None, BORDERPX);
        assert_eq!(
            geom,
            Rect {
                x: 658,
                y: 353,
                w: 604,
                h: 404
            }
        );
    }

    #[test]
    fn dialog_uses_its_own_base_size_instead_of_a_fixed_600x400() {
        let hints = SizeHints {
            min_w: 400,
            min_h: 300,
            base_w: 400,
            base_h: 300,
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.w, geom.h), (404, 304));
        assert_eq!((geom.x, geom.y), (758, 403));
    }

    #[test]
    fn requested_position_and_gravity_are_honored_and_clamped() {
        let hints = SizeHints {
            min_w: 400,
            min_h: 300,
            base_w: 400,
            base_h: 300,
            requested_pos: Some((1800, 100)),
            gravity: Some(Gravity::NORTH_EAST),
            ..Default::default()
        };
        // NorthEastGravity means x points at the right edge of the window.
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (1396, 100));

        let offscreen = SizeHints {
            requested_pos: Some((-100, -100)),
            requested_size: Some((800, 600)),
            user_position: true, // a user choice is clamped, a program one centers
            ..Default::default()
        };
        let geom = floating_geometry(&offscreen, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (0, 30));
    }

    #[test]
    fn placeholder_program_position_does_not_defeat_centering() {
        let hints = SizeHints {
            requested_pos: Some((0, 0)),
            user_position: false,
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (658, 353));

        let explicit = SizeHints {
            user_position: true,
            ..hints
        };
        let geom = floating_geometry(&explicit, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (0, 30));
    }

    #[test]
    fn program_position_from_another_monitor_centers_on_the_assigned_monitor() {
        // HDMI-1 starts at y=768. The updater asked for 810,209, which is the
        // center of eDP-1 at 277x0; it must not be clamped to HDMI's top edge.
        let area = Rect {
            x: 0,
            y: 812,
            w: 1920,
            h: 1036,
        };
        let hints = SizeHints {
            min_w: 300,
            min_h: 350,
            max_w: 300,
            max_h: 350,
            base_w: 300,
            base_h: 350,
            requested_size: Some((300, 350)),
            requested_pos: Some((810, 209)),
            ..Default::default()
        };
        let geom = floating_geometry(&hints, area, None, BORDERPX);
        assert_eq!(
            geom,
            Rect {
                x: 808,
                y: 1153,
                w: 304,
                h: 354
            }
        );
    }

    #[test]
    fn program_position_on_the_assigned_monitor_is_still_honored() {
        let hints = SizeHints {
            requested_pos: Some((400, 400)),
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (400, 400));
    }

    #[test]
    fn user_position_outside_the_work_area_is_honored_and_clamped() {
        let hints = SizeHints {
            requested_pos: Some((810, 10)),
            user_position: true,
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.x, geom.y), (810, 30));
    }

    #[test]
    fn transient_dialog_centers_on_its_parent() {
        let parent = Rect {
            x: 200,
            y: 100,
            w: 1000,
            h: 800,
        };
        let geom = floating_geometry(&SizeHints::default(), work_area(), Some(parent), BORDERPX);
        assert_eq!((geom.x, geom.y), (398, 298));
    }

    #[test]
    fn requested_size_is_rounded_to_the_size_increment() {
        let hints = SizeHints {
            base_w: 100,
            base_h: 100,
            inc_w: 50,
            inc_h: 50,
            requested_size: Some((230, 230)),
            ..Default::default()
        };
        let geom = floating_geometry(&hints, work_area(), None, BORDERPX);
        assert_eq!((geom.w, geom.h), (204, 204));
    }

    #[test]
    fn nearest_tile_picks_closest_box_in_a_gap() {
        let leaves = [
            (
                1,
                Rect {
                    x: 0,
                    y: 0,
                    w: 400,
                    h: 500,
                },
            ),
            (
                2,
                Rect {
                    x: 420,
                    y: 0,
                    w: 400,
                    h: 500,
                },
            ),
        ];
        assert_eq!(
            Wm::nearest_tile(&leaves, (410, 250)).map(|(w, _)| *w),
            Some(1)
        );
        assert_eq!(
            Wm::nearest_tile(&leaves, (425, 250)).map(|(w, _)| *w),
            Some(2)
        );
    }
}

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::mpsc::Receiver;
use std::thread;
use std::time::{Duration, Instant};

use x11rb::connection::Connection;
use x11rb::properties::WmSizeHints;
use x11rb::protocol::xproto::{
    AtomEnum, ButtonIndex, ChangeWindowAttributesAux, ClientMessageEvent, ColormapAlloc,
    ConfigWindow, ConfigureNotifyEvent, ConfigureWindowAux, ConnectionExt, CreateWindowAux,
    EventMask, Gravity, GrabMode, GrabStatus, InputFocus, KeyPressEvent, ModMask, PropMode,
    StackMode, Window, WindowClass, CONFIGURE_NOTIFY_EVENT,
};
use x11rb::protocol::xkb::{self, ConnectionExt as _};
use x11rb::protocol::Event;
use x11rb::rust_connection::RustConnection;
use x11rb::wrapper::ConnectionExt as _;
use x11rb::{CURRENT_TIME, NONE};

use crate::bar::{
    BAR_BACKGROUND_PIXEL, BARGAP, CLOCKPAD, CursorLoader, HORIZPADBAR, KBLAYOUTPAD, LAUNCHERS,
    LAYOUT_SYMBOL, Metrics, TAG_LABEL, TAGS,
};
use crate::drw::Drw;
use crate::config::{self, BORDERPX, FLOATBAR, TOPBAR};
use crate::keys::{self, Action, GapScope, Key, MOD_4, TAGMASK, TAG_COUNT};
use crate::tree::{self, Gaps, Node, Rect};

pub type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

const LOCK_MASK: u16 = 1 << 1;
const MOD2_MASK: u16 = 1 << 4;
/// dwm's CLEANMASK: every modifier except CapsLock and NumLock (Mod2 here).
const CLEAN_MASK: u16 = 0xFD & !MOD2_MASK;
/// Pointer motion throttle during a drag, matching dwm's `1000 / 60`.
const DRAG_FRAME: Duration = Duration::from_millis(16);
/// The one cadence for every animated bar value. Clock peaks and scrolling
/// titles advance on this same grid, so redraws never come from two timers
/// with different phases.
const BAR_TICK: Duration = Duration::from_millis(20);
/// Slow fallback for wakeups that only background threads can cause (PipeWire
/// peaks and MPRIS snapshots). Used when no bar animation is active.
const IDLE_POLL: Duration = Duration::from_millis(500);
/// Scrolling title moves one pixel every two bar ticks (40 ms). A separate
/// 33 ms timer used to fire between ticks and produced uneven redraw gaps.
const SCROLL_TICKS: u32 = 2;
/// Peak sampling stays on `BAR_TICK`, but the clock window is only resized at
/// this rate. Each resize damages the compositor's frame, so limiting it cuts
/// the GPU work without making the animation noticeably choppy.
const CLOCK_RESIZE_TICK: Duration = Duration::from_millis(40);
/// Don't repaint the MPRIS panel until the interpolated progress bar would
/// move by about a pixel. This replaces the old once-per-second Position poll.
const PROGRESS_EPSILON: f32 = 0.005;

/// The parts of `WM_NORMAL_HINTS` dwm's `updatesizehints()` keeps. Zero means
/// "not specified", as in the C version. Sizes are client sizes, without the
/// border, because that is what `applysizehints()` operates on.
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

pub struct Client {
    pub win: Window,
    pub tags: u32,
    pub mon: usize,
    /// dwm's `isfloating`: a floating window is outside the tiling tree.
    pub floating: bool,
    /// Temporarily outside the tiling tree while Super+drag moves it. Its tree
    /// leaf stays in place, so siblings expand until the drop reinserts it.
    dragging: bool,
    /// The outer box of a floating window, like dwm's `x`, `y`, `w` and `h`.
    pub geom: Rect,
    /// dwm's `minw`, `basew`, `incw`, aspect and friends from `WM_NORMAL_HINTS`.
    hints: SizeHints,
    /// The input-only hover zones over the window's edges and corners, in the
    /// order of `tree::ZONE_EDGES`.
    pub edge_wins: [Window; 8],
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
}

/// dwm's `barwidths()` output.
struct BarWidths {
    tw: i32,
    tlw: i32,
    cw: i32,
    kw: i32,
    rw: i32,
}

struct Atoms {
    wm_protocols: u32,
    wm_delete: u32,
    net_wm_name: u32,
    utf8_string: u32,
    net_current_desktop: u32,
    net_number_of_desktops: u32,
    no_animation: u32,
}

pub struct Wm {
    pub conn: RustConnection,
    pub root: Window,
    pub monitors: Vec<Monitor>,
    /// Newest first, like dwm's client list. Its order is the focus and move order.
    pub clients: Vec<Client>,
    pub selmon: usize,
    keys: Vec<Key>,
    keysyms: Vec<u32>,
    min_keycode: u8,
    atoms: Atoms,
    /// Text measuring for the layout, on the same Xlib display as `drw`.
    metrics: Metrics,
    /// Xlib/Xft/XRender drawing, like C dwm's `drw`.
    drw: Drw,
    /// Last clock window state, so animation only repaints when it changes.
    clock_drawn: RefCell<HashMap<Window, (i32, i32, i32, String, bool)>>,
    visual_id: u32,
    depth: u8,
    clock: String,
    /// Shared PipeWire peak for the animated clock width. It is sampled in the
    /// main loop instead of a separate fixed-cadence thread, so there is no
    /// second 50 Hz wakeup just to publish one atomic.
    clock_peak: Option<crate::sound::Peak>,
    /// Last time the peak was sampled, on the shared `BAR_TICK` grid.
    clock_anim_last: Instant,
    /// Last time the clock window was actually resized.
    clock_resize_last: Instant,
    /// dwm's `clockbar_dynw` minus `clockbar_cw`: px the clock bar grows past
    /// its text width on the selected monitor.
    clock_extra: i32,
    /// Typed top-right bar values and `kbstr` (keyboard layout).
    bar_status: crate::status::Status,
    kbstr: String,
    /// Set by an event that may change what the bar shows. Window motion and
    /// client configure events deliberately do not set it.
    bar_dirty: bool,
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
    /// Keeps the Xlib connection that owns the themed cursor ids alive.
    _cursor_loader: CursorLoader,
    pub restart: bool,
}

pub fn spawn(cmd: &str) -> Result {
    let mut child = Command::new("sh");
    child.arg("-c").arg(cmd);
    unsafe {
        child.pre_exec(|| {
            libc::signal(libc::SIGCHLD, libc::SIG_DFL);
            Ok(())
        });
    }
    let mut child = child.spawn()?;
    thread::spawn(move || {
        let _ = child.wait();
    });
    Ok(())
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
                    | EventMask::PROPERTY_CHANGE,
            ),
        )?
        .check()?;

        let intern = |name: &[u8]| -> Result<u32> {
            Ok(conn.intern_atom(false, name)?.reply()?.atom)
        };
        let atoms = Atoms {
            wm_protocols: intern(b"WM_PROTOCOLS")?,
            wm_delete: intern(b"WM_DELETE_WINDOW")?,
            net_wm_name: intern(b"_NET_WM_NAME")?,
            utf8_string: intern(b"UTF8_STRING")?,
            net_current_desktop: intern(b"_NET_CURRENT_DESKTOP")?,
            net_number_of_desktops: intern(b"_NET_NUMBER_OF_DESKTOPS")?,
            no_animation: intern(b"_NO_ANIMATION")?,
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
        let mut status = crate::status::StatusSampler::new();
        let bar_status = status.sample_with_mpris(Some(&mpris));
        let cursor_loader = CursorLoader::open()?;
        let resize_cursors = create_resize_cursors(&cursor_loader);
        conn.change_window_attributes(
            root,
            &ChangeWindowAttributesAux::new().cursor(cursor_loader.load("left_ptr")),
        )?;
        // Fonts, cursors and every bar pixel use this one Xlib connection, the
        // same way C dwm shares a single `Display *dpy` for all drawing.
        let dpy = cursor_loader.display();
        let screen = cursor_loader.screen();
        let metrics = Metrics::new(dpy, screen)?;
        let drw = Drw::new(dpy, screen, root as x11::xlib::Window)?;
        let clock_peak = if config::CLOCK_ANIMATE {
            Some(crate::sound::start())
        } else {
            None
        };
        let monitor_count = monitors.len();
        let mut wm = Wm {
            conn,
            root,
            monitors,
            clients: Vec::new(),
            selmon: 0,
            keys,
            keysyms,
            min_keycode,
            atoms,
            metrics,
            drw,
            clock_drawn: RefCell::new(HashMap::new()),
            visual_id,
            depth,
            clock: now_clock(),
            clock_peak,
            clock_anim_last: Instant::now() - BAR_TICK,
            clock_resize_last: Instant::now(),
            clock_extra: 0,
            bar_status,
            kbstr: "us".to_string(),
            bar_dirty: true,
            force_windows: RefCell::new(HashSet::new()),
            bar_mapped: RefCell::new(HashSet::new()),
            bar_drawn: RefCell::new(HashMap::new()),
            center_shown: RefCell::new(vec![false; monitor_count]),
            name_cache: RefCell::new(HashMap::new()),
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
            _cursor_loader: cursor_loader,
            restart: false,
        };
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
        wm.conn.flush()?;
        Ok(wm)
    }

    /// dwm's setup block: select Xkb StateNotify and read the layout once.
    fn init_xkb(&mut self) {
        let (present, first_event) = self
            .conn
            .query_extension(b"XKB")
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|r| (r.present, r.first_event))
            .unwrap_or((false, 0));
        if !present {
            return;
        }
        let aux = xkb::SelectEventsAux::new().state_notify(xkb::SelectEventsAuxStateNotify {
            affect_state: xkb::StatePart::default(),
            state_details: xkb::StatePart::default(),
        });
        let selected = self
            .conn
            .xkb_select_events(
                xkb::ID::USE_CORE_KBD.into(),
                xkb::EventType::default(),
                xkb::EventType::STATE_NOTIFY,
                xkb::MapPart::default(),
                xkb::MapPart::default(),
                &aux,
            )
            .is_ok();
        if selected {
            self.xkb_event_base = first_event;
        }
        self.update_kb();
    }

    /// dwm's `getkblayout()`: pick the layout of the current XKB group out of
    /// the `_XKB_RULES_NAMES` property.
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

    fn grab_buttons(&self, win: Window) -> Result {
        self.conn.ungrab_button(ButtonIndex::ANY, win, ModMask::ANY)?;
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

    fn is_visible(&self, c: &Client) -> bool {
        c.tags & self.tags_of(c.mon) != 0
    }

    /// Visible windows on `mi` in stack order, like dwm's `ISVISIBLE` walk.
    fn stack_order(&self, mi: usize) -> Vec<Window> {
        self.clients
            .iter()
            .filter(|c| c.mon == mi && self.is_visible(c))
            .map(|c| c.win)
            .collect()
    }

    fn is_managed(&self, win: Window) -> bool {
        self.clients.iter().any(|c| c.win == win)
    }

    fn bar_h(&self) -> i32 {
        self.metrics.bar_height()
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
        })
    }

    /// The monitor's area below the bar, set by `update_bar_pos`.
    fn work(&self, mi: usize) -> Rect {
        let m = &self.monitors[mi];
        Rect { x: m.wx, y: m.wy, w: m.ww as u32, h: m.wh as u32 }
    }

    /// The visible tiled windows on `mi` in stack order.
    fn tiled_order(&self, mi: usize) -> Vec<Window> {
        self.clients
            .iter()
            .filter(|c| c.mon == mi && !c.floating && !c.dragging && self.is_visible(c))
            .map(|c| c.win)
            .collect()
    }

    /// The outer box `win` is drawn in: its floating geometry or its tile.
    fn geometry(&self, mi: usize, win: Window) -> Option<Rect> {
        if let Some(c) = self
            .clients
            .iter()
            .find(|c| c.win == win && (c.floating || c.dragging))
        {
            return Some(c.geom);
        }
        self.layout_mon(mi).into_iter().find(|(w, _)| *w == win).map(|(_, r)| r)
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
                m.by = if TOPBAR { m.wy + m.gaps.oh } else { m.wy + m.wh };
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

    /// dwm's `updatebars()`: creates the five bar windows of each monitor.
    fn update_bars(&mut self) -> Result {
        let bh = self.bar_h() as u16;
        let root_colormap = self.conn.get_window_attributes(self.root)?.reply()?.colormap;
        let marker_pixel = self
            .conn
            .alloc_color(root_colormap, 0xB8B8, 0xE9E9, 0xB4B4)?
            .reply()?
            .pixel;
        for mi in 0..self.monitors.len() {
            let r = self.monitors[mi].rect;
            let cmap = self.conn.generate_id()?;
            self.conn
                .create_colormap(ColormapAlloc::NONE, cmap, self.root, self.visual_id)?;
            let mut wins = [0 as Window; 5];
            for win in wins.iter_mut() {
                *win = self.conn.generate_id()?;
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
                        &CreateWindowAux::new()
                            .background_pixel(BAR_BACKGROUND_PIXEL)
                            .border_pixel(0)
                            .bit_gravity(Gravity::NORTH_WEST)
                            .colormap(cmap)
                            .override_redirect(1)
                            .event_mask(
                                EventMask::EXPOSURE
                                    | EventMask::ENTER_WINDOW
                                    | EventMask::LEAVE_WINDOW
                                    | EventMask::BUTTON_PRESS
                                    | EventMask::BUTTON_RELEASE
                                    | EventMask::POINTER_MOTION,
                            ),
                    )?
                    .check()?;
                self.conn.map_window(*win)?;
                self.bar_mapped.borrow_mut().insert(*win);
            }
            let m = &mut self.monitors[mi];
            [m.barwin, m.bartitlewin, m.barkbwin, m.barcenterwin, m.barrightwin] = wins;

            m.mpris_markerwin = self.conn.generate_id()?;
            self.conn.create_window(
                0,
                m.mpris_markerwin,
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
                    m.mpris_markerwin,
                    AtomEnum::WM_NAME,
                    AtomEnum::STRING,
                    b"dwm-mpris-volume-marker",
                )?
                .check()?;
            self.conn
                .change_property8(
                    PropMode::REPLACE,
                    m.mpris_markerwin,
                    AtomEnum::WM_CLASS,
                    AtomEnum::STRING,
                    b"dwm-mpris-volume-marker\0dwm-mpris-volume-marker\0",
                )?
                .check()?;
        }
        Ok(())
    }

    fn tagsbarwidth(&self) -> i32 {
        let w: i32 = (0..TAGS).map(|_| self.metrics.textw(TAG_LABEL)).sum();
        BORDERPX + w + self.metrics.textw(LAYOUT_SYMBOL)
    }

    /// dwm's `bartitlewidth()`: launchers plus the selected client's name,
    /// limited to `budget`.
    fn bartitlewidth(&self, mi: usize, budget: i32) -> i32 {
        let mut w: i32 = LAUNCHERS.iter().map(|name| self.metrics.textw(name)).sum();
        if let Some(sel) = self.monitors[mi].sel {
            w += self.metrics.textw(&self.client_name(sel));
        }
        w.min(budget)
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
        let cw = self.metrics.text_width(&self.clock) + 2 * CLOCKPAD;
        let kw = self.metrics.text_width(&self.kbstr) + 2 * KBLAYOUTPAD;
        let tw = self.tagsbarwidth();
        let used = tw + rw + cw + kw + 4 * BARGAP;
        let avail = if barw > used { barw - used } else { 0 };
        let budget = if avail > BORDERPX { avail - BORDERPX } else { 0 };
        let mut tlw = BORDERPX + self.bartitlewidth(mi, budget);
        if tlw > avail {
            tlw = avail;
        }
        BarWidths { tw, tlw, cw, kw, rw }
    }

    /// Width of the center clock window: dwm's `dcw`. Only the selected monitor
    /// grows, and the layout keeps the fixed `cw`.
    fn clock_window_width(&self, mi: usize, cw: i32) -> i32 {
        if mi == self.selmon {
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
        let rx = lx + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw;
        let kx = lx + b.tw + BARGAP;
        let titlex = kx + b.kw + BARGAP;
        let title_right = titlex + b.tlw;
        let span = rx - title_right;
        let cw = b.cw;
        if span < cw + 2 * BARGAP {
            return None;
        }
        let mut cx = title_right + (span - cw - 2 * BARGAP) / 2;
        let mut clock_cx = cx + (cw + 2 * BARGAP) / 2;
        let monitor_center = m.wx + m.ww / 2;
        if clock_cx < monitor_center {
            clock_cx = monitor_center;
            cx = clock_cx - (cw + 2 * BARGAP) / 2;
        }
        let dcw = self.clock_window_width(mi, cw);
        Some((cx + (cw + 2 * BARGAP) / 2 - dcw / 2, dcw))
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
    fn send_configure(&self, win: Window, rect: Rect, inner_w: u32, inner_h: u32) -> Result {
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
            border_width: BORDERPX as u16,
            override_redirect: false,
        };
        self.conn.send_event(false, win, EventMask::STRUCTURE_NOTIFY, event)?;
        Ok(())
    }

    /// Configures one client and sends dwm's synthetic `ConfigureNotify` only
    /// when the geometry changed. Returns the geometry actually applied, after
    /// `WM_NORMAL_HINTS` for floating clients, and whether it changed.
    fn place_client(&self, c: &Client, rect: Rect) -> Result<(Rect, bool)> {
        let rect = if c.floating {
            constrain_size(&c.hints, rect, BORDERPX, self.bar_h())
        } else {
            rect
        };
        let inner_w = (rect.w as i32 - 2 * BORDERPX).max(1) as u32;
        let inner_h = (rect.h as i32 - 2 * BORDERPX).max(1) as u32;
        let changed = self.configure_cached(
            c.win,
            rect.x,
            rect.y,
            inner_w as i32,
            inner_h as i32,
            BORDERPX as u32,
        )?;
        if changed {
            self.send_configure(c.win, rect, inner_w, inner_h)?;
        }
        Ok((rect, changed))
    }

    /// dwm's `resizebarwin()`, without the systray, Finder, notification and
    /// MPRIS sections. The clock window is placed by the clock thread.
    fn resize_bar_win(&self, mi: usize) -> Result {
        let m = &self.monitors[mi];
        let bh = self.bar_h();
        if !m.showbar {
            for win in [m.barwin, m.bartitlewin, m.barcenterwin, m.barkbwin, m.barrightwin] {
                self.place_cached(win, m.wx, m.by, 1, bh)?;
            }
            self.set_mapped(m.mpris_markerwin, false)?;
            self.center_shown.borrow_mut()[mi] = false;
            return Ok(());
        }

        let b = self.barwidths(mi);
        let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
        let rx = lx + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw;

        self.place_cached(m.barwin, lx, m.by, b.tw, bh)?;

        let kx = lx + b.tw + BARGAP;
        self.place_cached(m.barkbwin, kx, m.by, b.kw, bh)?;
        self.set_mapped(m.barkbwin, true)?;

        let titlex = kx + b.kw + BARGAP;
        self.place_cached(m.bartitlewin, titlex, m.by, b.tlw, bh)?;
        self.set_mapped(m.bartitlewin, true)?;

        let show_clock = self.clock_place(mi).is_some();
        self.set_mapped(m.barcenterwin, show_clock)?;
        let was_shown = self.center_shown.borrow()[mi];
        if was_shown != show_clock {
            self.center_shown.borrow_mut()[mi] = show_clock;
            // A remapped clock window needs an explicit repaint even when its
            // text and size match the last draw.
            if show_clock {
                self.force_windows.borrow_mut().insert(m.barcenterwin);
            }
        }

        let right_h = if self.mpris_hovered && mi == self.selmon && self.mpris.present {
            bh * 2
        } else {
            bh
        };
        self.place_cached(m.barrightwin, rx, m.by, b.rw, right_h)?;
        self.set_mapped(m.barrightwin, true)?;
        Ok(())
    }

    /// Raise or lower the top-right bar and its volume marker relative to
    /// client windows. On hover the panel grows to two rows and can overlap a
    /// floating client, so while expanded it must sit on top of every window;
    /// otherwise the extra row is hidden and its controls cannot be clicked.
    /// With no sibling, `ABOVE`/`BELOW` are exactly the requests XRaiseWindow
    /// and XLowerWindow send: top and bottom of the root's stacking order.
    fn stack_mpris_bar(&self, mi: usize, above: bool) -> Result {
        let m = &self.monitors[mi];
        let aux = ConfigureWindowAux::new()
            .stack_mode(if above { StackMode::ABOVE } else { StackMode::BELOW });
        if above {
            // Raise the panel first so the marker ends up on top of it.
            self.conn.configure_window(m.barrightwin, &aux)?;
            self.conn.configure_window(m.mpris_markerwin, &aux)?;
        } else {
            // Unwind in the opposite order when the panel collapses.
            self.conn.configure_window(m.mpris_markerwin, &aux)?;
            self.conn.configure_window(m.barrightwin, &aux)?;
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

    /// dwm's `focus()`: gives the selected window of the selected monitor the
    /// focus border colour and every other window the normal one.
    fn focus(&self) -> Result {
        let sel = self.monitors[self.selmon].sel;
        for c in &self.clients {
            let pixel = if Some(c.win) == sel {
                config::COL_SEL_BORDER
            } else {
                config::COL_NORM_BORDER
            };
            self.conn
                .change_window_attributes(c.win, &ChangeWindowAttributesAux::new().border_pixel(pixel))?;
        }
        let target = sel.unwrap_or(self.root);
        self.conn
            .set_input_focus(InputFocus::POINTER_ROOT, target, CURRENT_TIME)?;
        self.conn.flush()?;
        Ok(())
    }

    fn apply_layout(&mut self) -> Result {
        let mut boxes: Vec<(Window, Rect, bool)> = Vec::new();
        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
            for (win, r) in self.layout_mon(mi) {
                let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
                    continue;
                };
                let (rect, changed) = self.place_client(&self.clients[idx], r)?;
                self.clients[idx].geom = rect;
                boxes.push((win, rect, changed));
            }
        }
        // Oldest first, so the newest floating window ends up on top.
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
            self.conn.configure_window(
                self.clients[idx].win,
                &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
            )?;
            boxes.push((self.clients[idx].win, rect, changed));
        }
        // A tiled client being moved is visible, but its leaf is hidden from
        // layout_mon() so its siblings take the whole workspace. Keep its
        // zones at the last dragged position without reconfiguring the client.
        for c in self.clients.iter().filter(|c| c.dragging && self.is_visible(c)) {
            boxes.push((c.win, c.geom, false));
        }
        let shown: HashSet<Window> = self
            .clients
            .iter()
            .filter(|c| self.is_visible(c))
            .map(|c| c.win)
            .collect();
        for c in &self.clients {
            if shown.contains(&c.win) {
                self.conn.map_window(c.win)?;
            } else {
                // Drop the cached geometry while hidden. A client may change its
                // own size on UnmapNotify, and the next arrange must configure
                // it again when its tag becomes visible.
                self.geom_cache.borrow_mut().remove(&c.win);
                self.conn.unmap_window(c.win)?;
            }
        }
        for idx in 0..self.clients.len() {
            let win = self.clients[idx].win;
            match boxes.iter().find(|(w, _, _)| *w == win) {
                Some((_, r, changed)) => {
                    let zones = self.clients[idx].edge_wins;
                    // Floating clients are restacked above on every layout, so
                    // their zones need to follow even when the box is unchanged.
                    let restack = *changed || self.clients[idx].floating || self.clients[idx].dragging;
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
        self.conn.flush()?;
        Ok(())
    }

    /// Puts the hover zones of `win` over its outer box `r`, each directly above
    /// the window so that other windows still stack over it correctly.
    fn place_edge_zones(
        &self,
        zones: [Window; 8],
        win: Window,
        r: Rect,
        restack: bool,
    ) -> Result {
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
            .filter(|c| c.mon == mi && !c.floating && self.is_visible(c))
            .map(|c| c.win)
            .collect();
        let area = self.tile_area(mi);
        for win in visible {
            let has_leaf = self.monitors[mi].tree.as_ref().is_some_and(|t| t.has_leaf(win));
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
        self.focus()
    }

    fn manage(&mut self, win: Window) -> Result {
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        let (mx, my) = (pointer.root_x as i32, pointer.root_y as i32);
        let mi = self.monitor_at(mx, my);

        let leaves = self.layout_mon(mi);
        let work = self.tile_area(mi);
        let target = leaves
            .iter()
            .copied()
            .find(|(_, r)| r.contains(mx, my))
            .or(leaves.last().copied());
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

        let tags = self.tags_of(mi);
        let geom = Rect { x: 0, y: 0, w: 0, h: 0 };
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
        let hints = self.read_size_hints(win).unwrap_or_default();
        self.clients.insert(
            0,
            Client {
                win,
                tags,
                mon: mi,
                floating: false,
                dragging: false,
                geom,
                hints,
                edge_wins,
            },
        );
        self.selmon = mi;
        self.monitors[mi].sel = Some(win);
        self.conn.change_window_attributes(
            win,
            &ChangeWindowAttributesAux::new().event_mask(EventMask::ENTER_WINDOW | EventMask::PROPERTY_CHANGE),
        )?;
        self.grab_buttons(win)?;
        self.arrange()
    }

    fn unmanage(&mut self, win: Window) -> Result {
        let Some(idx) = self.clients.iter().position(|c| c.win == win) else {
            return Ok(());
        };
        let client = self.clients.remove(idx);
        self.name_cache.borrow_mut().remove(&win);
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
            .get_property(false, win, self.atoms.net_wm_name, self.atoms.utf8_string, 0, 256)
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

    /// Redraws every shown bar. Returns true when the clock text changed.
    pub fn update_clock(&mut self) -> bool {
        let now = now_clock();
        if now == self.clock {
            return false;
        }
        self.clock = now;
        true
    }

    /// Current peak-derived width in pixels, without changing any state.
    fn pending_clock_extra(&self) -> i32 {
        let Some(peak) = self.clock_peak.as_ref() else {
            return 0;
        };
        let level = crate::sound::read(peak);
        if level < config::CLOCK_PEAK_EPSILON {
            return 0;
        }
        let step = config::CLOCK_ANIM_STEP.max(1);
        let raw = (level * config::CLOCK_ANIM_EXTRA as f32) as i32;
        ((raw / step) * step).clamp(0, config::CLOCK_ANIM_EXTRA)
    }

    /// Samples the PipeWire peak on the shared `BAR_TICK` grid. Returns true
    /// when the quantized width changed.
    pub fn update_clock_anim(&mut self) -> bool {
        if self.clock_peak.is_none() {
            return false;
        }
        let now = Instant::now();
        if now.duration_since(self.clock_anim_last) < BAR_TICK {
            return false;
        }
        self.clock_anim_last = now;

        let extra = self.pending_clock_extra();
        if extra == self.clock_extra
            || now.duration_since(self.clock_resize_last) < CLOCK_RESIZE_TICK
        {
            return false;
        }
        self.clock_extra = extra;
        self.clock_resize_last = now;
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

    /// Deadline for the next bar tick. The main loop blocks on the X connection
    /// until this instant or an event, making this the only wakeup source.
    pub fn next_tick(&self) -> Instant {
        let mut next = self.status.next_sample();
        if self.pending_clock_extra() != self.clock_extra {
            next = next.min(self.clock_resize_last + CLOCK_RESIZE_TICK);
        }
        if self.scroll_active() {
            next = next.min(self.mpris_scroll_next);
        }
        next.min(Instant::now() + IDLE_POLL)
    }

    /// Recomputes and updates the positions and widths of all bar windows.
    pub fn update_bars_geometry(&self) -> Result {
        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
        }
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
        self.drw.map(win as x11::xlib::Window, dw, dh);
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
            let focused = mi == self.selmon;
            let b = self.barwidths(mi);
            let (barwin, titlewin, kbwin, rightwin, marker_win) =
                (m.barwin, m.bartitlewin, m.barkbwin, m.barrightwin, m.mpris_markerwin);
            let selected = self.tags_of(mi);
            let kbstr = self.kbstr.clone();
            let status = self.bar_status.clone();
            let player = self.mpris.clone();
            let (scroll, progress, marker_hovered) =
                (self.mpris_scroll_px, self.mpris.current_progress(), self.mpris_marker_hovered);

            let tw = b.tw.max(1) as u32;
            let tag_key = format!("tags:{tw}:{occupied}:{selected}");
            if self.section_changed(barwin, &tag_key) {
                self.drw.resize(tw, bh as u32);
                self.drw.tags(&self.metrics, tw as i32, occupied, selected);
                self.drw.map(barwin as x11::xlib::Window, tw, bh as u32);
                self.bar_drawn.borrow_mut().insert(barwin, tag_key);
            }

            let tlw = b.tlw.max(1) as u32;
            let title_key = format!("title:{tlw}:{title:?}:{focused}");
            if self.section_changed(titlewin, &title_key) {
                self.drw.resize(tlw, bh as u32);
                self.drw.title(&self.metrics, tlw as i32, title.as_deref(), focused);
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
                let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
                let rx = lx + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw;
                let x = rx + marker_x;
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
                let right_key = format!("status:{rw}:{bh}:{}:{scroll}:{progress_key:?}", status.key());
                if self.section_changed(rightwin, &right_key) {
                    self.drw.resize(rw, bh as u32);
                    if let Some(custom) = &status.custom {
                        self.drw.status(&self.metrics, rw as i32, custom, scroll, progress);
                    } else {
                        self.drw.status_runs(&self.metrics, rw as i32, &status, scroll, progress);
                    }
                    self.drw.map(rightwin as x11::xlib::Window, rw, bh as u32);
                    self.bar_drawn.borrow_mut().insert(rightwin, right_key);
                }
            }
            self.draw_clock(mi)?;
        }
        self.conn.flush()?;
        self.force_windows.borrow_mut().clear();
        Ok(())
    }

    /// One pass of the bar's per-tick work: applies state changes, then
    /// redraws the bars only when their contents or layout changed. Window
    /// motion and client configure events do not get here.
    pub fn refresh(&mut self) -> Result {
        let mut bars = std::mem::take(&mut self.bar_dirty);
        if self.update_mpris() {
            bars = true;
        }
        if self.update_clock() {
            // The clock text can change the width budget, which moves and
            // resizes the other bar sections too.
            bars = true;
        }
        let clock_anim = self.update_clock_anim();
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
        } else if clock_anim {
            // Only the center window's width changed: redraw just the clocks.
            for mi in 0..self.monitors.len() {
                if self.monitors[mi].showbar {
                    self.draw_clock(mi)?;
                }
            }
            self.conn.flush()?;
        }
        Ok(())
    }

    fn rightbar_x(&self, mi: usize) -> i32 {
        let m = &self.monitors[mi];
        let b = self.barwidths(mi);
        let left = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
        left + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw
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
            * if self.mpris_hovered && self.mpris.present && mi == self.selmon { 2 } else { 1 };
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

    pub fn handle(&mut self, event: Event) -> Result {
        match event {
            Event::MapRequest(e) => {
                if !self.is_managed(e.window) {
                    self.manage(e.window)?;
                }
                self.bar_dirty = true;
            }
            // Hidden clients are unmapped by apply_layout, so UnmapNotify is
            // not a sign that a client went away. DestroyNotify handles that.
            Event::UnmapNotify(_) => {}
            Event::DestroyNotify(e) => {
                self.unmanage(e.window)?;
                self.bar_dirty = true;
            }
            Event::ConfigureRequest(e) => {
                if let Some((idx, mi, floating)) = self.clients.iter().enumerate().find_map(
                    |(i, c)| {
                        (c.win == e.window).then_some((i, c.mon, c.floating))
                    },
                ) {
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
                        self.clients[idx].geom = rect;
                        self.place_floating(e.window)?;
                    } else if let Some(rect) = self.geometry(mi, e.window) {
                        // A tiled client cannot resize itself. Tell it the
                        // geometry dwm chose instead of relaying the request.
                        let inner_w = (rect.w as i32 - 2 * BORDERPX).max(1) as u32;
                        let inner_h = (rect.h as i32 - 2 * BORDERPX).max(1) as u32;
                        self.send_configure(e.window, rect, inner_w, inner_h)?;
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
                    if mask & u16::from(ConfigWindow::STACK_MODE) != 0 {
                        aux = aux.stack_mode(e.stack_mode);
                    }
                    self.conn.configure_window(e.window, &aux)?;
                    self.conn.flush()?;
                }
            }
            Event::EnterNotify(e) => {
                self.bar_dirty = true;
                if let Some(mi) = self.monitors.iter().position(|m| {
                    m.barrightwin == e.event || m.mpris_markerwin == e.event
                }) {
                    if mi == self.selmon && self.mpris.present {
                        if self.monitors[mi].mpris_markerwin == e.event {
                            self.mpris_marker_hovered = true;
                            self.update_mpris_marker_class(mi)?;
                        } else {
                            self.mpris_hovered = true;
                            self.resize_bar_win(mi)?;
                        }
                    }
                    return Ok(());
                }
                let found = self
                    .clients
                    .iter()
                    .find(|c| c.win == e.event && self.is_visible(c))
                    .map(|c| (c.win, c.mon));
                if let Some((win, mon)) = found {
                    self.selmon = mon;
                    self.monitors[mon].sel = Some(win);
                    self.focus()?;
                }
            }
            Event::LeaveNotify(e) => {
                self.bar_dirty = true;
                if let Some(mi) = self.monitors.iter().position(|m| {
                    m.barrightwin == e.event || m.mpris_markerwin == e.event
                }) {
                    let root_x = e.root_x as i32;
                    let root_y = e.root_y as i32;
                    if self.monitors[mi].mpris_markerwin == e.event {
                        self.mpris_marker_hovered = false;
                        self.update_mpris_marker_class(mi)?;
                    }
                    let over_marker = self.mpris_marker_rect.is_some_and(|(x, y, w, h)| {
                        root_x >= x && root_x < x + w && root_y >= y && root_y < y + h
                    });
                    if !self.pointer_over_mpris_bar(mi, root_x, root_y)
                        && !over_marker
                        && !self.mpris_volume_drag
                    {
                        self.mpris_hovered = false;
                        self.mpris_marker_hovered = false;
                        self.resize_bar_win(mi)?;
                    }
                    return Ok(());
                }
            }
            Event::ButtonPress(e) => {
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
                if let Some(mi) = self.monitors.iter().position(|m| {
                    m.barrightwin == e.event || m.mpris_markerwin == e.event
                }) {
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
                if self.monitors.iter().any(|m| {
                    m.barrightwin == e.event || m.mpris_markerwin == e.event
                }) {
                    self.mpris_volume_drag = false;
                    return Ok(());
                }
            }
            Event::MotionNotify(e) => {
                if self.mpris_volume_drag {
                    if let Some(mi) = self.monitors.iter().position(|m| {
                        m.barrightwin == e.event || m.mpris_markerwin == e.event
                    }) {
                        let x = e.root_x as i32 - self.rightbar_x(mi);
                        self.set_mpris_volume_from_x(mi, x);
                        self.bar_dirty = true;
                    }
                }
            }
            Event::KeyPress(e) => {
                self.key_press(e)?;
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
                let Some(idx) = self.clients.iter().position(|c| c.win == e.window) else {
                    return Ok(());
                };
                let hints = self.read_size_hints(e.window).unwrap_or_default();
                self.clients[idx].hints = hints;
                if self.clients[idx].floating && self.is_visible(&self.clients[idx]) {
                    let geom = self.clients[idx].geom;
                    self.clients[idx].geom = geom;
                    self.place_floating(e.window)?;
                }
            }
            Event::Expose(e) => {
                // Like dwm's expose(), only the last event in a batch needs a
                // repaint, and only the window that was actually exposed. A
                // global force here makes every GL section swap during a drag.
                if e.count == 0
                    && self.monitors.iter().any(|m| {
                        [m.barwin, m.bartitlewin, m.barkbwin, m.barcenterwin, m.barrightwin]
                            .contains(&e.window)
                    })
                {
                    self.force_windows.borrow_mut().insert(e.window);
                    self.bar_dirty = true;
                }
            }
            _ => {}
        }
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
            Action::KillClient => self.killclient(),
            Action::ForceKillClient => self.forcekillclient(),
            Action::FocusMon(d) => self.focusmon(d),
            Action::TagMon(d) => self.tagmon(d),
            Action::ToggleBar => self.togglebar(),
            Action::ToggleGaps => self.togglegaps(),
            Action::DefaultGaps => self.defaultgaps(),
            Action::IncrGaps(scope, d) => self.incrgaps(scope, d),
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
                        Event::MotionNotify(e) => {
                            latest = Some((e.root_x as i32, e.root_y as i32))
                        }
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
                // Bar animation uses the same 20 ms grid as the main loop, not
                // the 16 ms pointer gate, so drags cannot run a second clock.
                if last_bar_tick.elapsed() >= BAR_TICK {
                    self.refresh()?;
                    last_bar_tick = Instant::now();
                }
            }
        })();
        let _ = self.conn.ungrab_pointer(CURRENT_TIME);
        let _ = self.set_no_animation(win, false);
        let _ = self.conn.flush();
        result.map(|_| end)
    }

    /// Waits until the X connection has an event or `timeout` expires. The
    /// main loop uses this instead of an unconditional sleep, so an event is
    /// handled as soon as it arrives like C dwm's blocking `XNextEvent`.
    pub fn wait_event(&self, timeout: Duration) -> Result {
        let mut pfd = libc::pollfd {
            fd: self.conn.stream().as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        let ms = timeout.as_millis().min(i32::MAX as u128) as i32;
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
        self.conn.flush()?;
        Ok(())
    }

    /// Geometry while dragging. The grab offset stays under the pointer and
    /// the window keeps its size, exactly like a floating drag.
    fn drag_geom((x, y): (i32, i32), (ox, oy): (i32, i32), current: Rect) -> Rect {
        Rect { x: x - ox, y: y - oy, w: current.w, h: current.h }
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

    /// dwm's `movemouse()` with Hyprland-style dwindle dragging. A floating
    /// window follows the pointer. A tiled window is temporarily taken out of
    /// the tree at its current size, so its siblings expand while it follows
    /// the pointer. On release it is removed
    /// first, then reinserted as an even split into the tile under the pointer
    /// in the expanded layout, the same order `onWindowCreatedTiling` uses.
    fn movemouse(&mut self, win: Window, (px, py): (i32, i32)) -> Result {
        let Some((mi, floating)) = self
            .clients
            .iter()
            .find(|c| c.win == win)
            .map(|c| (c.mon, c.floating))
        else {
            return Ok(());
        };
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
            // Raise once at drag start. apply_layout() only restacks the zones;
            // repeated stack requests per frame delay the client's redraw.
            self.conn.configure_window(
                win,
                &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
            )?;
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
        let Some((dx, dy)) = end else {
            return self.arrange();
        };
        let tm = self.monitor_at(dx, dy);
        if tm != mi {
            self.sendmon(win, tm)?;
            self.selmon = tm;
            self.monitors[tm].sel = Some(win);
        }
        if floating {
            return self.arrange();
        }
        // Remove the dragged window before looking at the layout, just like
        // Hyprland's onWindowRemovedTiling() before onWindowCreatedTiling().
        // Otherwise the target is still in its pre-drag half, whose aspect ratio
        // flips on every drop and makes repeated drops alternate split axes.
        {
            let tree = &mut self.monitors[tm].tree;
            *tree = tree.take().and_then(|t| t.remove(win));
        }
        let leaves: Vec<(Window, Rect)> = self.layout_mon(tm).into_iter().collect();
        let target = leaves
            .iter()
            .copied()
            .find(|(_, r)| r.contains(dx, dy))
            .or_else(|| Self::nearest_tile(&leaves, (dx, dy)).copied());
        match target {
            Some((target, rect)) => {
                let (new_first, side_by_side) = tree::split_for_drop(rect, (dx, dy));
                if let Some(t) = self.monitors[tm].tree.as_mut() {
                    t.insert(target, win, new_first, side_by_side);
                }
            }
            None => {
                // No tile under the pointer: append beside whatever is left of
                // the tree. Replacing it with a single leaf would drop the
                // hidden leaves of other tags and break those tags on return.
                let area = self.tile_area(tm);
                let tree = &mut self.monitors[tm].tree;
                *tree = Some(tree::append(tree.take(), win, area));
            }
        }
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
        let Some((mi, floating)) = self
            .clients
            .iter()
            .find(|c| c.win == win)
            .map(|c| (c.mon, c.floating))
        else {
            return Ok(());
        };
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

    /// dwm's `togglefloating()`: moves the selected window between the tiling
    /// tree and the floating layer without losing its place in the tree.
    fn togglefloating(&mut self) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        let Some(c) = self.clients.iter().find(|c| c.win == sel) else {
            return Ok(());
        };
        if c.floating {
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
                c.floating = false;
            }
            // A floated window keeps its leaf in the tree; tiled_order() hides
            // it while floating, so toggling back restores the old split.
            if !self.monitors[mi].tree.as_ref().is_some_and(|t| t.has_leaf(sel)) {
                let area = self.tile_area(mi);
                let tree = &mut self.monitors[mi].tree;
                *tree = Some(tree::append(tree.take(), sel, area));
            }
        } else {
            let Some(rect) = self.geometry(mi, sel) else {
                return Ok(());
            };
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
                c.floating = true;
                c.geom = rect;
            }
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
        if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
            c.tags = t;
        }
        self.arrange()
    }

    fn toggletag(&mut self, ui: u32) -> Result {
        let Some(sel) = self.monitors[self.selmon].sel else {
            return Ok(());
        };
        let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) else {
            return Ok(());
        };
        let newtags = c.tags ^ (ui & TAGMASK);
        if newtags == 0 {
            return Ok(());
        }
        c.tags = newtags;
        self.arrange()
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
        let order = self.stack_order(mi);
        let (Some(idx), n) = (order.iter().position(|&w| w == sel), order.len()) else {
            return Ok(());
        };
        let next = if d > 0 { (idx + 1) % n } else { (idx + n - 1) % n };
        let c = order[next];
        self.monitors[mi].sel = Some(c);
        self.focus()?;
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
        let target = if d > 0 { (idx + 1) % n } else { (idx + n - 1) % n };
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
            .and_then(|r| r.value32().map(|mut it| it.any(|a| a == self.atoms.wm_delete)))
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
        let t = &mut self.monitors[target];
        t.tree = Some(tree::append(t.tree.take(), win, area));
        self.clients[ci].mon = target;
        self.clients[ci].tags = tags;
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
        self.setgaps(config::GAPPOH, config::GAPPOV, config::GAPPIH, config::GAPPIV)
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
}

#[cfg(test)]
mod tests {
    use super::*;

    fn box_(w: u32, h: u32) -> Rect {
        Rect { x: 10, y: 20, w, h }
    }

    #[test]
    fn size_hints_enforce_minimum() {
        let hints = SizeHints { min_w: 200, min_h: 100, base_w: 200, base_h: 100, ..Default::default() };
        let got = constrain_size(&hints, box_(110, 70), 2, 0);
        assert_eq!((got.w, got.h), (204, 104));
        assert_eq!((got.x, got.y), (10, 20));
    }

    #[test]
    fn size_hints_apply_base_and_increment() {
        let hints = SizeHints { base_w: 10, base_h: 20, inc_w: 10, inc_h: 10, ..Default::default() };
        let got = constrain_size(&hints, box_(123, 133), 0, 0);
        assert_eq!((got.w, got.h), (120, 130));
    }

    #[test]
    fn size_hints_enforce_maximum() {
        let hints = SizeHints { max_w: 300, max_h: 200, ..Default::default() };
        let got = constrain_size(&hints, box_(500, 500), 0, 0);
        assert_eq!((got.w, got.h), (300, 200));
    }

    #[test]
    fn drag_geom_keeps_grab_offset_and_size_instead_of_centering_on_pointer() {
        let start = Rect { x: 100, y: 200, w: 1000, h: 500 };
        let (ox, oy) = (300, 120); // grabbed at (400, 320)

        // First motion without moving the pointer: no jump and no resize.
        assert_eq!(
            Wm::drag_geom((400, 320), (ox, oy), start),
            start
        );
        // Moving the pointer moves the top-left by the same amount, size intact.
        assert_eq!(
            Wm::drag_geom((700, 520), (ox, oy), start),
            Rect { x: 400, y: 400, w: 1000, h: 500 }
        );
    }

    #[test]
    fn nearest_tile_picks_closest_box_in_a_gap() {
        let leaves = [
            (1, Rect { x: 0, y: 0, w: 400, h: 500 }),
            (2, Rect { x: 420, y: 0, w: 400, h: 500 }),
        ];
        assert_eq!(Wm::nearest_tile(&leaves, (410, 250)).map(|(w, _)| *w), Some(1));
        assert_eq!(Wm::nearest_tile(&leaves, (425, 250)).map(|(w, _)| *w), Some(2));
    }
}

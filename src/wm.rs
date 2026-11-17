use std::collections::HashSet;
use std::error::Error;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::mpsc::Receiver;
use std::thread;
use std::time::{Duration, Instant};

use x11rb::connection::Connection;
use x11rb::protocol::xproto::{
    AtomEnum, ButtonIndex, ChangeWindowAttributesAux, ClientMessageEvent, ColormapAlloc,
    ConfigureWindowAux, ConnectionExt, CreateWindowAux, EventMask, Gravity, GrabMode, GrabStatus,
    InputFocus, KeyPressEvent, ModMask, PropMode, StackMode, Window, WindowClass,
};
use x11rb::protocol::xkb::{self, ConnectionExt as _};
use x11rb::protocol::Event;
use x11rb::rust_connection::RustConnection;
use x11rb::wrapper::ConnectionExt as _;
use x11rb::{CURRENT_TIME, NONE};

use crate::bar::{
    BAR_BACKGROUND_PIXEL, BARGAP, CLOCKPAD, Gl, HORIZPADBAR, KBLAYOUTPAD, LAUNCHERS,
    LAYOUT_SYMBOL, Metrics, TAG_LABEL, TAGS,
};
use crate::render::{
    self, ClockBar, ClockRenderer, Frame, MonitorBar, RightBar, Renderer, TagsBar, TextBar, TitleBar,
};
use crate::config::{self, BORDERPX, FLOATBAR, TOPBAR};
use crate::keys::{self, Action, GapScope, Key, MOD_4, TAGMASK, TAG_COUNT};
use crate::tree::{self, Gaps, Node, Rect};

pub type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

const LOCK_MASK: u16 = 1 << 1;
const MOD2_MASK: u16 = 1 << 4;
/// dwm's CLEANMASK: every modifier except CapsLock and NumLock (Mod2 here).
const CLEAN_MASK: u16 = 0xFD & !MOD2_MASK;

pub struct Client {
    pub win: Window,
    pub tags: u32,
    pub mon: usize,
    /// dwm's `isfloating`: a floating window is outside the tiling tree.
    pub floating: bool,
    /// The outer box of a floating window, like dwm's `x`, `y`, `w` and `h`.
    pub geom: Rect,
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
fn create_resize_cursors(gl: &Gl) -> ResizeCursors {
    ResizeCursors {
        moving: gl.load_cursor("fleur"),
        horizontal: gl.load_cursor("sb_h_double_arrow"),
        vertical: gl.load_cursor("sb_v_double_arrow"),
        top_left: gl.load_cursor("top_left_corner"),
        top_right: gl.load_cursor("top_right_corner"),
        bottom_left: gl.load_cursor("bottom_left_corner"),
        bottom_right: gl.load_cursor("bottom_right_corner"),
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
    /// Text measuring for the layout. Drawing happens on `renderer`.
    metrics: Metrics,
    renderer: Renderer,
    clock_renderer: ClockRenderer,
    visual_id: u32,
    depth: u8,
    clock: String,
    /// dwm's `clockbar_peak` source. `None` when `CLOCK_ANIMATE` is off.
    clock_peak: Option<crate::sound::Peak>,
    /// dwm's `clockbar_dynw` minus `clockbar_cw`: px the clock bar grows past
    /// its text width on the selected monitor.
    clock_extra: i32,
    /// dwm's `stext` (status text) and `kbstr` (keyboard layout).
    stext: String,
    kbstr: String,
    status: crate::status::StatusSampler,
    mpris_rx: Receiver<crate::mpris::Snapshot>,
    mpris: crate::mpris::Snapshot,
    mpris_scroll_text: String,
    mpris_scroll_px: u32,
    mpris_scroll_last: Instant,
    mpris_scroll_accum: Duration,
    mpris_hovered: bool,
    mpris_marker_hovered: bool,
    mpris_volume_drag: bool,
    mpris_marker_rect: Option<(i32, i32, i32, i32)>,
    /// First event code of the XKB extension, or 0 when it is unavailable.
    xkb_event_base: u8,
    /// dwm's `enablegaps`, toggled by `ToggleGaps`.
    gaps_enabled: bool,
    resize_cursors: ResizeCursors,
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

/// A bar-sized window with the GLX `visual` and `depth`, for a GL context to draw into.
fn gl_window(conn: &RustConnection, root: Window, visual: u32, depth: u8) -> Result<u32> {
    let win = conn.generate_id()?;
    let cmap = conn.generate_id()?;
    conn.create_colormap(ColormapAlloc::NONE, cmap, root, visual)?;
    conn.create_window(
        depth,
        win,
        root,
        0,
        0,
        1,
        1,
        0,
        WindowClass::INPUT_OUTPUT,
        visual,
        &CreateWindowAux::new()
            .background_pixel(BAR_BACKGROUND_PIXEL)
            .border_pixel(0)
            .colormap(cmap),
    )?
    .check()?;
    Ok(win)
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

        let gl = Gl::new(|visual, depth| gl_window(&conn, root, visual, depth))?;

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
        let stext = status.sample_with_mpris(Some(&mpris));
        let resize_cursors = create_resize_cursors(&gl);
        conn.change_window_attributes(
            root,
            &ChangeWindowAttributesAux::new().cursor(gl.load_cursor("left_ptr")),
        )?;
        let metrics = Metrics::open()?;
        let (visual_id, depth) = (gl.visual_id, gl.depth);
        let renderer = render::spawn(gl);
        let clock_renderer = render::spawn_clock(depth);
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
            renderer,
            clock_renderer,
            visual_id,
            depth,
            clock: now_clock(),
            clock_peak: config::CLOCK_ANIMATE.then(crate::sound::start),
            clock_extra: 0,
            stext,
            kbstr: "us".to_string(),
            status,
            mpris_rx,
            mpris,
            mpris_scroll_text: String::new(),
            mpris_scroll_px: 0,
            mpris_scroll_last: Instant::now(),
            mpris_scroll_accum: Duration::ZERO,
            mpris_hovered: false,
            mpris_marker_hovered: false,
            mpris_volume_drag: false,
            mpris_marker_rect: None,
            xkb_event_base: 0,
            gaps_enabled: true,
            resize_cursors,
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

    /// The monitor's area below the bar, set by `update_bar_pos`.
    fn work(&self, mi: usize) -> Rect {
        let m = &self.monitors[mi];
        Rect { x: m.wx, y: m.wy, w: m.ww as u32, h: m.wh as u32 }
    }

    /// The visible tiled windows on `mi` in stack order.
    fn tiled_order(&self, mi: usize) -> Vec<Window> {
        self.clients
            .iter()
            .filter(|c| c.mon == mi && !c.floating && self.is_visible(c))
            .map(|c| c.win)
            .collect()
    }

    /// The outer box `win` is drawn in: its floating geometry or its tile.
    fn geometry(&self, mi: usize, win: Window) -> Option<Rect> {
        if let Some(c) = self.clients.iter().find(|c| c.win == win && c.floating) {
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
        let mut rw = self.metrics.status_width(&self.stext) + HORIZPADBAR;
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

    /// dwm's `resizebarwin()`, without the systray, Finder, notification and
    /// MPRIS sections. The clock window is placed by the clock thread.
    fn resize_bar_win(&self, mi: usize) -> Result {
        let m = &self.monitors[mi];
        let bh = self.bar_h();
        let conn = &self.conn;
        let place = |win: Window, x: i32, y: i32, w: i32, h: i32| -> Result {
            conn.configure_window(
                win,
                &ConfigureWindowAux::new()
                    .x(x)
                    .y(y)
                    .width(w.max(1) as u32)
                    .height(h.max(1) as u32),
            )?;
            Ok(())
        };

        if !m.showbar {
            for win in [m.barwin, m.bartitlewin, m.barcenterwin, m.barkbwin, m.barrightwin] {
                place(win, m.wx, m.by, 1, bh)?;
            }
            self.conn.unmap_window(m.mpris_markerwin)?;
            return Ok(());
        }

        let b = self.barwidths(mi);
        let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
        let rx = lx + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw;

        place(m.barwin, lx, m.by, b.tw, bh)?;

        let kx = lx + b.tw + BARGAP;
        place(m.barkbwin, kx, m.by, b.kw, bh)?;
        self.conn.map_window(m.barkbwin)?;

        let titlex = kx + b.kw + BARGAP;
        place(m.bartitlewin, titlex, m.by, b.tlw, bh)?;
        self.conn.map_window(m.bartitlewin)?;

        if self.clock_place(mi).is_some() {
            self.conn.map_window(m.barcenterwin)?;
        } else {
            self.conn.unmap_window(m.barcenterwin)?;
        }

        let right_h = if self.mpris_hovered && mi == self.selmon && self.mpris.present {
            bh * 2
        } else {
            bh
        };
        place(m.barrightwin, rx, m.by, b.rw, right_h)?;
        self.conn.map_window(m.barrightwin)?;
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

    /// Moves and sizes `win` to the outer box `r`. The client area is inset
    /// by the border on each side, as in dwm's resize().
    fn place(&self, win: Window, r: Rect) -> Result {
        let inner_w = (r.w as i32 - 2 * BORDERPX).max(1) as u32;
        let inner_h = (r.h as i32 - 2 * BORDERPX).max(1) as u32;
        self.conn.configure_window(
            win,
            &ConfigureWindowAux::new()
                .x(r.x)
                .y(r.y)
                .width(inner_w)
                .height(inner_h)
                .border_width(BORDERPX as u32),
        )?;
        Ok(())
    }

    fn apply_layout(&self) -> Result {
        let mut boxes: Vec<(Window, Rect)> = Vec::new();
        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
            for (win, r) in self.layout_mon(mi) {
                self.place(win, r)?;
                boxes.push((win, r));
            }
        }
        // Oldest first, so the newest floating window ends up on top.
        for c in self.clients.iter().rev().filter(|c| c.floating && self.is_visible(c)) {
            self.place(c.win, c.geom)?;
            self.conn.configure_window(
                c.win,
                &ConfigureWindowAux::new().stack_mode(StackMode::ABOVE),
            )?;
            boxes.push((c.win, c.geom));
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
                self.conn.unmap_window(c.win)?;
            }
        }
        for c in &self.clients {
            match boxes.iter().find(|(w, _)| *w == c.win) {
                Some((_, r)) => self.place_edge_zones(c, *r)?,
                None => {
                    for zone in c.edge_wins {
                        self.conn.unmap_window(zone)?;
                    }
                }
            }
        }
        self.conn.flush()?;
        Ok(())
    }

    /// Puts the hover zones of `c` over its outer box `r`, each directly above
    /// the window so that other windows still stack over it correctly.
    fn place_edge_zones(&self, c: &Client, r: Rect) -> Result {
        let zones = tree::edge_zones(r, config::RESIZE_EDGE_PX);
        for (zone, z) in c.edge_wins.iter().zip(zones) {
            self.conn.configure_window(
                *zone,
                &ConfigureWindowAux::new()
                    .x(z.x)
                    .y(z.y)
                    .width(z.w.max(1))
                    .height(z.h.max(1))
                    .sibling(c.win)
                    .stack_mode(StackMode::ABOVE),
            )?;
            self.conn.map_window(*zone)?;
        }
        Ok(())
    }

    fn arrange(&mut self) -> Result {
        for mi in 0..self.monitors.len() {
            self.ensure_sel(mi);
            self.update_bar_pos(mi);
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
                let side_by_side = rect.w > rect.h;
                let new_first = if side_by_side {
                    mx < rect.x + (rect.w / 2) as i32
                } else {
                    my < rect.y + (rect.h / 2) as i32
                };
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
        self.clients.insert(0, Client { win, tags, mon: mi, floating: false, geom, edge_wins });
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
        for zone in client.edge_wins {
            self.conn.destroy_window(zone)?;
        }
        let m = &mut self.monitors[client.mon];
        m.tree = m.tree.take().and_then(|t| t.remove(win));
        if m.sel == Some(win) {
            m.sel = None;
        }
        self.arrange()
    }

    fn client_name(&self, win: Window) -> String {
        let utf8 = self
            .conn
            .get_property(false, win, self.atoms.net_wm_name, self.atoms.utf8_string, 0, 256)
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

    /// Redraws every shown bar. Returns true when the clock text changed.
    pub fn update_clock(&mut self) -> bool {
        let now = now_clock();
        if now == self.clock {
            return false;
        }
        self.clock = now;
        true
    }

    /// dwm's `updateclockbar()` width step: maps the PipeWire peak to extra
    /// clock width, the same truncation as `clock_draw_loop`. Returns true when
    /// the width changed.
    pub fn update_clock_anim(&mut self) -> bool {
        let extra = match &self.clock_peak {
            Some(peak) => {
                let level = crate::sound::read(peak);
                (level * config::CLOCK_ANIM_EXTRA as f32) as i32
            }
            None => 0,
        };
        if extra == self.clock_extra {
            return false;
        }
        self.clock_extra = extra;
        true
    }

    /// Redraws every shown bar. Returns true when the status text changed.
    pub fn update_status(&mut self) -> bool {
        let new_status = self.status.sample_with_mpris(Some(&self.mpris));
        if new_status != self.stext {
            self.stext = new_status;
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
            self.mpris_scroll_accum = Duration::ZERO;
            self.mpris_scroll_last = Instant::now();
        }
        let changed = self.mpris.present != snapshot.present
            || self.mpris.playing != snapshot.playing
            || self.mpris.service != snapshot.service
            || self.mpris.artist != snapshot.artist
            || self.mpris.title != snapshot.title
            || self.mpris.art_url != snapshot.art_url
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
        if !self.mpris.present || !self.mpris.playing || self.mpris_scroll_text.is_empty() {
            self.mpris_scroll_last = Instant::now();
            self.mpris_scroll_accum = Duration::ZERO;
            return false;
        }
        let text_width = self.metrics.text_width(&self.mpris_scroll_text);
        if text_width + 16 <= 240 {
            self.mpris_scroll_px = 0;
            self.mpris_scroll_last = Instant::now();
            self.mpris_scroll_accum = Duration::ZERO;
            return false;
        }

        let now = Instant::now();
        let elapsed = now.duration_since(self.mpris_scroll_last).min(Duration::from_millis(250));
        self.mpris_scroll_last = now;
        self.mpris_scroll_accum += elapsed;
        let frame = Duration::from_nanos(33_333_333);
        let steps = (self.mpris_scroll_accum.as_nanos() / frame.as_nanos()) as u32;
        if steps == 0 {
            return false;
        }
        self.mpris_scroll_accum -= frame * steps;
        let cycle = (text_width + 32).max(1) as u32;
        self.mpris_scroll_px = (self.mpris_scroll_px + steps) % cycle;
        true
    }

    /// Recomputes and updates the positions and widths of all bar windows.
    pub fn update_bars_geometry(&self) -> Result {
        for mi in 0..self.monitors.len() {
            self.resize_bar_win(mi)?;
        }
        Ok(())
    }

    /// dwm's `drawbar()` for each shown monitor, one window per section. The
    /// layout and the MPRIS marker window are set here, and the pixels are
    /// drawn by the render thread from the frame built here.
    pub fn draw_bars(&mut self, redraw_bars: bool) -> Result {
        self.mpris_marker_rect = None;
        let mut frame = Frame { monitors: Vec::new() };
        let mut clocks: Vec<ClockBar> = Vec::new();
        for (mi, m) in self.monitors.iter().enumerate() {
            if !m.showbar {
                continue;
            }
            let occupied = self
                .clients
                .iter()
                .filter(|c| c.mon == mi)
                .fold(0, |acc, c| acc | c.tags);
            let title = m.sel.map(|w| self.client_name(w));
            let focused = mi == self.selmon;
            let b = self.barwidths(mi);
            let right = if mi == self.selmon && self.mpris_hovered && self.mpris.present {
                let rw = b.rw.max(1);
                let (marker_x, marker_y, marker_w, marker_h) = crate::bar::mpris_knob(
                    rw,
                    self.bar_h(),
                    self.mpris.volume,
                    self.mpris_marker_hovered,
                );
                let lx = if FLOATBAR { m.wx + m.gaps.ov } else { m.wx };
                let rx = lx + (if FLOATBAR { m.ww - 2 * m.gaps.ov } else { m.ww }) - b.rw;
                let x = rx + marker_x;
                let y = m.by + marker_y;
                self.conn.configure_window(
                    m.mpris_markerwin,
                    &ConfigureWindowAux::new()
                        .x(x)
                        .y(y)
                        .width(marker_w as u32)
                        .height(marker_h as u32),
                )?;
                self.conn.map_window(m.mpris_markerwin)?;
                self.mpris_marker_rect = Some((x, y, marker_w, marker_h));
                RightBar::Panel {
                    win: m.barrightwin,
                    w: b.rw,
                    text: self.stext.clone(),
                    player: self.mpris.clone(),
                    scroll: self.mpris_scroll_px,
                    marker_hovered: self.mpris_marker_hovered,
                }
            } else {
                self.conn.unmap_window(m.mpris_markerwin)?;
                RightBar::Status {
                    win: m.barrightwin,
                    w: b.rw,
                    text: self.stext.clone(),
                    scroll: self.mpris_scroll_px,
                    progress: self.mpris.progress,
                }
            };
            if let Some((x, dcw)) = self.clock_place(mi) {
                clocks.push(ClockBar {
                    win: m.barcenterwin,
                    x,
                    y: m.by,
                    w: dcw,
                    text: self.clock.clone(),
                    focused,
                });
            }
            frame.monitors.push(MonitorBar {
                tags: TagsBar {
                    win: m.barwin,
                    w: b.tw,
                    occupied,
                    selected: self.tags_of(mi),
                },
                title: TitleBar {
                    win: m.bartitlewin,
                    w: b.tlw,
                    name: title,
                    focused,
                },
                kb: TextBar {
                    win: m.barkbwin,
                    w: b.kw,
                    text: self.kbstr.clone(),
                    focused,
                },
                right,
            });
        }
        self.conn.flush()?;
        // The render thread swaps buffers on its own connection. Wait until
        // the server has applied the moves and resizes above, so each swap
        // lands on a window of the size it was drawn for.
        self.conn.get_input_focus()?.reply()?;
        self.clock_renderer.submit(clocks);
        if redraw_bars {
            self.renderer.submit(frame);
        }
        Ok(())
    }

    /// One pass of the bar's per-tick work: applies state changes, then
    /// redraws the bars if anything changed or `dirty` was set by an event.
    pub fn refresh(&mut self, dirty: bool) -> Result {
        let mut bars = dirty;
        if self.update_mpris() {
            bars = true;
        }
        let clock = self.update_clock() | self.update_clock_anim();
        if self.update_status() {
            bars = true;
        }
        if self.update_mpris_scroll() {
            bars = true;
        }
        if bars || clock {
            self.update_bars_geometry()?;
            self.draw_bars(bars)?;
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
            }
            // Hidden clients are unmapped by apply_layout, so UnmapNotify is
            // not a sign that a client went away. DestroyNotify handles that.
            Event::UnmapNotify(_) => {}
            Event::DestroyNotify(e) => self.unmanage(e.window)?,
            Event::ConfigureRequest(e) => {
                if self.is_managed(e.window) {
                    self.apply_layout()?;
                } else {
                    self.conn.configure_window(
                        e.window,
                        &ConfigureWindowAux::new()
                            .x(e.x as i32)
                            .y(e.y as i32)
                            .width(e.width as u32)
                            .height(e.height as u32),
                    )?;
                }
            }
            Event::EnterNotify(e) => {
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
                    }
                }
            }
            Event::KeyPress(e) => self.key_press(e)?,
            Event::PropertyNotify(e)
                if e.window == self.root
                    && (e.atom == u32::from(AtomEnum::WM_NAME) || e.atom == self.atoms.net_wm_name) =>
            {
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
        loop {
            // Polls instead of blocking, so the bar keeps updating during the drag.
            let mut latest = None;
            let mut handled = false;
            while let Some(event) = self.conn.poll_for_event()? {
                handled = true;
                match event {
                    Event::MotionNotify(e) => latest = Some((e.root_x as i32, e.root_y as i32)),
                    Event::ButtonRelease(e) => {
                        let end = (e.root_x as i32, e.root_y as i32);
                        on_motion(self, end.0, end.1)?;
                        self.set_no_animation(win, false)?;
                        self.conn.ungrab_pointer(CURRENT_TIME)?;
                        self.conn.flush()?;
                        return Ok(Some(end));
                    }
                    other => self.handle(other)?,
                }
            }
            if let Some((x, y)) = latest {
                on_motion(self, x, y)?;
            }
            self.refresh(handled)?;
            thread::sleep(Duration::from_millis(5));
        }
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
    fn place_floating(&self, win: Window) -> Result {
        let Some(c) = self.clients.iter().find(|c| c.win == win) else {
            return Ok(());
        };
        self.place(c.win, c.geom)?;
        self.place_edge_zones(c, c.geom)?;
        self.conn.flush()?;
        Ok(())
    }

    /// dwm's `movemouse()` and `placemouse()`. A floating window follows the
    /// pointer. A tiled one follows it too and is re-inserted at the tile under
    /// the pointer on release.
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
        }
        let (ox, oy) = (px - start.x, py - start.y);
        let end = self.drag_pointer(win, self.resize_cursors.moving, |wm, x, y| {
            if floating {
                if let Some(c) = wm.clients.iter_mut().find(|c| c.win == win) {
                    c.geom.x = x - ox;
                    c.geom.y = y - oy;
                }
                return wm.place_floating(win);
            }
            wm.conn.configure_window(
                win,
                &ConfigureWindowAux::new()
                    .x(x - ox)
                    .y(y - oy)
                    .stack_mode(StackMode::ABOVE),
            )?;
            wm.conn.flush()?;
            Ok(())
        })?;
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
        let leaves = self.layout_mon(tm);
        let target = leaves
            .iter()
            .copied()
            .find(|(w, r)| *w != win && r.contains(dx, dy));
        if let Some((target, rect)) = target {
            let side_by_side = rect.w > rect.h;
            let new_first = if side_by_side {
                dx < rect.x + (rect.w / 2) as i32
            } else {
                dy < rect.y + (rect.h / 2) as i32
            };
            let tree = &mut self.monitors[tm].tree;
            *tree = tree.take().and_then(|t| t.remove(win));
            if let Some(t) = tree.as_mut() {
                t.insert(target, win, new_first, side_by_side);
            }
        }
        self.arrange()
    }

    /// dwm's `resizemouse()`. The part of the window the press landed in picks
    /// the edges that move. A floating window changes its size by the
    /// pointer's movement from the press, with the opposite edges staying put.
    /// A tiled window stays tiled: the split boundaries on the chosen edges
    /// follow the pointer.
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
            self.drag_pointer(win, cursor, |wm, x, y| {
                let geom = tree::resize_rect(rect, edges, (x - mx, y - my));
                if let Some(c) = wm.clients.iter_mut().find(|c| c.win == win) {
                    c.geom = geom;
                }
                wm.place_floating(win)
            })?;
            return self.arrange();
        }
        let (mut lx, mut ly) = (mx, my);
        self.drag_pointer(win, cursor, |wm, x, y| {
            wm.resize_tiled(mi, win, edges, (x - lx, y - ly));
            (lx, ly) = (x, y);
            wm.apply_layout()
        })?;
        self.arrange()
    }

    /// Moves the tree boundaries next to the tiled window `win` on `edges`.
    fn resize_tiled(&mut self, mi: usize, win: Window, edges: (bool, bool, bool, bool), delta: (i32, i32)) {
        let vis: HashSet<Window> = self.tiled_order(mi).into_iter().collect();
        let gaps = self.effective_gaps(mi);
        let area = self.tile_area(mi);
        if let Some(tree) = self.monitors[mi].tree.as_mut() {
            tree::resize_tiled(tree, area, &vis, &gaps, win, edges, delta);
        }
    }

    /// dwm's `togglefloating()`: moves the selected window between the tiling
    /// tree and the floating layer.
    fn togglefloating(&mut self) -> Result {
        let mi = self.selmon;
        let Some(sel) = self.monitors[mi].sel else {
            return Ok(());
        };
        let Some(c) = self.clients.iter().find(|c| c.win == sel) else {
            return Ok(());
        };
        if c.floating {
            let area = self.tile_area(mi);
            if let Some(c) = self.clients.iter_mut().find(|c| c.win == sel) {
                c.floating = false;
            }
            let tree = &mut self.monitors[mi].tree;
            *tree = Some(tree::append(tree.take(), sel, area));
        } else {
            let Some(rect) = self.geometry(mi, sel) else {
                return Ok(());
            };
            self.float_window(mi, sel, rect);
        }
        self.arrange()
    }

    /// Takes `win` out of the tiling tree and gives it `rect` as its floating
    /// geometry. The caller arranges the layout.
    fn float_window(&mut self, mi: usize, win: Window, rect: Rect) {
        let tree = &mut self.monitors[mi].tree;
        *tree = tree.take().and_then(|t| t.remove(win));
        if let Some(c) = self.clients.iter_mut().find(|c| c.win == win) {
            c.floating = true;
            c.geom = rect;
        }
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

//! Freedesktop system tray: own `_NET_SYSTEM_TRAY_Sn` and host XEMBED icons.
//!
//! The tray is a single override-redirect window that follows the selected
//! monitor. Background apps send `_NET_SYSTEM_TRAY_OPCODE` dock requests to the
//! selection owner; their icon windows are reparented here and laid out in a
//! horizontal row. Clicks are delivered straight to the icon windows, so each
//! app keeps handling its own menu and activation.

use std::error::Error;

use x11rb::connection::Connection;
use x11rb::protocol::xproto::{
    AtomEnum, ChangeWindowAttributesAux, ClientMessageEvent, ColormapAlloc, ConfigureWindowAux,
    ConnectionExt, CreateWindowAux, EventMask, PropMode, SELECTION_NOTIFY_EVENT,
    SelectionNotifyEvent, SelectionRequestEvent, Window, WindowClass,
};
use x11rb::rust_connection::RustConnection;
use x11rb::wrapper::ConnectionExt as _;
use x11rb::{CURRENT_TIME, NONE};

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

pub const SYSTEM_TRAY_REQUEST_DOCK: u32 = 0;

/// XEMBED protocol message numbers used by the host side.
const XEMBED_EMBEDDED_NOTIFY: u32 = 0;
const XEMBED_WINDOW_ACTIVATE: u32 = 1;
const XEMBED_FOCUS_IN: u32 = 4;
const XEMBED_REQUEST_FOCUS: u32 = 3;
/// `_XEMBED_INFO` flags bit: the embedee wants to be mapped.
const XEMBED_MAPPED: u32 = 1;

pub struct Atoms {
    pub manager: u32,
    pub opcode: u32,
    pub orientation: u32,
    pub visual: u32,
    pub xembed: u32,
    pub xembed_info: u32,
    pub targets: u32,
}

#[derive(Clone, Copy)]
struct Icon {
    win: Window,
    /// XEMBED_MAPPED flag from `_XEMBED_INFO`.
    mapped: bool,
    /// Whether the client currently wants the icon on screen.
    visible: bool,
    /// Geometry the icon had when it was docked, used to keep its aspect
    /// ratio the way dwm's `updatesystrayicongeom()` does.
    geom_w: i32,
    geom_h: i32,
}

impl Icon {
    /// Width inside the bar for icon height `h`: square when the icon is
    /// square, otherwise scaled from its docked width/height (dwm's formula).
    fn width(&self, h: i32) -> i32 {
        if self.geom_h <= 0 || self.geom_w == self.geom_h {
            h
        } else if self.geom_h == h {
            self.geom_w
        } else {
            (h as f64 * (self.geom_w as f64 / self.geom_h as f64)) as i32
        }
    }
}

pub struct Tray {
    pub window: Window,
    pub colormap: u32,
    pub selection: u32,
    pub owns_selection: bool,
    depth: u8,
    root: Window,
    atoms: Atoms,
    icons: Vec<Icon>,
}

impl Tray {
    pub fn new(
        conn: &RustConnection,
        root: Window,
        atoms: Atoms,
        screen: i32,
        visual: u32,
        depth: u8,
        background: u32,
    ) -> Result<Tray> {
        let name = format!("_NET_SYSTEM_TRAY_S{screen}");
        let selection = conn.intern_atom(false, name.as_bytes())?.reply()?.atom;
        let colormap = conn.generate_id()?;
        conn.create_colormap(ColormapAlloc::NONE, colormap, root, visual)?
            .check()?;
        let window = conn.generate_id()?;
        conn.create_window(
            depth,
            window,
            root,
            0,
            0,
            1,
            1,
            0,
            WindowClass::INPUT_OUTPUT,
            visual,
            &CreateWindowAux::new()
                .background_pixel(background)
                .border_pixel(0)
                .colormap(colormap)
                .override_redirect(1)
                .event_mask(
                    EventMask::STRUCTURE_NOTIFY
                        | EventMask::SUBSTRUCTURE_NOTIFY
                        | EventMask::PROPERTY_CHANGE,
                ),
        )?
        .check()?;

        // The selection owner advertises the opcode atom and the visual that
        // embedded icon windows must use (32-bit ARGB when available).
        conn.change_property32(
            PropMode::REPLACE,
            window,
            atoms.opcode,
            AtomEnum::ATOM,
            &[atoms.opcode],
        )?;
        conn.change_property32(
            PropMode::REPLACE,
            window,
            atoms.orientation,
            AtomEnum::CARDINAL,
            &[0], // SYSTEM_TRAY_ORIENTATION_HORZ
        )?;
        conn.change_property32(
            PropMode::REPLACE,
            window,
            atoms.visual,
            AtomEnum::VISUALID,
            &[visual],
        )?;
        Ok(Tray {
            window,
            colormap,
            selection,
            owns_selection: false,
            depth,
            root,
            atoms,
            icons: Vec::new(),
        })
    }

    /// ICCCM manager selection: take ownership, then announce it on root so
    /// newly started apps know where to send their dock requests.
    pub fn claim(&mut self, conn: &RustConnection, root: Window) -> Result {
        conn.set_selection_owner(self.window, self.selection, CURRENT_TIME)?
            .check()?;
        self.owns_selection = conn
            .get_selection_owner(self.selection)?
            .reply()?
            .owner
            == self.window;
        if self.owns_selection {
            let ev = ClientMessageEvent::new(
                32,
                root,
                self.atoms.manager,
                [CURRENT_TIME, self.selection, self.window, 0, 0],
            );
            conn.send_event(
                false,
                root,
                EventMask::SUBSTRUCTURE_NOTIFY | EventMask::SUBSTRUCTURE_REDIRECT,
                ev,
            )?;
        }
        Ok(())
    }

    pub fn contains(&self, win: Window) -> bool {
        win != 0 && self.icons.iter().any(|i| i.win == win)
    }

    pub fn is_empty(&self) -> bool {
        self.icons.is_empty()
    }

    /// Icon whose cell contains local coordinate `x`, using the same layout as
    /// `layout()`. Used to associate a click on the tray with the app that owns
    /// the icon, so a menu mapped a moment later can be recognised.
    pub fn icon_at(&self, x: i32, icon_h: i32, spacing: i32) -> Option<Window> {
        let mut left = spacing;
        for icon in self.icons.iter().filter(|i| i.visible) {
            let w = icon.width(icon_h);
            if x >= left && x < left + w {
                return Some(icon.win);
            }
            left += w + spacing;
        }
        None
    }

    /// dwm's `getsystraywidth()`: every icon is preceded by `spacing` and the
    /// last one is followed by another `spacing`. Only visible icons count.
    pub fn width(&self, icon_h: i32, spacing: i32) -> i32 {
        let mut w = 0;
        for icon in self.icons.iter().filter(|i| i.visible) {
            w += icon.width(icon_h) + spacing;
        }
        if w > 0 { w + spacing } else { 0 }
    }

    pub fn dock(&mut self, conn: &RustConnection, win: Window) -> Result<bool> {
        if win == 0 || win == self.window || self.contains(win) {
            return Ok(false);
        }
        let mapped = self.xembed_mapped(conn, win).unwrap_or(true);
        // Apps often create icon windows on their own visual with the same
        // depth and channel masks as root (Discord uses visual 996 vs root's
        // 33 here). XReparentWindow only needs matching depth; requiring an
        // identical visual id would silently skip every one of those icons.
        let geom = match conn.get_geometry(win).ok().and_then(|c| c.reply().ok()) {
            Some(geom) => geom,
            None => return Ok(false),
        };
        if geom.depth != self.depth {
            return Ok(false);
        }
        let cookie = match conn.reparent_window(win, self.window, 0, 0) {
            Ok(cookie) => cookie,
            Err(_) => return Ok(false),
        };
        if let Err(err) = cookie.check() {
            eprintln!("rwm: tray: cannot reparent {win:#x}: {err}");
            return Ok(false);
        }
        if let Ok(cookie) = conn.change_window_attributes(
            win,
            &ChangeWindowAttributesAux::new()
                .event_mask(EventMask::STRUCTURE_NOTIFY | EventMask::PROPERTY_CHANGE),
        ) {
            let _ = cookie.check();
        }
        let _ = conn.configure_window(win, &ConfigureWindowAux::new().border_width(0));
        self.icons.push(Icon {
            win,
            mapped,
            visible: true,
            geom_w: geom.width as i32,
            geom_h: geom.height as i32,
        });
        // EMBEDDED_NOTIFY's detail is the host's XEMBED version, data1 its
        // window. The other messages make the icon behave as if active.
        self.send(conn, win, XEMBED_EMBEDDED_NOTIFY, 1, self.window, 0);
        self.send(conn, win, XEMBED_WINDOW_ACTIVATE, 0, 0, 0);
        Ok(true)
    }

    pub fn undock(&mut self, win: Window) -> bool {
        if let Some(i) = self.icons.iter().position(|i| i.win == win) {
            self.icons.remove(i);
            true
        } else {
            false
        }
    }

    /// Updates the XEMBED_MAPPED state from a `_XEMBED_INFO` property notify.
    pub fn read_info(&mut self, conn: &RustConnection, win: Window) -> bool {
        let Some(mapped) = self.xembed_mapped(conn, win) else {
            return false;
        };
        if let Some(icon) = self.icons.iter_mut().find(|i| i.win == win) {
            let changed = icon.mapped != mapped || (mapped && !icon.visible);
            icon.mapped = mapped;
            // A layout pass unmaps icons whose XEMBED_MAPPED flag is clear;
            // that UnmapNotify clears `visible`. Setting the flag again must
            // bring the icon back instead of leaving an empty slot, even when
            // the flag itself was already set in our cached state.
            if mapped {
                icon.visible = true;
            }
            changed
        } else {
            false
        }
    }

    pub fn set_visible(&mut self, win: Window, visible: bool) -> bool {
        if let Some(icon) = self.icons.iter_mut().find(|i| i.win == win) {
            let changed = icon.visible != visible;
            icon.visible = visible;
            changed
        } else {
            false
        }
    }

    /// dwm's `updatesystray()`: icons start one `spacing` in from the tray's
    /// left edge and are separated by `spacing`; `tray_width()` reserves the
    /// matching gap after the last one.
    pub fn layout(&self, conn: &RustConnection, icon_h: i32, spacing: i32, bar_h: i32) -> Result {
        let y = ((bar_h - icon_h) / 2).max(0);
        let mut x = spacing;
        for icon in &self.icons {
            if !icon.visible {
                conn.unmap_window(icon.win)?;
                continue;
            }
            let w = icon.width(icon_h);
            conn.configure_window(
                icon.win,
                &ConfigureWindowAux::new()
                    .x(x)
                    .y(y)
                    .width(w as u32)
                    .height(icon_h as u32)
                    .border_width(0),
            )?;
            if icon.mapped {
                conn.map_window(icon.win)?;
            } else {
                conn.unmap_window(icon.win)?;
            }
            x += w + spacing;
        }
        Ok(())
    }

    /// Moves keyboard focus into an icon that asked for it with XEMBED.
    pub fn focus_icon(&self, conn: &RustConnection, win: Window) -> Result {
        if !self.contains(win) {
            return Ok(());
        }
        conn.set_input_focus(x11rb::protocol::xproto::InputFocus::POINTER_ROOT, win, CURRENT_TIME)?;
        self.send(conn, win, XEMBED_FOCUS_IN, 0, 0, 0);
        Ok(())
    }

    /// Handles `_NET_SYSTEM_TRAY_OPCODE` sent to the selection owner.
    /// Per spec the fields are `time, opcode, window, data1, data2`; the
    /// older `opcode, window` layout is also accepted for older toolkits.
    pub fn opcode(&mut self, conn: &RustConnection, window: Window, data: &[u32]) -> Result<bool> {
        if window != self.window || data.len() < 2 {
            return Ok(false);
        }
        let icon = if data[1] == SYSTEM_TRAY_REQUEST_DOCK && data.get(2).copied().unwrap_or(0) != 0 {
            data[2]
        } else if data[0] == SYSTEM_TRAY_REQUEST_DOCK {
            data[1]
        } else {
            // BEGIN_MESSAGE/CANCEL_MESSAGE are balloon requests. rwm has no
            // popup surface for them, so acknowledging them by ignoring is fine.
            return Ok(true);
        };
        self.dock(conn, icon)?;
        Ok(true)
    }

    /// Docks icon windows that were created before rwm claimed the selection.
    /// Apps send the dock request once; a WM restart otherwise leaves their
    /// icon windows orphaned on root, which is why Discord can be open but
    /// absent from a freshly started tray.
    pub fn scan_existing(&mut self, conn: &RustConnection, root: Window) -> Result<usize> {
        let children = conn.query_tree(root)?.reply()?.children;
        let mut found = Vec::new();
        for win in children {
            if win == self.window || self.contains(win) {
                continue;
            }
            let has_info = conn
                .get_property(
                    false,
                    win,
                    self.atoms.xembed_info,
                    self.atoms.xembed_info,
                    0,
                    1,
                )
                .ok()
                .and_then(|c| c.reply().ok())
                .is_some_and(|r| r.type_ == self.atoms.xembed_info);
            if has_info {
                found.push(win);
            }
        }
        let count = found.len();
        for win in found {
            self.dock(conn, win)?;
        }
        Ok(count)
    }

    pub fn is_xembed_message(&self, e: &ClientMessageEvent) -> bool {
        e.type_ == self.atoms.xembed && self.contains(e.window)
    }

    pub fn handle_xembed(&self, conn: &RustConnection, e: &ClientMessageEvent) -> Result {
        let data = e.data.as_data32();
        if data.get(1).copied() == Some(XEMBED_REQUEST_FOCUS) {
            self.focus_icon(conn, e.window)?;
        }
        Ok(())
    }

    /// ICCCM requires a reply even for manager selections that carry no data.
    pub fn selection_request(&self, conn: &RustConnection, e: &SelectionRequestEvent) -> Result {
        if e.selection != self.selection {
            return Ok(());
        }
        let property = if e.target == self.atoms.targets {
            conn.change_property32(
                PropMode::REPLACE,
                e.requestor,
                e.property,
                AtomEnum::ATOM,
                &[self.atoms.targets],
            )?;
            e.property
        } else {
            NONE
        };
        let notify = SelectionNotifyEvent {
            response_type: SELECTION_NOTIFY_EVENT,
            sequence: 0,
            time: e.time,
            requestor: e.requestor,
            selection: e.selection,
            target: e.target,
            property,
        };
        conn.send_event(false, e.requestor, EventMask::NO_EVENT, notify)?;
        Ok(())
    }

    /// Returns icons to the root before the tray disappears. Destroying the
    /// tray window also destroys all of its children, which used to kill apps
    /// like Discord with `GdkWindow ... unexpectedly destroyed` on WM restart.
    pub fn release(&mut self, conn: &RustConnection) {
        let tray_pos = conn
            .get_geometry(self.window)
            .ok()
            .and_then(|c| c.reply().ok())
            .map(|g| (g.x, g.y))
            .unwrap_or((0, 0));
        for icon in &self.icons {
            let pos = conn
                .get_geometry(icon.win)
                .ok()
                .and_then(|c| c.reply().ok())
                .map(|g| (tray_pos.0 + g.x, tray_pos.1 + g.y))
                .unwrap_or(tray_pos);
            let _ = conn.reparent_window(icon.win, self.root, pos.0, pos.1);
            if icon.mapped && icon.visible {
                let _ = conn.map_window(icon.win);
            } else {
                let _ = conn.unmap_window(icon.win);
            }
        }
        self.icons.clear();
        self.owns_selection = false;
    }

    pub fn destroy(&mut self, conn: &RustConnection) {
        self.release(conn);
        let _ = conn.set_selection_owner(NONE, self.selection, CURRENT_TIME);
        if self.colormap != 0 {
            let _ = conn.free_colormap(self.colormap);
            self.colormap = 0;
        }
        let _ = conn.destroy_window(self.window);
        self.window = 0;
    }

    fn xembed_mapped(&self, conn: &RustConnection, win: Window) -> Option<bool> {
        conn.get_property(
            false,
            win,
            self.atoms.xembed_info,
            self.atoms.xembed_info,
            0,
            2,
        )
        .ok()?
        .reply()
        .ok()?
        .value32()
        .and_then(|mut values| values.nth(1))
        .map(|flags| flags & XEMBED_MAPPED != 0)
    }

    fn send(
        &self,
        conn: &RustConnection,
        win: Window,
        message: u32,
        detail: u32,
        data1: u32,
        data2: u32,
    ) {
        let ev = ClientMessageEvent::new(
            32,
            win,
            self.atoms.xembed,
            [CURRENT_TIME, message, detail, data1, data2],
        );
        let _ = conn.send_event(false, win, EventMask::NO_EVENT, ev);
    }
}

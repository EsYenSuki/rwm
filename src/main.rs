use std::error::Error;
use std::process::Command;

use x11rb::connection::Connection;
use x11rb::protocol::randr;
use x11rb::protocol::xproto::{
    ChangeWindowAttributesAux, ConfigureWindowAux, ConnectionExt, EventMask, InputFocus, Window,
};
use x11rb::protocol::Event;
use x11rb::rust_connection::RustConnection;
use x11rb::CURRENT_TIME;

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

#[derive(Clone, Copy, Debug)]
struct Rect {
    x: i32,
    y: i32,
    w: u32,
    h: u32,
}

impl Rect {
    fn contains(&self, px: i32, py: i32) -> bool {
        px >= self.x
            && py >= self.y
            && px < self.x + self.w as i32
            && py < self.y + self.h as i32
    }

    fn split(self, side_by_side: bool) -> (Rect, Rect) {
        if side_by_side {
            let w1 = self.w / 2;
            (
                Rect { w: w1, ..self },
                Rect { x: self.x + w1 as i32, w: self.w - w1, ..self },
            )
        } else {
            let h1 = self.h / 2;
            (
                Rect { h: h1, ..self },
                Rect { y: self.y + h1 as i32, h: self.h - h1, ..self },
            )
        }
    }
}

enum Node {
    Leaf(Window),
    Split {
        side_by_side: bool,
        first: Box<Node>,
        second: Box<Node>,
    },
}

impl Node {
    fn layout(&self, rect: Rect, out: &mut Vec<(Window, Rect)>) {
        match self {
            Node::Leaf(win) => out.push((*win, rect)),
            Node::Split { side_by_side, first, second } => {
                let (a, b) = rect.split(*side_by_side);
                first.layout(a, out);
                second.layout(b, out);
            }
        }
    }

    /// Replaces the leaf `target` with a split holding `target` and `new`.
    fn insert(&mut self, target: Window, new: Window, new_first: bool, side_by_side: bool) -> bool {
        if let Node::Split { first, second, .. } = self {
            return first.insert(target, new, new_first, side_by_side)
                || second.insert(target, new, new_first, side_by_side);
        }
        let Node::Leaf(w) = *self else { return false };
        if w != target {
            return false;
        }
        let (first, second) = if new_first {
            (Node::Leaf(new), Node::Leaf(w))
        } else {
            (Node::Leaf(w), Node::Leaf(new))
        };
        *self = Node::Split {
            side_by_side,
            first: Box::new(first),
            second: Box::new(second),
        };
        true
    }

    /// Removes the leaf `target`; its sibling takes over the whole parent area.
    fn remove(self, target: Window) -> Option<Node> {
        match self {
            Node::Leaf(w) => (w != target).then_some(Node::Leaf(w)),
            Node::Split { side_by_side, first, second } => {
                match ((*first).remove(target), (*second).remove(target)) {
                    (Some(a), Some(b)) => Some(Node::Split {
                        side_by_side,
                        first: Box::new(a),
                        second: Box::new(b),
                    }),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                }
            }
        }
    }
}

struct Monitor {
    rect: Rect,
    tree: Option<Node>,
}

impl Monitor {
    fn leaves(&self) -> Vec<(Window, Rect)> {
        let mut out = Vec::new();
        if let Some(tree) = &self.tree {
            tree.layout(self.rect, &mut out);
        }
        out
    }
}

struct Wm {
    conn: RustConnection,
    root: Window,
    monitors: Vec<Monitor>,
}

impl Wm {
    fn leaves(&self) -> Vec<(Window, Rect)> {
        self.monitors.iter().flat_map(|m| m.leaves()).collect()
    }

    fn is_managed(&self, win: Window) -> bool {
        self.leaves().iter().any(|(w, _)| *w == win)
    }

    /// The monitor under (x, y), falling back to the first monitor.
    fn monitor_at(&self, x: i32, y: i32) -> usize {
        self.monitors
            .iter()
            .position(|m| m.rect.contains(x, y))
            .unwrap_or(0)
    }

    fn manage(&mut self, win: Window) -> Result {
        let pointer = self.conn.query_pointer(self.root)?.reply()?;
        let (mx, my) = (pointer.root_x as i32, pointer.root_y as i32);

        let idx = self.monitor_at(mx, my);
        let monitor = &mut self.monitors[idx];
        let leaves = monitor.leaves();
        match leaves
            .iter()
            .copied()
            .find(|(_, r)| r.contains(mx, my))
            .or(leaves.last().copied())
        {
            None => monitor.tree = Some(Node::Leaf(win)),
            Some((target, rect)) => {
                let side_by_side = rect.w > rect.h;
                let new_first = if side_by_side {
                    mx < rect.x + (rect.w / 2) as i32
                } else {
                    my < rect.y + (rect.h / 2) as i32
                };
                if let Some(tree) = monitor.tree.as_mut() {
                    tree.insert(target, win, new_first, side_by_side);
                }
            }
        }

        self.conn.change_window_attributes(
            win,
            &ChangeWindowAttributesAux::new().event_mask(EventMask::ENTER_WINDOW),
        )?;
        self.apply_layout()?;
        self.conn.map_window(win)?;
        self.conn
            .set_input_focus(InputFocus::POINTER_ROOT, win, CURRENT_TIME)?;
        self.conn.flush()?;
        Ok(())
    }

    fn unmanage(&mut self, win: Window) -> Result {
        let Some(monitor) = self.monitors.iter_mut().find(|m| {
            m.leaves().iter().any(|(w, _)| *w == win)
        }) else {
            return Ok(());
        };
        monitor.tree = monitor.tree.take().and_then(|t| t.remove(win));
        self.apply_layout()
    }

    fn apply_layout(&self) -> Result {
        for (win, r) in self.leaves() {
            self.conn.configure_window(
                win,
                &ConfigureWindowAux::new()
                    .x(r.x)
                    .y(r.y)
                    .width(r.w)
                    .height(r.h),
            )?;
        }
        self.conn.flush()?;
        Ok(())
    }

    fn handle(&mut self, event: Event) -> Result {
        match event {
            Event::MapRequest(e) => {
                if self.is_managed(e.window) {
                    self.conn.map_window(e.window)?;
                } else {
                    self.manage(e.window)?;
                }
            }
            Event::UnmapNotify(e) => self.unmanage(e.window)?,
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
                if self.is_managed(e.event) {
                    self.conn
                        .set_input_focus(InputFocus::POINTER_ROOT, e.event, CURRENT_TIME)?;
                    self.conn.flush()?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

fn monitor_rects(conn: &RustConnection, root: Window, screen: Rect) -> Result<Vec<Rect>> {
    let reply = randr::get_monitors(conn, root, true)?.reply()?;
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

fn main() -> Result {
    let (conn, screen_num) = x11rb::connect(None)?;
    let (root, width, height) = {
        let s = &conn.setup().roots[screen_num];
        (s.root, s.width_in_pixels, s.height_in_pixels)
    };

    conn.change_window_attributes(
        root,
        &ChangeWindowAttributesAux::new().event_mask(
            EventMask::SUBSTRUCTURE_REDIRECT | EventMask::SUBSTRUCTURE_NOTIFY,
        ),
    )?
    .check()?;

    let screen = Rect { x: 0, y: 0, w: width as u32, h: height as u32 };
    let monitors = monitor_rects(&conn, root, screen)?
        .into_iter()
        .map(|rect| Monitor { rect, tree: None })
        .collect();

    let mut wm = Wm { conn, root, monitors };

    // Each argument is a shell command started at launch, e.g. `rwm xterm "firefox"`.
    for cmd in std::env::args().skip(1) {
        Command::new("sh").arg("-c").arg(&cmd).spawn()?;
    }

    loop {
        let event = wm.conn.wait_for_event()?;
        wm.handle(event)?;
    }
}

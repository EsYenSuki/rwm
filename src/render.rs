//! Drawing thread for the bar windows. The window manager builds a `Frame`
//! from its state and sends it here, so GL drawing and buffer swaps never block
//! event handling or pointer drags.

use std::sync::mpsc::{self, Sender};
use std::thread;
use std::time::{Duration, Instant};

use x11rb::connection::Connection;
use x11rb::protocol::xproto::{ConfigureWindowAux, ConnectionExt, CreateGCAux, ImageFormat, Window};
use x11rb::rust_connection::RustConnection;

use crate::bar::{Gl, LAYOUT_SYMBOL, Metrics};
use crate::mpris::Snapshot;
use crate::soft;

/// Shortest time between two clock redraws, so the clock thread runs at 50 fps.
const CLOCK_FRAME: Duration = Duration::from_millis(20);

pub struct Frame {
    pub monitors: Vec<MonitorBar>,
}

pub struct MonitorBar {
    pub tags: TagsBar,
    pub title: TitleBar,
    pub kb: TextBar,
    pub right: RightBar,
}

pub struct TagsBar {
    pub win: Window,
    pub w: i32,
    pub occupied: u32,
    pub selected: u32,
}

pub struct TitleBar {
    pub win: Window,
    pub w: i32,
    pub name: Option<String>,
    pub focused: bool,
}

pub struct TextBar {
    pub win: Window,
    pub w: i32,
    pub text: String,
    pub focused: bool,
}

pub enum RightBar {
    Status {
        win: Window,
        w: i32,
        text: String,
        scroll: u32,
        progress: Option<f32>,
    },
    Panel {
        win: Window,
        w: i32,
        text: String,
        player: Snapshot,
        scroll: u32,
        marker_hovered: bool,
    },
}

pub struct Renderer {
    tx: Sender<Frame>,
}

impl Renderer {
    pub fn submit(&self, frame: Frame) {
        let _ = self.tx.send(frame);
    }
}

/// A clock window with the place it goes and the text it shows.
pub struct ClockBar {
    pub win: Window,
    pub x: i32,
    pub y: i32,
    pub w: i32,
    pub text: String,
    pub focused: bool,
}

/// Sends the clock windows to the clock thread, which draws them at 50 fps.
pub struct ClockRenderer {
    tx: Sender<Vec<ClockBar>>,
}

impl ClockRenderer {
    pub fn submit(&self, bars: Vec<ClockBar>) {
        let _ = self.tx.send(bars);
    }
}

/// Starts the clock thread. It draws on the CPU and puts the pixels into the
/// windows with its own X connection, so the clock never touches GL. Each
/// window's move and resize go in the same request batch as its pixels.
pub fn spawn_clock(depth: u8) -> ClockRenderer {
    let (tx, rx) = mpsc::channel::<Vec<ClockBar>>();
    thread::spawn(move || {
        let metrics = match Metrics::open() {
            Ok(metrics) => metrics,
            Err(err) => return eprintln!("clock thread: {err}"),
        };
        let Ok((conn, _)) = RustConnection::connect(None) else {
            return eprintln!("clock thread: X connection failed");
        };
        let mut gc = None;
        let mut last = Instant::now();
        while let Ok(mut bars) = rx.recv() {
            thread::sleep(CLOCK_FRAME.saturating_sub(last.elapsed()));
            while let Ok(newer) = rx.try_recv() {
                bars = newer;
            }
            last = Instant::now();
            for b in &bars {
                let canvas = soft::clock(&metrics, b.w, &b.text, b.focused);
                let (w, h) = (canvas.w as u16, canvas.h as u16);
                let _ = conn.configure_window(
                    b.win,
                    &ConfigureWindowAux::new().x(b.x).y(b.y).width(w as u32).height(h as u32),
                );
                let gc = match gc {
                    Some(gc) => gc,
                    None => {
                        let id = conn.generate_id().unwrap_or(0);
                        if conn.create_gc(id, b.win, &CreateGCAux::new()).is_ok() {
                            gc = Some(id);
                        }
                        id
                    }
                };
                let _ = conn.put_image(
                    ImageFormat::Z_PIXMAP,
                    b.win,
                    gc,
                    w,
                    h,
                    0,
                    0,
                    0,
                    depth,
                    &canvas.into_bytes(),
                );
            }
            let _ = conn.flush();
        }
    });
    ClockRenderer { tx }
}

/// Starts the drawing thread, which takes over the GL context of `gl`.
pub fn spawn(gl: Gl) -> Renderer {
    gl.release_current();
    let (tx, rx) = mpsc::channel::<Frame>();
    thread::spawn(move || {
        while let Ok(mut frame) = rx.recv() {
            // Only the newest frame is worth drawing; skip the ones queued behind it.
            while let Ok(newer) = rx.try_recv() {
                frame = newer;
            }
            draw(&gl, &frame);
        }
    });
    Renderer { tx }
}

fn draw(gl: &Gl, frame: &Frame) {
    for m in &frame.monitors {
        gl.draw_tags(m.tags.win, m.tags.w.max(1), m.tags.occupied, m.tags.selected, LAYOUT_SYMBOL);
        gl.draw_title(m.title.win, m.title.w.max(1), m.title.name.as_deref(), m.title.focused);
        gl.draw_kb(m.kb.win, m.kb.w.max(1), &m.kb.text, m.kb.focused);
        match &m.right {
            RightBar::Status { win, w, text, scroll, progress } => {
                gl.draw_status(*win, (*w).max(1), text, *scroll, *progress);
            }
            RightBar::Panel { win, w, text, player, scroll, marker_hovered } => {
                gl.draw_mpris_panel(*win, (*w).max(1), text, player, *scroll, *marker_hovered);
            }
        }
    }
}

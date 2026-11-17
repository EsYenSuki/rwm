mod bar;
mod config;
mod keys;
mod mpris;
mod render;
mod soft;
mod sound;
mod status;
mod text;
mod tree;
mod wm;

use std::env;
use std::error::Error;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::thread;
use std::time::Duration;

use x11rb::connection::Connection;
use x11rb::protocol::randr;
use x11rb::protocol::xproto::Window;
use x11rb::rust_connection::RustConnection;

use tree::Rect;
use wm::Wm;

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

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
    // The render thread and the window manager each use Xlib displays.
    unsafe {
        x11::xlib::XInitThreads();
    }
    let (conn, screen_num) = x11rb::connect(None)?;
    let (root, width, height, min_kc, max_kc) = {
        let setup = conn.setup();
        let s = &setup.roots[screen_num];
        (
            s.root,
            s.width_in_pixels,
            s.height_in_pixels,
            setup.min_keycode,
            setup.max_keycode,
        )
    };

    let screen = Rect { x: 0, y: 0, w: width as u32, h: height as u32 };
    let rects = monitor_rects(&conn, root, screen)?;
    let mut wm = Wm::new(conn, root, rects, min_kc, max_kc)?;

    // Each argument is a shell command started at launch, e.g. `rwm xterm "firefox"`.
    for cmd in env::args().skip(1) {
        wm::spawn(&cmd)?;
    }

    let mut dirty = true;
    loop {
        while let Some(event) = wm.conn.poll_for_event()? {
            wm.handle(event)?;
            dirty = true;
        }
        if wm.restart {
            let exe = env::current_exe()?;
            let err = Command::new(exe).args(env::args().skip(1)).exec();
            return Err(err.into());
        }
        wm.refresh(dirty)?;
        dirty = false;
        thread::sleep(Duration::from_millis(20));
    }
}

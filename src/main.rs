mod bar;
mod config;
mod drw;
mod egl;
mod finder;
mod finder_math;
mod finder_net;
mod gl;
mod keys;
mod mpris;
mod notification;
mod sound;
mod status;
mod text;
mod tray;
mod tree;
mod wm;

use std::env;
use std::error::Error;
use std::os::unix::process::CommandExt;
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use x11rb::connection::Connection;
use x11rb::protocol::randr;
use x11rb::protocol::xproto::Window;
use x11rb::rust_connection::RustConnection;

use tree::Rect;
use wm::Wm;

type Result<T = ()> = std::result::Result<T, Box<dyn Error>>;

/// `kill rwm` (SIGTERM), Ctrl-C, or a hung-up terminal must unwind through
/// `Drop`: destroying the tray window also destroys every embedded icon, which
/// crashes apps like Discord when their GdkWindow disappears underneath them.
/// Signals do not run destructors, so flag the request and let the main loop
/// call `shutdown()` (via `Drop`) before exiting.
static SHUTDOWN_REQUESTED: AtomicBool = AtomicBool::new(false);

extern "C" fn on_shutdown_signal(_: libc::c_int) {
    SHUTDOWN_REQUESTED.store(true, Ordering::SeqCst);
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
    // One Xlib display serves cursors, fonts and all drawing. x11rb handles
    // window management on its own connection, as in AnDWM's single `dpy`.
    unsafe {
        x11::xlib::XInitThreads();
        for sig in [libc::SIGTERM, libc::SIGINT, libc::SIGHUP] {
            libc::signal(sig, on_shutdown_signal as libc::sighandler_t);
        }
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

    let screen = Rect {
        x: 0,
        y: 0,
        w: width as u32,
        h: height as u32,
    };
    let rects = monitor_rects(&conn, root, screen)?;
    let mut wm = Wm::new(conn, root, rects, min_kc, max_kc)?;
    // `next_tick()` returns a deadline relative to the moment it is called, so
    // keep the one computed after the last refresh instead of asking again at
    // the top of every loop. Otherwise the BAR_TICK deadline is always 16 ms in
    // the future and only the stale 1 s status deadline can trigger a refresh.
    let mut next_refresh = wm.next_tick();

    // Each argument is a shell command started at launch, e.g. `rwm xterm "firefox"`.
    for cmd in env::args().skip(1) {
        wm::spawn(&cmd)?;
    }

    loop {
        // A signal interrupts poll() with EINTR; check the flag on every turn
        // so Drop can reparent tray icons back to root before the connection
        // closes. Without this, `kill rwm` would strand them in the tray window.
        if SHUTDOWN_REQUESTED.load(Ordering::SeqCst) {
            break;
        }
        while let Some(event) = wm.conn.poll_for_event()? {
            wm.handle(event)?;
        }
        // Pointer crossings, fullscreen toggles and tag changes can all change
        // whether the pointer's monitor is fullscreen. Apply that before the
        // refresh/deadline check so the 60 fps bar tick stops or resumes on the
        // same loop iteration as the event, not a tick later.
        wm.sync_bar_suspended();
        if wm.restart {
            // exec() does not run Drop, so release grabs and bar windows first.
            wm.shutdown();
            let exe = env::current_exe()?;
            let err = Command::new(exe).args(env::args().skip(1)).exec();
            return Err(err.into());
        }
        if wm.finder_active()
            || wm.needs_refresh()
            || next_refresh.saturating_duration_since(Instant::now()).is_zero()
        {
            wm.refresh()?;
            next_refresh = wm.next_tick();
        }
        // All animated bar values advance on the single deadline refresh()
        // just computed. Block on the X connection until then or an event.
        wm.wait_event(next_refresh.saturating_duration_since(Instant::now()))?;
    }
    Ok(())
}

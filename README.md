# rwm

`rwm` is an experimental X11 window manager written in Rust. It is heavily
inspired by dwm and AnDWM: tags instead of workspaces, keyboard-driven window
management, a small status bar and no config file parser.

**This is work in progress.** It is a playground for trying out ideas, not a
stable daily-driver WM. Things may break, change or disappear without notice.

## What's in it right now

- Tree-based tiling layout with resizable splits, gaps and floating windows.
- Multiple monitors via RandR, with tags and focus per monitor.
- A bar with status information (battery, CPU, memory, Wi-Fi, playing track),
  an MPRIS media section, a system tray and a PipeWire audio visualizer.
- Desktop notifications.
- An application finder/launcher popup, with an OCR variant.
- Drawing through OpenGL/EGL with XRender/Xlib fallbacks for the bar and icons.
- dwm-style keybindings: `Super` is the main modifier, `Super+1..5` views tags,
  `Super+Shift+1..5` tags windows, `Super+Return` opens a terminal,
  `Super+j/k` changes focus, `Super+q` closes a window, `Super+Shift+r`
  restarts. Some media and brightness keys are bound too.

See `src/keys.rs` for the full, current keymap.

## Building and running

Requires a Rust toolchain and X11 development libraries (Xlib, Xft, XRender,
RandR, XKB, XCursor), FreeType, OpenGL/EGL, PipeWire and D-Bus.

```sh
cargo build --release
./target/release/rwm
```

Any command-line arguments are started as programs at launch, for example:

```sh
./target/release/rwm "kitty -1" "firefox"
```

## Configuration

There is no runtime config format yet. Change values in `src/config.rs` and
bindings in `src/keys.rs`, then rebuild. Some bindings still point to this
machine's scripts and applications; adjust them for your system.

## Status

Features are added as experiments and refined only when they prove useful.
Expect rough edges in the bar, layout behavior, EGL paths and error handling.
Bug reports and ideas are welcome, but please treat this as an unfinished
project.

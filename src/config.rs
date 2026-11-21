//! Layout settings, named after AnDWM's config.def.h. Edit and rebuild.

/// config.def.h `floatbar`: the bar floats inside the outer gap.
pub const FLOATBAR: bool = true;
/// Float windows whose `WM_NORMAL_HINTS` pin both axes to one size (min == max).
/// EWMH dialog types already float; this is the fallback for clients that
/// publish no window type but are unresizable, such as updater popups. No app
/// names are involved, so any client with the same hints gets the same rule.
pub const FLOAT_FIXED_SIZE: bool = true;
/// config.def.h `topbar`.
pub const TOPBAR: bool = true;
/// Attempt a 32-bit ARGB visual (with an XRender alpha mask) for the center
/// clock bar window, as dwm does for its finder popup. Set to `false` to force
/// the default root visual everywhere; the same fallback is used automatically
/// when the server has no ARGB visual or rejects its creation.
pub const FINDER_ARGB: bool = true;
/// config.h `finder_width`: popup width in pixels.
pub const FINDER_WIDTH: i32 = 300;
/// config.h `finder_rows`: maximum number of visible application rows.
pub const FINDER_ROWS: usize = 10;
/// dwm.c `FINDER_MARKER_WIDTH`: width of the separate white selection marker.
pub const FINDER_MARKER_WIDTH: i32 = 270;
/// config.h `finder_app_dirs`: scanned in this order, non-recursively.
pub const FINDER_APP_DIRS: &[&str] = &[
    "~/.local/share/applications",
    "/usr/local/share/applications",
    "/usr/share/applications",
    "~/.local/share/flatpak/exports/share/applications",
    "/var/lib/flatpak/exports/share/applications",
];
/// config.def.h `smartgaps`: no outer gap when a monitor shows one window.
pub const SMARTGAPS: bool = false;

/// config.def.h `gappih`: gap between windows stacked top and bottom.
pub const GAPPIH: i32 = 14;
/// config.def.h `gappiv`: gap between windows placed side by side.
pub const GAPPIV: i32 = 14;
/// config.def.h `gappoh`: top and bottom margin to the screen edge.
pub const GAPPOH: i32 = 14;
/// config.def.h `gappov`: left and right margin to the screen edge.
pub const GAPPOV: i32 = 14;

/// config.def.h `borderpx`: border width of windows and the bar.
pub const BORDERPX: i32 = 2;
/// Width of the band along each window edge where hovering shows a resize
/// cursor and a plain left click starts a resize.
pub const RESIZE_EDGE_PX: i32 = 2;

/// Hyprland `dwindle:split_width_multiplier`: a tile splits left/right when its
/// width is greater than its height times this value. The default is 1.0.
pub const DWINDLE_SPLIT_WIDTH_MULTIPLIER: f64 = 1.0;
/// First child's share of a new dwindle split. Hyprland's default
/// `dwindle:default_split_ratio` is 1.0, which makes the first child
/// `box.w / 2 * 1.0`, i.e. half the box.
pub const DWINDLE_DEFAULT_SPLIT_SHARE: f64 = 0.5;
/// config.def.h `colors[SchemeNorm][ColBorder]`: border of unfocused windows.
pub const COL_NORM_BORDER: u32 = 0x27372d;
/// config.def.h `colors[SchemeSel][ColBorder]`: border of the focused window.
pub const COL_SEL_BORDER: u32 = 0x94E2D5;

/// dwm.c `CLOCK_ANIMATE`: the clock bar grows with the audio peak. 0 disables it.
pub const CLOCK_ANIMATE: bool = true;
/// dwm.c `CLOCK_ANIM_EXTRA`: most px the clock bar grows past its text width.
pub const CLOCK_ANIM_EXTRA: i32 = 280;
/// Peaks below this are treated as silence, so monitor noise cannot make the
/// clock bar animate while nothing is playing.
pub const CLOCK_PEAK_EPSILON: f32 = 0.02;
/// Clock animation widths are quantized to this many pixels. Fewer, larger
/// resizes mean fewer damaged regions for the compositor to repaint.
pub const CLOCK_ANIM_STEP: i32 = 4;
/// dwm.c `PW_MONITOR_SINK`: capture system output (true) or the microphone (false).
pub const PW_MONITOR_SINK: bool = true;

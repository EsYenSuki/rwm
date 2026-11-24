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
/// Keep menus and popups opened from a system-tray icon stacked above the bar.
/// Without this, raising the always-on-top bar layer buries the menu a tray
/// app just mapped, so its top rows are hidden behind the tray it came from.
pub const TRAY_MENUS_ABOVE_BAR: bool = true;
/// Attempt a 32-bit ARGB visual (with an XRender alpha mask) for the center
/// clock bar window, as dwm does for its finder popup. Set to `false` to force
/// the default root visual everywhere; the same fallback is used automatically
/// when the server has no ARGB visual or rejects its creation.
pub const FINDER_ARGB: bool = true;
/// Allow the EGL readback fallback when the driver accepts pixmap surfaces but
/// does not publish their pixels to XRender. `0` forces the zero-copy path so
/// EGL can be tested on its own; `1` restores the XImage upload fallback for
/// software drivers such as Mesa on Xvfb.
pub const EGL_FALLBACK: u8 = 0;
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

/// dwm.c `CLOCK_ANIMATE`: the clock bar grows with the audio level. 0 disables it.
pub const CLOCK_ANIMATE: bool = true;
/// dwm.c `CLOCK_ANIM_EXTRA`: most px the clock bar grows past its text width.
pub const CLOCK_ANIM_EXTRA: i32 = 100;
/// Adaptive RMS normalization: target output RMS. Gain is adjusted so a quiet
/// or loud source still lands near this level, which keeps the bar useful
/// without touching playback audio.
pub const CLOCK_RMS_TARGET: f32 = 0.08;
/// Gain bounds for the visualizer only. 100 is +40 dB.
pub const CLOCK_GAIN_MIN: f32 = 0.01;
pub const CLOCK_GAIN_MAX: f32 = 100.0;
/// Denominator floor when computing gain, plus the gate below which gain is
/// held instead of boosted (so silence/noise is not amplified).
pub const CLOCK_RMS_FLOOR: f32 = 0.001;
pub const CLOCK_RMS_GATE: f32 = 0.0008;
/// Gain smoothing time constant, in seconds. Long enough to track overall
/// loudness rather than each beat, so dynamics reach the bar instead of being
/// compressed away. Smoothing happens in log space.
pub const CLOCK_GAIN_ADAPT_SECS: f32 = 0.8;
/// dBFS floor of the one-bar meter. -40..0 dB maps to 0..CLOCK_ANIM_EXTRA px.
/// A narrower range leaves more pixels for the crest of each beat.
pub const CLOCK_METER_MIN_DB: f32 = -40.0;
/// Expected peak/RMS ratio of the normalized signal. Levels near this crest
/// are the visual center; expansion pushes below it down and peaks further up.
pub const CLOCK_EXPECTED_CREST: f32 = 3.0;
pub const CLOCK_DYNAMIC_EXPAND: f32 = 1.7;
/// Clock animation widths are quantized to this many pixels. Fewer, larger
/// resizes mean fewer damaged regions for the compositor to repaint.
pub const CLOCK_ANIM_STEP: i32 = 4;
/// dwm.c `PW_MONITOR_SINK`: capture system output (true) or the microphone (false).
pub const PW_MONITOR_SINK: bool = true;

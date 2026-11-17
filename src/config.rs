//! Layout settings, named after AnDWM's config.def.h. Edit and rebuild.

/// config.def.h `floatbar`: the bar floats inside the outer gap.
pub const FLOATBAR: bool = true;
/// config.def.h `topbar`.
pub const TOPBAR: bool = true;
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
/// config.def.h `colors[SchemeNorm][ColBorder]`: border of unfocused windows.
pub const COL_NORM_BORDER: u32 = 0x27372d;
/// config.def.h `colors[SchemeSel][ColBorder]`: border of the focused window.
pub const COL_SEL_BORDER: u32 = 0x94E2D5;

/// dwm.c `CLOCK_ANIMATE`: the clock bar grows with the audio peak. 0 disables it.
pub const CLOCK_ANIMATE: bool = true;
/// dwm.c `CLOCK_ANIM_EXTRA`: most px the clock bar grows past its text width.
pub const CLOCK_ANIM_EXTRA: i32 = 280;
/// dwm.c `PW_MONITOR_SINK`: capture system output (true) or the microphone (false).
pub const PW_MONITOR_SINK: bool = true;

use x11::keysym::*;

pub const MOD_SHIFT: u16 = 1 << 0;
pub const MOD_CONTROL: u16 = 1 << 2;
pub const MOD_1: u16 = 1 << 3;
pub const MOD_4: u16 = 1 << 6;

pub const TAG_COUNT: u32 = 5;
pub const TAGMASK: u32 = (1 << TAG_COUNT) - 1;

/// Which gap values an `IncrGaps` key changes, as in dwm's vanitygaps keys.
#[derive(Clone, Copy, Debug)]
pub enum GapScope {
    All,
    Inner,
    Outer,
    InnerH,
    InnerV,
    OuterH,
    OuterV,
}

#[derive(Clone, Copy, Debug)]
pub enum Action {
    View(u32),
    ToggleView(u32),
    Tag(u32),
    ToggleTag(u32),
    ViewAll,
    TagAll,
    ViewPrev,
    ShiftView(i32),
    FocusStack(i32),
    MoveStack(i32),
    Zoom,
    ToggleFloating,
    KillClient,
    ForceKillClient,
    FocusMon(i32),
    TagMon(i32),
    ToggleBar,
    ToggleGaps,
    DefaultGaps,
    IncrGaps(GapScope, i32),
    Restart,
    Spawn(&'static str),
}

#[derive(Clone, Copy, Debug)]
pub struct Key {
    pub mods: u16,
    pub keysym: u32,
    pub action: Action,
}

const TAG_KEYSYMS: [u32; 9] = [XK_1, XK_2, XK_3, XK_4, XK_5, XK_6, XK_7, XK_8, XK_9];

fn tag_keys(keys: &mut Vec<Key>) {
    // Only TAG_COUNT tags exist; Mod+6..9 are left free for the gap keys.
    for (i, &sym) in TAG_KEYSYMS.iter().take(TAG_COUNT as usize).enumerate() {
        let bit = 1u32 << i;
        keys.push(Key { mods: MOD_4, keysym: sym, action: Action::View(bit) });
        keys.push(Key { mods: MOD_4 | MOD_CONTROL, keysym: sym, action: Action::ToggleView(bit) });
        keys.push(Key { mods: MOD_4 | MOD_SHIFT, keysym: sym, action: Action::Tag(bit) });
        keys.push(Key {
            mods: MOD_4 | MOD_CONTROL | MOD_SHIFT,
            keysym: sym,
            action: Action::ToggleTag(bit),
        });
    }
}

const TOGGLE_KB: &str = "setxkbmap -layout us,th -option grp:win_space_toggle";

/// Bindings in dwm config.def.h order. Every matching binding runs, as in dwm.
pub fn bindings() -> Vec<Key> {
    use Action::*;
    let mut k = vec![
        Key { mods: 0, keysym: XF86XK_AudioLowerVolume, action: Spawn("/usr/bin/pactl set-sink-volume 0 -5%") },
        Key { mods: 0, keysym: XF86XK_AudioMute, action: Spawn("/usr/bin/pactl set-sink-mute 0 toggle") },
        Key { mods: 0, keysym: XF86XK_AudioRaiseVolume, action: Spawn("/usr/bin/pactl set-sink-volume 0 +5%") },
        Key { mods: 0, keysym: XF86XK_MonBrightnessUp, action: Spawn("/usr/bin/light -A 5") },
        Key { mods: 0, keysym: XF86XK_MonBrightnessDown, action: Spawn("/usr/bin/light -U 5") },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_s, action: Spawn("/home/hi/.config/AnDWM/scripts/bin/znap") },
        Key { mods: MOD_4, keysym: XK_v, action: Spawn("/home/hi/.config/AnDWM/scripts/bin/clyp") },
        Key { mods: MOD_4, keysym: XK_Return, action: Spawn("kitty") },
        Key { mods: MOD_4, keysym: XK_e, action: Spawn("nemo") },
        Key { mods: MOD_4, keysym: XK_b, action: Spawn("MOZ_X11_EGL=1 MOZ_USE_XINPUT2=1 zen-browser") },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_c, action: Spawn("picom cursor toggle") },
        Key { mods: MOD_4, keysym: XK_equal, action: Spawn("picom-zoom +0.2") },
        Key { mods: MOD_4, keysym: XK_minus, action: Spawn("picom-zoom -0.2") },
        Key { mods: MOD_4, keysym: XK_BackSpace, action: Spawn("picom-zoom 1") },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_equal, action: Spawn("picom-zoom +0.4") },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_minus, action: Spawn("picom-zoom -0.4") },
        Key { mods: MOD_4, keysym: XK_space, action: Spawn(TOGGLE_KB) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_b, action: ToggleBar },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_t, action: ToggleGaps },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_i, action: IncrGaps(GapScope::All, 1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_d, action: IncrGaps(GapScope::All, -1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_i, action: IncrGaps(GapScope::Inner, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_i, action: IncrGaps(GapScope::Inner, -1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_o, action: IncrGaps(GapScope::Outer, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_o, action: IncrGaps(GapScope::Outer, -1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_6, action: IncrGaps(GapScope::InnerH, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_6, action: IncrGaps(GapScope::InnerH, -1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_7, action: IncrGaps(GapScope::InnerV, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_7, action: IncrGaps(GapScope::InnerV, -1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_8, action: IncrGaps(GapScope::OuterH, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_8, action: IncrGaps(GapScope::OuterH, -1) },
        Key { mods: MOD_4 | MOD_CONTROL, keysym: XK_9, action: IncrGaps(GapScope::OuterV, 1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_9, action: IncrGaps(GapScope::OuterV, -1) },
        Key { mods: MOD_4 | MOD_CONTROL | MOD_SHIFT, keysym: XK_d, action: DefaultGaps },
        Key { mods: MOD_4, keysym: XK_j, action: FocusStack(1) },
        Key { mods: MOD_4, keysym: XK_k, action: FocusStack(-1) },
        Key { mods: MOD_4, keysym: XK_Left, action: ShiftView(-1) },
        Key { mods: MOD_4, keysym: XK_Right, action: ShiftView(1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_j, action: MoveStack(1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_k, action: MoveStack(-1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_Return, action: Zoom },
        Key { mods: MOD_4, keysym: XK_w, action: ToggleFloating },
        Key { mods: MOD_4, keysym: XK_Tab, action: ViewPrev },
        Key { mods: MOD_1, keysym: XK_Tab, action: FocusStack(1) },
        Key { mods: MOD_1 | MOD_SHIFT, keysym: XK_Tab, action: FocusStack(-1) },
        Key { mods: MOD_4, keysym: XK_0, action: ViewAll },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_0, action: TagAll },
        Key { mods: MOD_4, keysym: XK_comma, action: FocusMon(-1) },
        Key { mods: MOD_4, keysym: XK_period, action: FocusMon(1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_comma, action: TagMon(-1) },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_period, action: TagMon(1) },
        Key { mods: MOD_4, keysym: XK_q, action: KillClient },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_q, action: ForceKillClient },
        Key { mods: MOD_4 | MOD_SHIFT, keysym: XK_r, action: Restart },
    ];
    tag_keys(&mut k);
    k
}

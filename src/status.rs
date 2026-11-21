use std::fs;
use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Instant;

use crate::bar::col;

#[derive(Debug, Clone, PartialEq)]
pub enum StatusToken {
    Text(String),
    ScrollText(String),
    Fg([f32; 4]),
    Bg([f32; 4]),
    Reset,
    Forward(i32),
    Rect(i32, i32, u32, u32),
}

/// One painted run of the status bar: a string and the two colors it is drawn
/// with. Layout and color decisions live in `Status::runs`, so the renderer
/// never has to interpret markup characters to know what to draw.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatusRun {
    pub text: String,
    pub fg: u32,
    pub bg: u32,
    /// Draw with the animated, clipped scroll field instead of plain text.
    pub scroll: bool,
}

/// The top-right bar's state as typed values. Icons are derived from the
/// readings and only change when the underlying state changes; the text
/// values are the parts that get re-polled. Nothing here is a markup string.
#[derive(Debug, Clone)]
pub struct Status {
    /// Custom root-window text. When set it replaces the built-in cells.
    pub custom: Option<String>,
    /// Scrolling title while a player is playing, empty otherwise.
    pub playing: Option<String>,
    pub battery_icon: &'static str,
    pub battery_percent: i32,
    pub cpu_percent: f32,
    pub mem_icon: &'static str,
    pub mem_text: String,
    pub mem_warn: bool,
    pub wifi_icon: &'static str,
    pub wifi_text: String,
}

impl Status {
    /// Value used by the bar cache. Only the polled values appear here, so a
    /// stable idle reading keeps the right window untouched.
    pub fn key(&self) -> String {
        if let Some(custom) = &self.custom {
            return format!("custom:{custom}");
        }
        format!(
            "{}:{}:{}:{}:{}:{}:{}:{}:{}",
            self.playing.as_deref().unwrap_or(""),
            self.battery_icon,
            self.battery_percent,
            self.cpu_percent,
            self.mem_icon,
            self.mem_text,
            self.mem_warn,
            self.wifi_icon,
            self.wifi_text,
        )
    }

    /// The status cells in the exact dwm left-to-right order. Each run carries
    /// its own foreground and background, so the drawn pixels are fully
    /// described here with no `^c`/`^b` markup in between. `scroll` marks the
    /// animated MPRIS field, which the renderer clips and advances itself.
    pub fn runs(&self) -> Vec<StatusRun> {
        const SAV: u32 = 0xa6e3a1;
        const BAT: u32 = 0x96cdfb;
        const DIM: u32 = 0x1e1d2d;
        const VAL: u32 = 0xd9e0ee;
        const NORM: u32 = 0x585767;
        const CPU_BG: u32 = 0xa6e3a1;
        const VAL_BG: u32 = 0x282737;
        const WIFI_BG: u32 = 0x96cdfb;
        const PLAY_BG: u32 = 0xb8e9b4;
        let mem_fg = if self.mem_warn { 0xed8796 } else { DIM };

        if let Some(playing) = &self.playing {
            let runs = vec![
                StatusRun {
                    text: String::new(),
                    fg: SAV,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: SAV,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: DIM,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: " 󰎆".into(),
                    fg: DIM,
                    bg: PLAY_BG,
                    scroll: false,
                },
                StatusRun {
                    text: format!(" {playing}"),
                    fg: DIM,
                    bg: PLAY_BG,
                    scroll: true,
                },
                StatusRun {
                    text: " ".into(),
                    fg: mem_fg,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: format!(" {}", self.mem_icon),
                    fg: mem_fg,
                    bg: WIFI_BG,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: mem_fg,
                    bg: WIFI_BG,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: DIM,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: format!(" {}", self.wifi_icon),
                    fg: DIM,
                    bg: WIFI_BG,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: DIM,
                    bg: WIFI_BG,
                    scroll: false,
                },
                StatusRun {
                    text: format!(" {}", self.battery_icon),
                    fg: BAT,
                    bg: DIM,
                    scroll: false,
                },
                StatusRun {
                    text: " ".into(),
                    fg: BAT,
                    bg: DIM,
                    scroll: false,
                },
            ];
            return runs;
        }

        vec![
            StatusRun {
                text: "  ".into(),
                fg: SAV,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: self.battery_icon.into(),
                fg: BAT,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: format!(" {}%", self.battery_percent),
                fg: BAT,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: DIM,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: DIM,
                bg: CPU_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: VAL,
                bg: CPU_BG,
                scroll: false,
            },
            StatusRun {
                text: format!(" {:>4.1}% ", self.cpu_percent),
                fg: VAL,
                bg: VAL_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: mem_fg,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: format!(" {}", self.mem_icon),
                fg: mem_fg,
                bg: CPU_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: VAL,
                bg: CPU_BG,
                scroll: false,
            },
            StatusRun {
                text: format!(" {} ", self.mem_text),
                fg: VAL,
                bg: VAL_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: DIM,
                bg: DIM,
                scroll: false,
            },
            StatusRun {
                text: format!(" {}", self.wifi_icon),
                fg: DIM,
                bg: WIFI_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: VAL,
                bg: WIFI_BG,
                scroll: false,
            },
            StatusRun {
                text: format!(" {} ", self.wifi_text),
                fg: VAL,
                bg: VAL_BG,
                scroll: false,
            },
            StatusRun {
                text: " ".into(),
                fg: NORM,
                bg: DIM,
                scroll: false,
            },
        ]
    }
}

pub fn parse_color(s: &str) -> Option<[f32; 4]> {
    let s = s.trim().trim_start_matches('#');
    if s.len() == 6 {
        let val = u32::from_str_radix(s, 16).ok()?;
        Some(col(val))
    } else if s.len() == 3 {
        let r = u8::from_str_radix(&s[0..1], 16).ok()?;
        let g = u8::from_str_radix(&s[1..2], 16).ok()?;
        let b = u8::from_str_radix(&s[2..3], 16).ok()?;
        Some([
            (r * 17) as f32 / 255.0,
            (g * 17) as f32 / 255.0,
            (b * 17) as f32 / 255.0,
            1.0,
        ])
    } else {
        None
    }
}

pub fn parse_status(text: &str) -> Vec<StatusToken> {
    let mut tokens = Vec::new();
    let mut current_text = String::new();
    let mut scrolling = false;
    let mut chars = text.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '^' {
            if chars.peek() == Some(&'^') {
                chars.next();
                current_text.push('^');
                continue;
            }
            if !current_text.is_empty() {
                let text = std::mem::take(&mut current_text);
                tokens.push(if scrolling {
                    StatusToken::ScrollText(text)
                } else {
                    StatusToken::Text(text)
                });
            }
            let mut code = String::new();
            for c in chars.by_ref() {
                if c == '^' {
                    break;
                }
                code.push(c);
            }
            if code.is_empty() {
                continue;
            }
            match code.chars().next() {
                Some('c') => {
                    if let Some(color) = parse_color(&code[1..]) {
                        tokens.push(StatusToken::Fg(color));
                    }
                }
                Some('b') => {
                    if let Some(color) = parse_color(&code[1..]) {
                        tokens.push(StatusToken::Bg(color));
                    }
                }
                Some('d') => {
                    tokens.push(StatusToken::Reset);
                }
                Some('m') => scrolling = true,
                Some('M') => scrolling = false,
                Some('f') => {
                    if let Ok(offset) = code[1..].parse::<i32>() {
                        tokens.push(StatusToken::Forward(offset));
                    }
                }
                Some('r') => {
                    let parts: Vec<&str> = code[1..].split(',').collect();
                    if parts.len() == 4
                        && let (Ok(x), Ok(y), Ok(w), Ok(h)) = (
                            parts[0].parse::<i32>(),
                            parts[1].parse::<i32>(),
                            parts[2].parse::<u32>(),
                            parts[3].parse::<u32>(),
                        )
                    {
                        tokens.push(StatusToken::Rect(x, y, w, h));
                    }
                }
                _ => {}
            }
        } else {
            current_text.push(ch);
        }
    }

    if !current_text.is_empty() {
        tokens.push(if scrolling {
            StatusToken::ScrollText(current_text)
        } else {
            StatusToken::Text(current_text)
        });
    }

    tokens
}

/// Watches NetworkManager D-Bus signals and sets a flag when the active
/// connection may have changed. Returns the flag plus whether the signal
/// source is available; when it is not, the sampler keeps its slow fallback
/// poll for setups that use iwctl or similar.
pub fn start_wifi_monitor() -> (Arc<AtomicBool>, bool) {
    let dirty = Arc::new(AtomicBool::new(false));
    let Ok(conn) = zbus::blocking::Connection::system() else {
        return (dirty, false);
    };
    let Ok(dbus) = zbus::blocking::fdo::DBusProxy::new(&conn) else {
        return (dirty, false);
    };
    // Without NetworkManager there are no signals to listen for (iwctl and
    // friends use other mechanisms), so keep the slow fallback poll.
    let Ok(names) = dbus.list_names() else {
        return (dirty, false);
    };
    if !names
        .iter()
        .any(|name| name.as_str() == "org.freedesktop.NetworkManager")
    {
        return (dirty, false);
    }
    let rules = [
        "type='signal',sender='org.freedesktop.NetworkManager',interface='org.freedesktop.DBus.Properties',member='PropertiesChanged'",
        "type='signal',sender='org.freedesktop.NetworkManager',member='StateChanged'",
    ];
    for rule in rules {
        let Ok(parsed) = zbus::OwnedMatchRule::try_from(rule) else {
            continue;
        };
        if dbus.add_match_rule(parsed.into()).is_err() {
            return (dirty, false);
        }
    }
    let writer = dirty.clone();
    if thread::Builder::new()
        .name("rwm-wifi".into())
        .spawn(move || {
            let events = zbus::blocking::MessageIterator::from(&conn);
            for _ in events {
                writer.store(true, Ordering::Release);
            }
        })
        .is_err()
    {
        return (dirty, false);
    }
    (dirty, true)
}

pub struct StatusSampler {
    last_total: u64,
    last_active: u64,
    last_sample_time: Instant,
    last_wifi_time: Instant,
    /// NetworkManager signal listener state. With signals available, WiFi is
    /// only re-read when this flag is set; otherwise the 3 s fallback applies.
    wifi_dirty: Arc<AtomicBool>,
    wifi_signals: bool,
    cached_wifi: (bool, String, &'static str),
    cached_status: Status,
    cached_mpris_key: String,
    custom: Option<String>,
}

impl StatusSampler {
    pub fn new() -> Self {
        let (wifi_dirty, wifi_signals) = start_wifi_monitor();
        let mut s = Self {
            last_total: 0,
            last_active: 0,
            last_sample_time: Instant::now() - std::time::Duration::from_secs(10),
            last_wifi_time: Instant::now() - std::time::Duration::from_secs(10),
            wifi_dirty,
            wifi_signals,
            cached_wifi: (false, String::new(), "󰤭"),
            cached_status: Status {
                custom: None,
                playing: None,
                battery_icon: "󰁹",
                battery_percent: 100,
                cpu_percent: 0.0,
                mem_icon: "󰾆",
                mem_text: "0Mi".into(),
                mem_warn: false,
                wifi_icon: "󰤭",
                wifi_text: "Disconnected".into(),
            },
            cached_mpris_key: String::new(),
            custom: None,
        };
        s.cached_status = s.sample();
        s
    }

    pub fn set_custom(&mut self, text: Option<String>) {
        self.custom = text;
    }

    pub fn sample(&mut self) -> Status {
        self.sample_with_mpris(None)
    }

    /// When the cached status becomes stale, so the main loop can sleep until
    /// then instead of waking on a fixed timer.
    pub fn next_sample(&self) -> Instant {
        self.last_sample_time + std::time::Duration::from_secs(1)
    }

    pub fn sample_with_mpris(&mut self, mpris: Option<&crate::mpris::Snapshot>) -> Status {
        let has_player = mpris.is_some_and(|player| player.present);
        if !has_player && let Some(ref custom) = self.custom {
            return Status {
                custom: Some(custom.clone()),
                playing: None,
                battery_icon: "",
                battery_percent: 0,
                cpu_percent: 0.0,
                mem_icon: "",
                mem_text: String::new(),
                mem_warn: false,
                wifi_icon: "",
                wifi_text: String::new(),
            };
        }
        let mpris_key = match mpris {
            Some(player) if player.present && player.playing => {
                format!("playing:{}:{}", player.service, player.scroll_text())
            }
            Some(player) if player.present => format!("paused:{}", player.service),
            _ => String::new(),
        };
        let now = Instant::now();
        // Update every 1000ms
        if now.duration_since(self.last_sample_time).as_millis() >= 1000
            || self.cached_mpris_key != mpris_key
        {
            self.last_sample_time = now;
            self.cached_status = self.generate_status(mpris);
            self.cached_mpris_key = mpris_key;
        }
        self.cached_status.clone()
    }

    fn get_wifi(&mut self) -> (bool, String, &'static str) {
        let now = Instant::now();
        let signaled = self.wifi_dirty.swap(false, Ordering::AcqRel);
        let due = if self.wifi_signals {
            signaled
        } else {
            now.duration_since(self.last_wifi_time).as_secs() >= 3
        };
        if due || self.cached_wifi.1.is_empty() {
            self.last_wifi_time = now;
            let refreshed = Self::read_wifi();
            if refreshed.1 != "Connected"
                || !self.cached_wifi.0
                || self.cached_wifi.1.is_empty()
                || self.cached_wifi.1 == "Connected"
            {
                self.cached_wifi = refreshed;
            }
        }
        self.cached_wifi.clone()
    }

    fn generate_status(&mut self, mpris: Option<&crate::mpris::Snapshot>) -> Status {
        let mpris_player = mpris.filter(|player| player.present && player.playing);
        let cpu = self.read_cpu();
        let (mem_percent, mem_text) = Self::read_memory();
        let (cap, charging) = Self::read_battery();
        let (wifi_ok, ssid, wicon) = self.get_wifi();

        let battery_icon = if charging {
            "󰂄"
        } else if cap >= 90 {
            "󰁹"
        } else if cap >= 50 {
            "󰁿"
        } else if cap >= 20 {
            "󰁼"
        } else {
            "󰁺"
        };

        let mem_icon = if mem_percent < 40 {
            "󰾆"
        } else if mem_percent < 80 {
            "󰾅"
        } else {
            "󰓅"
        };

        Status {
            custom: None,
            playing: mpris_player.map(|player| player.scroll_text()),
            battery_icon,
            battery_percent: cap,
            cpu_percent: cpu,
            mem_icon,
            mem_text,
            mem_warn: mem_percent >= 80,
            wifi_icon: wicon,
            wifi_text: if wifi_ok { ssid } else { "Disconnected".into() },
        }
    }

    fn read_cpu(&mut self) -> f32 {
        let Ok(content) = fs::read_to_string("/proc/stat") else {
            return 0.0;
        };
        let Some(line) = content.lines().next() else {
            return 0.0;
        };
        let parts: Vec<u64> = line
            .split_whitespace()
            .skip(1)
            .filter_map(|s| s.parse().ok())
            .collect();
        if parts.len() < 4 {
            return 0.0;
        }
        let total: u64 = parts.iter().sum();
        let idle: u64 = parts[3] + parts.get(4).copied().unwrap_or(0);
        let active = total.saturating_sub(idle);

        let mut cpu = 0.0f32;
        if self.last_total > 0 && total > self.last_total {
            let td = total - self.last_total;
            let ad = active.saturating_sub(self.last_active);
            cpu = (ad as f32 * 100.0) / (td as f32);
        }
        self.last_total = total;
        self.last_active = active;
        cpu
    }

    fn read_memory() -> (u32, String) {
        let Ok(content) = fs::read_to_string("/proc/meminfo") else {
            return (0, "0Mi".into());
        };
        let mut total = 0u64;
        let mut available = 0u64;
        for line in content.lines() {
            if line.starts_with("MemTotal:") {
                total = line
                    .split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
            } else if line.starts_with("MemAvailable:") {
                available = line
                    .split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
            }
        }
        let used = total.saturating_sub(available);
        let percent = (used * 100 + total / 2).checked_div(total).unwrap_or(0) as u32;
        let text = if used >= 1024 * 1024 {
            format!("{:.1}Gi", used as f64 / (1024.0 * 1024.0))
        } else if used >= 1024 {
            format!("{:.1}Mi", used as f64 / 1024.0)
        } else {
            format!("{}kB", used)
        };
        (percent, text)
    }

    fn read_battery() -> (i32, bool) {
        let cap = fs::read_to_string("/sys/class/power_supply/BAT0/capacity")
            .ok()
            .and_then(|s| s.trim().parse().ok())
            .unwrap_or(100);
        let charging = fs::read_to_string("/sys/class/power_supply/AC0/online")
            .ok()
            .and_then(|s| s.trim().parse::<i32>().ok())
            .unwrap_or(0)
            == 1;
        (cap, charging)
    }

    fn read_wifi() -> (bool, String, &'static str) {
        let wireless_interfaces = Self::wireless_interfaces();

        // 1. Try nmcli dev status / device listing (fastest and most reliable for NetworkManager)
        if let Ok(output) = Command::new("nmcli")
            .args(["-t", "-f", "DEVICE,TYPE,STATE,CONNECTION", "device"])
            .output()
            && output.status.success()
        {
            let text = String::from_utf8_lossy(&output.stdout);
            for line in text.lines() {
                let parts: Vec<&str> = line.split(':').collect();
                if parts.len() >= 4 {
                    let dev = parts[0].trim();
                    let dtype = parts[1].trim();
                    let state = parts[2].trim();
                    let conn = parts[3..].join(":").trim().replace("\\:", ":");
                    if (dev.starts_with("wl") || dtype == "wifi" || dtype == "wireless")
                        && state == "connected"
                        && !conn.is_empty()
                    {
                        return (true, conn, "󰤨");
                    }
                }
            }
        }

        // 2. Try nmcli dev wifi (to get active SSID with signal strength if possible)
        for args in [
            &["-t", "-f", "in-use,ssid,signal", "dev", "wifi"][..],
            &["-t", "-f", "active,ssid,signal", "dev", "wifi"][..],
        ] {
            if let Ok(output) = Command::new("nmcli").args(args).output()
                && output.status.success()
            {
                let text = String::from_utf8_lossy(&output.stdout);
                for line in text.lines() {
                    let is_active = line.starts_with('*')
                        || line.starts_with("yes")
                        || line.starts_with("true")
                        || line.starts_with("\\*");
                    if is_active {
                        let after_colon = line.split_once(':').map(|(_, r)| r).unwrap_or(line);
                        let mut parts = after_colon.split(':');
                        let ssid = parts.next().unwrap_or("").trim().replace("\\:", ":");
                        let signal: i32 = parts.next().and_then(|s| s.parse().ok()).unwrap_or(80);
                        if !ssid.is_empty() {
                            let icon = if signal > 60 {
                                "󰤨"
                            } else if signal > 45 {
                                "󰤥"
                            } else if signal > 35 {
                                "󰤢"
                            } else {
                                "󰤟"
                            };
                            return (true, ssid, icon);
                        }
                    }
                }
            }
        }

        // 3. Try nmcli active connections
        if let Ok(output) = Command::new("nmcli")
            .args([
                "-t",
                "-f",
                "NAME,TYPE,DEVICE",
                "connection",
                "show",
                "--active",
            ])
            .output()
            && output.status.success()
        {
            let text = String::from_utf8_lossy(&output.stdout);
            for line in text.lines() {
                let parts: Vec<&str> = line.split(':').collect();
                if parts.len() >= 2 {
                    let name = parts[0].trim().replace("\\:", ":");
                    let rest = parts[1..].join(":");
                    if (rest.contains("wireless") || rest.contains("wifi") || rest.contains("wlan"))
                        && !name.is_empty()
                    {
                        return (true, name, "󰤨");
                    }
                }
            }
        }

        // 4. Try busctl to query NetworkManager PrimaryConnection over system D-Bus
        if let Ok(output) = Command::new("busctl")
            .args([
                "--system",
                "get-property",
                "org.freedesktop.NetworkManager",
                "/org/freedesktop/NetworkManager",
                "org.freedesktop.NetworkManager",
                "PrimaryConnection",
            ])
            .output()
            && output.status.success()
        {
            let text = String::from_utf8_lossy(&output.stdout);
            if let Some(path) = text.split('"').nth(1)
                && path.starts_with("/org/freedesktop/NetworkManager/ActiveConnection/")
                && let Ok(id_out) = Command::new("busctl")
                    .args([
                        "--system",
                        "get-property",
                        "org.freedesktop.NetworkManager",
                        path,
                        "org.freedesktop.NetworkManager.Connection.Active",
                        "Id",
                    ])
                    .output()
                && id_out.status.success()
            {
                let id_text = String::from_utf8_lossy(&id_out.stdout);
                if let Some(ssid) = id_text.split('"').nth(1) {
                    let s = ssid.trim();
                    if !s.is_empty() {
                        return (true, s.to_string(), "󰤨");
                    }
                }
            }
        }

        // 5. Try iwctl (for iwd daemon)
        for name in &wireless_interfaces {
            if let Ok(output) = Command::new("iwctl")
                .args(["--dont-ask", "station", name, "show"])
                .output()
                && output.status.success()
            {
                let text = String::from_utf8_lossy(&output.stdout);
                for line in text.lines() {
                    if let Some(pos) = line.find("Connected network") {
                        let rest = &line[pos + "Connected network".len()..];
                        let ssid = rest.trim();
                        if !ssid.is_empty() {
                            return (true, ssid.to_string(), "󰤨");
                        }
                    }
                }
            }
        }

        // 6. Try wpa_cli status
        if let Ok(output) = Command::new("wpa_cli").args(["status"]).output()
            && output.status.success()
        {
            let text = String::from_utf8_lossy(&output.stdout);
            for line in text.lines() {
                if let Some(ssid) = line.strip_prefix("ssid=") {
                    let s = ssid.trim();
                    if !s.is_empty() {
                        return (true, s.to_string(), "󰤨");
                    }
                }
            }
        }

        // 7. Try iw dev <iface> link
        for name in &wireless_interfaces {
            if let Ok(output) = Command::new("iw").args(["dev", name, "link"]).output()
                && output.status.success()
            {
                let text = String::from_utf8_lossy(&output.stdout);
                for line in text.lines() {
                    let line = line.trim();
                    if let Some(ssid) = line.strip_prefix("SSID: ") {
                        let ssid = ssid.trim();
                        if !ssid.is_empty() {
                            return (true, ssid.to_string(), "󰤨");
                        }
                    }
                }
            }
        }

        // 8. Try iwgetid -r
        if let Ok(output) = Command::new("iwgetid").arg("-r").output()
            && output.status.success()
        {
            let ssid = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !ssid.is_empty() {
                return (true, ssid, "󰤨");
            }
        }

        // 9. Check if any wireless interface is UP / has carrier
        for name in &wireless_interfaces {
            let path = std::path::Path::new("/sys/class/net").join(name);
            let oper = fs::read_to_string(path.join("operstate"))
                .map(|s| s.trim().to_string())
                .unwrap_or_default();
            let carrier = fs::read_to_string(path.join("carrier"))
                .map(|s| s.trim() == "1")
                .unwrap_or(false);
            if oper == "up" || carrier {
                return (true, "Connected".to_string(), "󰤨");
            }
        }

        // 10. Check ethernet
        if let Ok(entries) = fs::read_dir("/sys/class/net") {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if name.starts_with("en") || name.starts_with("eth") {
                    let oper = fs::read_to_string(entry.path().join("operstate"))
                        .map(|s| s.trim().to_string())
                        .unwrap_or_default();
                    if oper == "up" {
                        return (true, "Wired".to_string(), "󰈀");
                    }
                }
            }
        }

        (false, "Disconnected".to_string(), "󰤭")
    }

    fn wireless_interfaces() -> Vec<String> {
        let Ok(entries) = fs::read_dir("/sys/class/net") else {
            return Vec::new();
        };

        entries
            .flatten()
            .filter_map(|entry| {
                let name = entry.file_name().to_string_lossy().into_owned();
                (entry.path().join("wireless").exists() || name.starts_with("wl")).then_some(name)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_status() {
        let s = "^c#a6e3a1^hello ^b#1E1D2D^world^d^";
        let tokens = parse_status(s);
        assert_eq!(tokens.len(), 5);
        assert!(matches!(tokens[0], StatusToken::Fg(_)));
        assert_eq!(tokens[1], StatusToken::Text("hello ".to_string()));
        assert!(matches!(tokens[2], StatusToken::Bg(_)));
        assert_eq!(tokens[3], StatusToken::Text("world".to_string()));
        assert_eq!(tokens[4], StatusToken::Reset);
    }

    #[test]
    fn test_parse_mpris_scroll_markers() {
        let tokens = parse_status("before^m^scrolling title^M^after");
        assert_eq!(tokens[0], StatusToken::Text("before".to_string()));
        assert_eq!(
            tokens[1],
            StatusToken::ScrollText("scrolling title".to_string())
        );
        assert_eq!(tokens[2], StatusToken::Text("after".to_string()));
    }

    #[test]
    fn test_active_mpris_status_is_typed() {
        let player = crate::mpris::Snapshot {
            present: true,
            playing: true,
            artist: "Example Band".into(),
            title: "A Song".into(),
            ..crate::mpris::Snapshot::default()
        };
        let mut sampler = StatusSampler::new();
        let status = sampler.generate_status(Some(&player));
        assert_eq!(status.playing.as_deref(), Some("[EXAMPLE BAND]  A Song"));
        assert_eq!(status.custom, None);
        let runs = status.runs();
        assert!(
            runs.iter()
                .any(|run| run.text == " 󰎆" && run.bg == 0xb8e9b4)
        );
    }

    #[test]
    fn test_active_mpris_mode_bypasses_status_cache() {
        let player = crate::mpris::Snapshot {
            present: true,
            playing: true,
            artist: "Example Band".into(),
            title: "A Song".into(),
            ..crate::mpris::Snapshot::default()
        };
        let mut sampler = StatusSampler::new();
        let status = sampler.sample_with_mpris(Some(&player));
        assert_eq!(status.playing.as_deref(), Some("[EXAMPLE BAND]  A Song"));
    }

    #[test]
    fn test_paused_mpris_mode_reverts_immediately() {
        let playing = crate::mpris::Snapshot {
            present: true,
            playing: true,
            artist: "Example Band".into(),
            title: "A Song".into(),
            service: "org.mpris.MediaPlayer2.test".into(),
            ..crate::mpris::Snapshot::default()
        };
        let paused = crate::mpris::Snapshot {
            playing: false,
            ..playing.clone()
        };
        let mut sampler = StatusSampler::new();
        assert!(sampler.sample_with_mpris(Some(&playing)).playing.is_some());
        let status = sampler.sample_with_mpris(Some(&paused));
        assert!(status.playing.is_none());
        let runs = status.runs();
        assert!(
            runs.iter()
                .any(|run| run.text == " " && run.bg == 0xa6e3a1)
        );
        assert!(
            runs.iter()
                .any(|run| run.fg == 0x96cdfb && run.text.contains('%'))
        );
    }

    #[test]
    fn test_status_sampler_runs_are_markup_free() {
        let mut sampler = StatusSampler::new();
        let status = sampler.sample();
        assert!(status.playing.is_none());
        let runs = status.runs();
        assert!(runs.iter().any(|run| run.text == " "));
        assert!(runs.iter().any(|run| run.bg == 0x282737));
        assert!(runs.iter().all(|run| !run.text.contains('^')));
    }

    #[test]
    fn test_status_runs_match_dwm_layout() {
        let status = Status {
            custom: None,
            playing: None,
            battery_icon: "󰁹",
            battery_percent: 85,
            cpu_percent: 12.3,
            mem_icon: "󰾆",
            mem_text: "3.2Gi".into(),
            mem_warn: false,
            wifi_icon: "󰤨",
            wifi_text: "MyWiFi".into(),
        };
        let runs = status.runs();
        let texts: Vec<&str> = runs.iter().map(|run| run.text.as_str()).collect();
        assert_eq!(
            texts,
            [
                "  ", "󰁹", " 85%", " ", " ", " ", " 12.3% ", " ", " 󰾆", " ", " 3.2Gi ", " ", " 󰤨",
                " ", " MyWiFi ", " ",
            ]
        );
        assert_eq!(runs[4].bg, 0xa6e3a1);
        assert_eq!(runs[6].bg, 0x282737);
        assert_eq!(runs[9].bg, 0xa6e3a1);
        assert_eq!(runs[12].bg, 0x96cdfb);
    }
}

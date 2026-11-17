use std::fs;
use std::process::Command;
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
                tokens.push(if scrolling { StatusToken::ScrollText(text) } else { StatusToken::Text(text) });
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
        tokens.push(if scrolling { StatusToken::ScrollText(current_text) } else { StatusToken::Text(current_text) });
    }

    tokens
}

pub struct StatusSampler {
    last_total: u64,
    last_active: u64,
    last_sample_time: Instant,
    last_wifi_time: Instant,
    cached_wifi: (bool, String, &'static str),
    cached_status: String,
    cached_mpris_key: String,
    custom: Option<String>,
}

impl StatusSampler {
    pub fn new() -> Self {
        let mut s = Self {
            last_total: 0,
            last_active: 0,
            last_sample_time: Instant::now() - std::time::Duration::from_secs(10),
            last_wifi_time: Instant::now() - std::time::Duration::from_secs(10),
            cached_wifi: (false, String::new(), "󰤭"),
            cached_status: String::new(),
            cached_mpris_key: String::new(),
            custom: None,
        };
        s.cached_status = s.sample();
        s
    }

    pub fn set_custom(&mut self, text: Option<String>) {
        self.custom = text;
    }

    pub fn sample(&mut self) -> String {
        self.sample_with_mpris(None)
    }

    pub fn sample_with_mpris(&mut self, mpris: Option<&crate::mpris::Snapshot>) -> String {
        let has_player = mpris.is_some_and(|player| player.present);
        if !has_player && let Some(ref custom) = self.custom {
            return custom.clone();
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
            || self.cached_status.is_empty()
            || self.cached_mpris_key != mpris_key
        {
            self.last_sample_time = now;
            self.cached_status = self.generate_system_status(mpris);
            self.cached_mpris_key = mpris_key;
        }
        self.cached_status.clone()
    }

    fn get_wifi(&mut self) -> (bool, String, &'static str) {
        let now = Instant::now();
        if now.duration_since(self.last_wifi_time).as_secs() >= 3 || self.cached_wifi.1.is_empty() {
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

    fn generate_system_status(&mut self, mpris: Option<&crate::mpris::Snapshot>) -> String {
        let has_player = mpris.is_some_and(|player| player.present);
        let mpris_player = mpris.filter(|player| player.present && player.playing);
        let mpris_playing = mpris_player.is_some();
        let cpu = self.read_cpu();
        let (mem_percent, mem_text) = Self::read_memory();
        let (cap, charging) = Self::read_battery();
        let (wifi_ok, ssid, wicon) = self.get_wifi();

        let bicon = if charging {
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

        let mem_color = if mem_percent < 80 { "#1E1D2D" } else { "#ed8796" };
        let wifi_str = if wifi_ok { &ssid } else { "Disconnected" };

        let sav_icon = "";

        if has_player && mpris_playing {
            let player = mpris_player.expect("playing player snapshot");
            let player_text = player.scroll_text();
            return format!(
                "^c#a6e3a1^{sav_icon} ^c#1E1D2D^ ^b#B8E9B4^ 󰎆^c#1E1D2D^^m^ {player_text}^M^^d^^c{mem_color}^ ^b#96CDFB^ {mem_icon} ^d^^c#1E1D2D^ ^b#96CDFB^ {wicon} ^d^^c#96CDFB^ {bicon}^b#1E1D2D^ "
            );
        }

        // Exact dwm.c status layout for systems without active playback.
        format!(
            "^c#a6e3a1^{sav_icon}  ^c#96CDFB^{bicon} {cap}%^c#1E1D2D^ ^b#a6e3a1^ ^c#D9E0EE^ ^b#282737^ {cpu:>4.1}% ^d^^c{mem_color}^ ^b#a6e3a1^ {mem_icon}^c#D9E0EE^ ^b#282737^ {mem_text} ^d^^c#1E1D2D^ ^b#96CDFB^ {wicon}^c#D9E0EE^ ^b#282737^ {wifi_str} ^d^^b#1E1D2D^ ",
            sav_icon = sav_icon,
            bicon = bicon,
            cap = cap,
            cpu = cpu,
            mem_color = mem_color,
            mem_icon = mem_icon,
            mem_text = mem_text,
            wicon = wicon,
            wifi_str = wifi_str,
        )
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
                total = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0);
            } else if line.starts_with("MemAvailable:") {
                available = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0);
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
            .args(["-t", "-f", "NAME,TYPE,DEVICE", "connection", "show", "--active"])
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
                (entry.path().join("wireless").exists() || name.starts_with("wl"))
                    .then_some(name)
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
        assert_eq!(tokens[1], StatusToken::ScrollText("scrolling title".to_string()));
        assert_eq!(tokens[2], StatusToken::Text("after".to_string()));
    }

    #[test]
    fn test_active_mpris_status_matches_dwm_markup() {
        let player = crate::mpris::Snapshot {
            present: true,
            playing: true,
            artist: "Example Band".into(),
            title: "A Song".into(),
            ..crate::mpris::Snapshot::default()
        };
        let mut sampler = StatusSampler::new();
        let status = sampler.generate_system_status(Some(&player));
        assert!(status.contains(
            "^c#1E1D2D^ ^b#B8E9B4^ 󰎆^c#1E1D2D^^m^ [EXAMPLE BAND]  A Song^M^"
        ));
        assert!(status.ends_with("^b#1E1D2D^ "));
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
        assert!(status.contains("^m^ [EXAMPLE BAND]  A Song^M^"));
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
        let paused = crate::mpris::Snapshot { playing: false, ..playing.clone() };
        let mut sampler = StatusSampler::new();
        assert!(sampler.sample_with_mpris(Some(&playing)).contains("^m^"));
        let status = sampler.sample_with_mpris(Some(&paused));
        assert!(!status.contains("^m^"));
        assert!(status.contains(""));
    }

    #[test]
    fn test_status_sampler_runs() {
        let mut sampler = StatusSampler::new();
        let status = sampler.sample();
        assert!(!status.is_empty());
        assert!(status.contains(""));
        assert!(status.contains("^c#"));
        // Check character spacing elements
        assert!(status.contains("^b#a6e3a1^ "));
        assert!(status.contains("^b#282737^"));
    }
}

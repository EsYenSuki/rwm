use std::collections::HashMap;
use std::process::{Command, Stdio};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender, TrySendError};
use std::sync::{Arc, OnceLock};
use std::thread;
use std::time::Instant;

use zbus::blocking::{Connection, MessageIterator};
use zbus::zvariant::OwnedValue;

const PLAYER_PATH: &str = "/org/mpris/MediaPlayer2";
const PLAYER_INTERFACE: &str = "org.mpris.MediaPlayer2.Player";
const ART_SIZE: usize = 512;

#[derive(Debug)]
pub struct Artwork {
    pub rgba: Vec<u8>,
    pub width: usize,
    pub height: usize,
}

#[derive(Clone, Debug)]
pub struct Snapshot {
    pub present: bool,
    pub playing: bool,
    pub service: String,
    pub artist: String,
    pub title: String,
    pub art_url: String,
    pub artwork: Option<Arc<Artwork>>,
    /// Progress at the moment the properties were read over D-Bus.
    pub progress: Option<f32>,
    pub volume: f32,
    /// Playback position and length in seconds at `position_at`. MPRIS players
    /// do not signal continuous position changes, so the bar advances this
    /// locally instead of polling Position.
    pub position: f64,
    pub length: f64,
    pub position_at: Instant,
}

impl PartialEq for Snapshot {
    /// Compares everything that can be drawn. Artwork is compared by identity
    /// so a new cover still counts as a change while the RGBA data is not
    /// scanned on every frame.
    fn eq(&self, other: &Self) -> bool {
        self.present == other.present
            && self.playing == other.playing
            && self.service == other.service
            && self.artist == other.artist
            && self.title == other.title
            && self.art_url == other.art_url
            && match (&self.artwork, &other.artwork) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
            && self.progress == other.progress
            && self.volume == other.volume
    }
}

impl Default for Snapshot {
    fn default() -> Self {
        Self {
            present: false,
            playing: false,
            service: String::new(),
            artist: String::new(),
            title: String::new(),
            art_url: String::new(),
            artwork: None,
            progress: None,
            volume: 1.0,
            position: 0.0,
            length: 0.0,
            position_at: Instant::now(),
        }
    }
}

impl Snapshot {
    /// Current progress, advanced from the last D-Bus reading. Seeking and
    /// track changes arrive as signals and replace the reading entirely.
    pub fn current_progress(&self) -> Option<f32> {
        if !self.playing || self.length <= 0.0 {
            return self.progress;
        }
        let elapsed = self.position_at.elapsed().as_secs_f64();
        let value = ((self.position + elapsed) / self.length).clamp(0.0, 1.0) as f32;
        Some(if value >= 0.995 { 1.0 } else { value })
    }

    pub fn scroll_text(&self) -> String {
        let mut artist = self.artist.to_ascii_uppercase();
        if artist.ends_with(" - TOPIC") {
            artist.truncate(artist.len() - 8);
        }
        format!("[{}]  {}", if artist.is_empty() { "UNKNOWN ARTIST" } else { &artist }, self.title)
    }
}

pub fn start_monitor() -> Receiver<Snapshot> {
    let (sender, receiver) = mpsc::sync_channel(1);
    let _ = thread::Builder::new().name("rwm-mpris".into()).spawn(move || monitor_loop(sender));
    receiver
}

/// Listens for MPRIS D-Bus signals instead of polling. Property changes cover
/// track, artist, cover and playback state; NameOwnerChanged covers players
/// appearing or leaving; Seeked covers position jumps. Ordinary playback
/// position is interpolated locally by `Snapshot::current_progress`.
fn monitor_loop(sender: SyncSender<Snapshot>) {
    let Ok(listener) = Connection::session() else {
        return;
    };
    // Method calls use a second connection: the listener's message iterator
    // consumes every message routed to its connection, including replies.
    let Ok(caller) = Connection::session() else {
        return;
    };
    let Ok(dbus) = zbus::blocking::fdo::DBusProxy::new(&listener) else {
        return;
    };
    let rules = [
        "type='signal',interface='org.freedesktop.DBus',member='NameOwnerChanged'",
        "type='signal',interface='org.freedesktop.DBus.Properties',member='PropertiesChanged',arg0='org.mpris.MediaPlayer2.Player'",
        "type='signal',interface='org.mpris.MediaPlayer2.Player',member='Seeked'",
    ];
    for rule in rules {
        let Ok(parsed) = zbus::OwnedMatchRule::try_from(rule) else {
            continue;
        };
        if dbus.add_match_rule(parsed.into()).is_err() {
            return;
        }
    }

    let mut art_url = String::new();
    let mut artwork = None;
    if !publish(&sender, &caller, &mut art_url, &mut artwork) {
        return;
    }
    let events = MessageIterator::from(&listener);
    for message in events {
        if message.is_ok() && !publish(&sender, &caller, &mut art_url, &mut artwork) {
            return;
        }
    }
}

fn publish(
    sender: &SyncSender<Snapshot>,
    caller: &Connection,
    art_url: &mut String,
    artwork: &mut Option<Arc<Artwork>>,
) -> bool {
    let mut snapshot = read_player(caller);
    if snapshot.art_url != *art_url {
        art_url.clone_from(&snapshot.art_url);
        *artwork = load_artwork(art_url).map(Arc::new);
    }
    snapshot.artwork = artwork.clone();
    match sender.try_send(snapshot) {
        Ok(()) | Err(TrySendError::Full(_)) => true,
        Err(TrySendError::Disconnected(_)) => false,
    }
}

fn read_player(caller: &Connection) -> Snapshot {
    let Ok(dbus) = zbus::blocking::fdo::DBusProxy::new(caller) else {
        return Snapshot::default();
    };
    let Ok(names) = dbus.list_names() else {
        return Snapshot::default();
    };
    let mut paused_player = None;
    for name in names {
        let service = name.to_string();
        if !service.starts_with("org.mpris.MediaPlayer2.") {
            continue;
        }
        let Ok(proxy) =
            zbus::blocking::Proxy::new(caller, service.clone(), PLAYER_PATH, PLAYER_INTERFACE)
        else {
            continue;
        };
        let Ok(status) = proxy.get_property::<String>("PlaybackStatus") else {
            continue;
        };
        if status != "Playing" && status != "Paused" {
            continue;
        }
        let Ok(metadata) = proxy.get_property::<HashMap<String, OwnedValue>>("Metadata") else {
            continue;
        };
        let title = dict_string(&metadata, "xesam:title").unwrap_or_default();
        if title.is_empty() {
            continue;
        }
        let artist = dict_array_string(&metadata, "xesam:artist").unwrap_or_default();
        let art_url = dict_string(&metadata, "mpris:artUrl").unwrap_or_default();
        // MPRIS uses microseconds for both length and Position.
        let length = dict_number(&metadata, "mpris:length").unwrap_or(0.0) / 1_000_000.0;
        let position = proxy.get_property::<i64>("Position").unwrap_or(0).max(0) as f64 / 1_000_000.0;
        let volume = proxy.get_property::<f64>("Volume").unwrap_or(1.0).clamp(0.0, 1.0) as f32;
        let progress = (length > 0.0).then(|| {
            let value = (position / length).min(1.0) as f32;
            if value >= 0.995 { 1.0 } else { value }
        });

        let snapshot = Snapshot {
            present: true,
            playing: status == "Playing",
            service,
            artist,
            title,
            art_url,
            artwork: None,
            progress,
            volume,
            position,
            length,
            position_at: Instant::now(),
        };
        if snapshot.playing {
            return snapshot;
        }
        paused_player.get_or_insert(snapshot);
    }
    paused_player.unwrap_or_default()
}

fn dict_string(fields: &HashMap<String, OwnedValue>, key: &str) -> Option<String> {
    let value = fields.get(key)?;
    let text: &str = value.try_into().ok()?;
    Some(text.to_owned())
}

fn dict_array_string(fields: &HashMap<String, OwnedValue>, key: &str) -> Option<String> {
    let value = fields.get(key)?;
    let array: &zbus::zvariant::Array = value.try_into().ok()?;
    array.iter().find_map(|item| item.downcast_ref::<&str>().ok().map(str::to_owned))
}

fn dict_number(fields: &HashMap<String, OwnedValue>, key: &str) -> Option<f64> {
    let value = fields.get(key)?;
    u64::try_from(value).ok().map(|number| number as f64).or_else(|| f64::try_from(value).ok())
}

// The old busctl output parser is no longer used at runtime. Kept for the
// tokenizer regression tests only.
#[cfg(test)]
fn busctl_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        if ch != '"' {
            let mut token = String::from(ch);
            while let Some(&next) = chars.peek() {
                if next.is_whitespace() {
                    break;
                }
                token.push(chars.next().unwrap());
            }
            tokens.push(token);
            continue;
        }

        let mut token = Vec::new();
        while let Some(ch) = chars.next() {
            match ch {
                '"' => break,
                '\\' => match chars.next() {
                    Some(ch @ '0'..='7') => {
                        let mut octal = String::from(ch);
                        for _ in 0..2 {
                            if let Some(&next @ '0'..='7') = chars.peek() {
                                octal.push(next);
                                chars.next();
                            }
                        }
                        if let Ok(byte) = u8::from_str_radix(&octal, 8) {
                            token.push(byte);
                        }
                    }
                    Some('n') => token.push(b'\n'),
                    Some('r') => token.push(b'\r'),
                    Some('t') => token.push(b'\t'),
                    Some(ch) => {
                        let mut encoded = [0; 4];
                        token.extend_from_slice(ch.encode_utf8(&mut encoded).as_bytes());
                    }
                    None => break,
                },
                ch => {
                    let mut encoded = [0; 4];
                    token.extend_from_slice(ch.encode_utf8(&mut encoded).as_bytes());
                }
            }
        }
        tokens.push(String::from_utf8_lossy(&token).into_owned());
    }
    tokens
}

#[cfg(test)]
fn busctl_dict_string(fields: &[String], key: &str) -> Option<String> {
    let index = fields.iter().position(|field| field == key)?;
    (fields.get(index + 1)? == "s").then(|| fields.get(index + 2).cloned()).flatten()
}

#[cfg(test)]
fn busctl_dict_array_string(fields: &[String], key: &str) -> Option<String> {
    let index = fields.iter().position(|field| field == key)?;
    if fields.get(index + 1)? != "as" {
        return None;
    }
    let count = fields.get(index + 2)?.parse::<usize>().ok()?;
    (count > 0).then(|| fields.get(index + 3).cloned()).flatten()
}

#[cfg(test)]
fn busctl_dict_number(fields: &[String], key: &str) -> Option<f64> {
    let index = fields.iter().position(|field| field == key)?;
    fields.get(index + 2)?.parse().ok()
}

fn load_artwork(url: &str) -> Option<Artwork> {
    let path = if let Some(path) = url.strip_prefix("file://") {
        decode_file_url(path)?
    } else if url.starts_with('/') {
        url.to_string()
    } else {
        return None;
    };
    let output = Command::new("ffmpeg")
        .args([
            "-hide_banner",
            "-loglevel",
            "error",
            "-i",
            &path,
            "-vf",
            "scale=512:512:force_original_aspect_ratio=increase,crop=512:512",
            "-frames:v",
            "1",
            "-f",
            "rawvideo",
            "-pix_fmt",
            "rgba",
            "pipe:1",
        ])
        .stdout(Stdio::piped())
        .output()
        .ok()?;
    let expected = ART_SIZE * ART_SIZE * 4;
    (output.status.success() && output.stdout.len() == expected).then_some(Artwork {
        rgba: output.stdout,
        width: ART_SIZE,
        height: ART_SIZE,
    })
}

fn decode_file_url(path: &str) -> Option<String> {
    let mut decoded = Vec::with_capacity(path.len());
    let bytes = path.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            let hex = std::str::from_utf8(bytes.get(index + 1..index + 3)?).ok()?;
            decoded.push(u8::from_str_radix(hex, 16).ok()?);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(decoded).ok()
}

pub fn slider_volume(position: f32) -> f32 {
    let position = position.clamp(0.0, 1.0);
    if position == 0.0 {
        0.0
    } else {
        ((position * 9.0_f32.ln_1p()).exp_m1() / 9.0).clamp(0.0, 1.0)
    }
}

pub fn volume_position(volume: f32) -> f32 {
    let volume = volume.clamp(0.0, 1.0);
    if volume == 0.0 {
        0.0
    } else {
        (1.0 + volume * 9.0).ln() / 9.0_f32.ln_1p()
    }
}

pub fn play_pause(service: &str) {
    call_method(service, "PlayPause");
}

pub fn previous(service: &str) {
    call_method(service, "Previous");
}

pub fn next(service: &str) {
    call_method(service, "Next");
}

fn call_method(service: &str, method: &str) {
    run_busctl([
        "--user",
        "call",
        service,
        PLAYER_PATH,
        PLAYER_INTERFACE,
        method,
    ]);
}

static VOLUME_TX: OnceLock<Sender<(String, f32)>> = OnceLock::new();

pub fn set_volume(service: &str, volume: f32) {
    let tx = VOLUME_TX.get_or_init(|| {
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || volume_writer(rx));
        tx
    });
    let _ = tx.send((service.to_string(), volume.clamp(0.0, 1.0)));
}

fn volume_writer(rx: Receiver<(String, f32)>) {
    while let Ok(mut latest) = rx.recv() {
        while let Ok(next) = rx.try_recv() {
            latest = next;
        }
        let (service, volume) = latest;
        let value = volume.to_string();
        let _ = Command::new("busctl")
            .args([
                "--user",
                "set-property",
                &service,
                PLAYER_PATH,
                PLAYER_INTERFACE,
                "Volume",
                "d",
                &value,
            ])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}

fn run_busctl<const N: usize>(args: [&str; N]) {
    let args = args.map(str::to_owned);
    thread::spawn(move || {
        let _ = Command::new("busctl")
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn parses_busctl_metadata_values() {
        let fields = busctl_tokens(
            r#"a{sv} 4 "xesam:title" s "A \"Quoted\" Song" "xesam:artist" as 1 "THE BAND" "mpris:length" x 240000000 "mpris:artUrl" s "file:///tmp/cover%20art.png""#,
        );
        assert_eq!(busctl_dict_string(&fields, "xesam:title").as_deref(), Some("A \"Quoted\" Song"));
        assert_eq!(busctl_dict_array_string(&fields, "xesam:artist").as_deref(), Some("THE BAND"));
        assert_eq!(busctl_dict_number(&fields, "mpris:length"), Some(240000000.0));
        assert_eq!(busctl_dict_string(&fields, "mpris:artUrl").as_deref(), Some("file:///tmp/cover%20art.png"));
    }

    #[test]
    fn decodes_busctl_octal_utf8_escapes() {
        let fields = busctl_tokens(r#"s "\345\210\235\351\237\263\343\203\237\343\202\257""#);
        assert_eq!(fields[1], "初音ミク");
    }

    #[test]
    fn volume_curve_round_trips() {
        for volume in [0.0, 0.1, 0.35, 0.75, 1.0] {
            assert!((slider_volume(volume_position(volume)) - volume).abs() < 0.0001);
        }
    }

    #[test]
    #[ignore = "requires a playing MPRIS player on the session bus"]
    fn reads_live_mpris_player() {
        let player = start_monitor()
            .recv_timeout(Duration::from_secs(5))
            .expect("MPRIS monitor did not publish a snapshot");
        assert!(player.present, "no player detected: {player:#?}");
        assert!(player.playing, "no playing player detected: {player:#?}");
        assert!(!player.title.is_empty());
    }

    #[test]
    fn formats_scroll_text_like_dwm() {
        let snapshot = Snapshot {
            artist: "Example Band - Topic".into(),
            title: "A Song".into(),
            ..Snapshot::default()
        };
        assert_eq!(snapshot.scroll_text(), "[EXAMPLE BAND]  A Song");
    }
}
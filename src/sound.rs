//! dwm.c's `sound_monitor_*` and `on_process`: captures the system output
//! through PipeWire and publishes its peak level for the clock bar animation.

use std::error::Error;
use std::io::Cursor;
use std::mem;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use pipewire as pw;
use pw::properties::properties;
use pw::spa;
use spa::param::ParamType;
use spa::param::audio::{AudioFormat, AudioInfoRaw};
use spa::param::format::{MediaSubtype, MediaType};
use spa::param::format_utils;
use spa::pod::serialize::PodSerializer;
use spa::pod::{Object, Pod, Value};
use spa::utils::SpaTypes;

use crate::config::PW_MONITOR_SINK;

/// Peak level in `0.0..=1.0` after the `sqrt` mapping, stored as f32 bits.
pub type Peak = Arc<AtomicU32>;

struct State {
    format: AudioInfoRaw,
    peak: Peak,
}

/// Starts the capture thread and returns the shared peak. The peak stays at 0
/// when PipeWire is unavailable, which leaves the clock at its fixed width.
pub fn start() -> Peak {
    let peak: Peak = Arc::new(AtomicU32::new(0));
    let writer = peak.clone();
    let spawned = thread::Builder::new()
        .name("rwm-sound-bar".into())
        .spawn(move || {
            if let Err(err) = run(writer) {
                eprintln!("rwm: clock peak monitor stopped: {err}");
            }
        });
    if let Err(err) = spawned {
        eprintln!("rwm: clock peak monitor not started: {err}");
    }
    peak
}

pub fn read(peak: &Peak) -> f32 {
    f32::from_bits(peak.load(Ordering::Relaxed))
}

fn run(peak: Peak) -> Result<(), Box<dyn Error>> {
    pw::init();
    let mainloop = pw::main_loop::MainLoopRc::new(None)?;
    let context = pw::context::ContextRc::new(&mainloop, None)?;
    let core = context.connect_rc(None)?;

    let mut props = properties! {
        *pw::keys::MEDIA_TYPE => "Audio",
        *pw::keys::MEDIA_CATEGORY => "Capture",
        *pw::keys::MEDIA_ROLE => "Music",
    };
    if PW_MONITOR_SINK {
        props.insert(*pw::keys::STREAM_CAPTURE_SINK, "true");
    }

    let stream = pw::stream::StreamBox::new(&core, "rwm-sound-bar", props)?;
    let _listener = stream
        .add_local_listener_with_user_data(State {
            format: AudioInfoRaw::default(),
            peak,
        })
        .param_changed(|_, state, id, param| {
            let Some(param) = param else {
                return;
            };
            if id != ParamType::Format.as_raw() {
                return;
            }
            let Ok((media_type, media_subtype)) = format_utils::parse_format(param) else {
                return;
            };
            if media_type != MediaType::Audio || media_subtype != MediaSubtype::Raw {
                return;
            }
            let _ = state.format.parse(param);
        })
        .process(|stream, state| {
            let Some(mut buffer) = stream.dequeue_buffer() else {
                return;
            };
            let datas = buffer.datas_mut();
            if datas.is_empty() || state.format.channels() == 0 {
                return;
            }
            let data = &mut datas[0];
            let size = data.chunk().size() as usize;
            let Some(samples) = data.data() else {
                return;
            };
            let count = (size / mem::size_of::<f32>()).min(samples.len() / mem::size_of::<f32>());

            let mut max = 0.0f32;
            for bytes in
                samples[..count * mem::size_of::<f32>()].chunks_exact(mem::size_of::<f32>())
            {
                let sample = f32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                max = max.max(sample.abs());
            }

            let level = max.min(1.0).sqrt();
            state.peak.store(level.to_bits(), Ordering::Relaxed);
        })
        .register()?;

    let mut info = AudioInfoRaw::new();
    info.set_format(AudioFormat::F32LE);
    let obj = Object {
        type_: SpaTypes::ObjectParamFormat.as_raw(),
        id: ParamType::EnumFormat.as_raw(),
        properties: info.into(),
    };
    let values: Vec<u8> = PodSerializer::serialize(Cursor::new(Vec::new()), &Value::Object(obj))?
        .0
        .into_inner();
    let mut params = [Pod::from_bytes(&values).ok_or("invalid format pod")?];

    stream.connect(
        spa::utils::Direction::Input,
        None,
        pw::stream::StreamFlags::AUTOCONNECT
            | pw::stream::StreamFlags::MAP_BUFFERS
            | pw::stream::StreamFlags::RT_PROCESS,
        &mut params,
    )?;

    mainloop.run();
    Ok(())
}

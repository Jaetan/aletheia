// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Aletheia Rust Benchmark.
//!
//! Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
//! through the Aletheia FFI pipeline (Rust -> libloading -> Haskell/MAlonzo/Agda).
//!
//! It is the Rust member of the cross-language benchmark suite: the workload,
//! the lane names, and the emitted JSON schema mirror the Go / Python / C++
//! benchmarks field-for-field, so `benchmarks/run_all.sh` compares like with
//! like. Point `ALETHEIA_LIB` at the built core and select a mode:
//!
//! ```sh
//! ALETHEIA_LIB=/path/to/build/libaletheia-ffi.so \
//!     cargo run --release --example benchmark -- throughput --frames 10000 --runs 5 --json
//! ```
//!
//! Modes: `throughput` (`--frames N --runs N`), `latency` (`--ops N`),
//! `scaling` (property-count sweep, `--frames N --runs N`). `--json` sends the
//! human-readable progress to stderr and prints the JSON report to stdout.
//! `--quick` shrinks the default sizes for a fast smoke run.

use std::time::{Instant, SystemTime, UNIX_EPOCH};

use aletheia::{
    ByteOrder, CanId, Client, Dbc, DbcMessage, DbcSignal, Dlc, Formula, Predicate, Presence,
    Rational, SignalValue, Timestamp,
};
use serde_json::{json, Value};

// ---------------------------------------------------------------------------
// DBC construction (programmatic, matching examples/*.dbc and the Go / C++
// benchmark definitions so every binding measures the same map-backed lookup
// path a real user exercises).
// ---------------------------------------------------------------------------

/// Shorthand for an exact rational used in the benchmark DBC definitions.
fn r(num: i64, den: i64) -> Rational {
    Rational::new(num, den).expect("benchmark rationals have non-zero positive denominators")
}

/// Build a little-endian, always-present signal. `scale` is `(factor, offset)`
/// and `bounds` is `(minimum, maximum)` — bundling them keeps the parameter
/// count within clippy's limit while covering the fields the benchmark varies.
fn sig(
    name: &str,
    start: u32,
    len: u32,
    signed: bool,
    scale: (Rational, Rational),
    bounds: (Rational, Rational),
    unit: &str,
) -> DbcSignal {
    DbcSignal {
        name: name.to_string(),
        start_bit: start,
        length: len,
        byte_order: ByteOrder::LittleEndian,
        signed,
        factor: scale.0,
        offset: scale.1,
        minimum: bounds.0,
        maximum: bounds.1,
        unit: unit.to_string(),
        receivers: Vec::new(),
        value_descriptions: Vec::new(),
        presence: Presence::Always,
    }
}

/// Build a standard-id (11-bit) message with the given signals.
fn msg(id: u32, name: &str, dlc: u32, sender: &str, signals: Vec<DbcSignal>) -> DbcMessage {
    DbcMessage {
        id,
        extended: false,
        name: name.to_string(),
        dlc,
        sender: sender.to_string(),
        senders: Vec::new(),
        signals,
    }
}

/// Wrap messages in an otherwise-empty DBC document.
fn dbc(messages: Vec<DbcMessage>) -> Dbc {
    Dbc {
        version: String::new(),
        messages,
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    }
}

/// CAN 2.0B database: EngineStatus (0x100) + BrakeStatus (0x200).
fn can20_dbc() -> Dbc {
    let engine = msg(
        0x100,
        "EngineStatus",
        8,
        "ECU1",
        vec![
            sig(
                "EngineSpeed",
                0,
                16,
                false,
                (r(1, 4), r(0, 1)),
                (r(0, 1), r(8000, 1)),
                "rpm",
            ),
            sig(
                "EngineTemp",
                16,
                8,
                false,
                (r(1, 1), r(-40, 1)),
                (r(-40, 1), r(215, 1)),
                "celsius",
            ),
        ],
    );
    let brake = msg(
        0x200,
        "BrakeStatus",
        8,
        "ECU2",
        vec![
            sig(
                "BrakePressure",
                0,
                16,
                false,
                (r(1, 10), r(0, 1)),
                (r(0, 1), r(65535, 10)),
                "bar",
            ),
            sig(
                "BrakePressed",
                16,
                1,
                false,
                (r(1, 1), r(0, 1)),
                (r(0, 1), r(1, 1)),
                "",
            ),
        ],
    );
    dbc(vec![engine, brake])
}

/// CAN-FD database: a 25-signal SensorFusion message (0x200, DLC 15 = 64 bytes).
fn canfd_dbc() -> Dbc {
    let signals = vec![
        sig(
            "GPSLatitude",
            0,
            32,
            true,
            (r(1, 10_000_000), r(0, 1)),
            (r(-90, 1), r(90, 1)),
            "deg",
        ),
        sig(
            "GPSLongitude",
            32,
            32,
            true,
            (r(1, 10_000_000), r(0, 1)),
            (r(-180, 1), r(180, 1)),
            "deg",
        ),
        sig(
            "GPSAltitude",
            64,
            16,
            true,
            (r(1, 10), r(0, 1)),
            (r(-1000, 1), r(55535, 10)),
            "m",
        ),
        sig(
            "GPSSpeed",
            80,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "YawRate",
            96,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "deg/s",
        ),
        sig(
            "LateralAccel",
            112,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "m/s2",
        ),
        sig(
            "LongAccel",
            128,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "m/s2",
        ),
        sig(
            "SteeringAngle",
            144,
            16,
            true,
            (r(1, 10), r(0, 1)),
            (r(-32768, 10), r(32767, 10)),
            "deg",
        ),
        sig(
            "WheelSpeedFL",
            160,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedFR",
            176,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedRL",
            192,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedRR",
            208,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "BrakeTempFL",
            224,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempFR",
            236,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempRL",
            248,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempRR",
            260,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "TirePressFL",
            272,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressFR",
            280,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressRL",
            288,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressRR",
            296,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "SensorStatus",
            304,
            8,
            false,
            (r(1, 1), r(0, 1)),
            (r(0, 1), r(255, 1)),
            "",
        ),
        sig(
            "IMUTemp",
            312,
            8,
            true,
            (r(1, 1), r(-40, 1)),
            (r(-40, 1), r(215, 1)),
            "celsius",
        ),
        sig(
            "BatteryVolt",
            320,
            12,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(4095, 100)),
            "V",
        ),
        sig(
            "GPSHeading",
            332,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "deg",
        ),
        sig(
            "TimestampMs",
            348,
            32,
            false,
            (r(1, 1), r(0, 1)),
            (r(0, 1), r(4_294_967_295, 1)),
            "ms",
        ),
    ];
    // The message `dlc` field is a byte count on the wire (Go serializes
    // `DLC.ToBytes()`); DLC code 15 = 64 bytes. The DLC *code* 15 is what the
    // send / extract / build calls use (`Dlc::new(15)`).
    dbc(vec![msg(
        0x200,
        "SensorFusion",
        64,
        "SensorGateway",
        signals,
    )])
}

// ---------------------------------------------------------------------------
// Frame payloads
// ---------------------------------------------------------------------------

/// CAN 2.0B payload (8 bytes): EngineSpeed raw 0x1F40 -> 2000 * 0.25 = ...
fn can20_frame() -> Vec<u8> {
    vec![0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]
}

/// CAN-FD payload (64 bytes) with realistic sensor-fusion values, zero-padded.
fn canfd_frame() -> Vec<u8> {
    let mut frame = vec![
        0x00, 0xE1, 0xF5, 0x05, // GPSLatitude
        0x00, 0x6C, 0xDC, 0x02, // GPSLongitude
        0xE8, 0x03, // GPSAltitude
        0xD0, 0x07, // GPSSpeed
        0x00, 0x00, // YawRate
        0x00, 0x00, // LateralAccel
        0x00, 0x00, // LongAccel
        0x00, 0x00, // SteeringAngle
        0xE8, 0x03, // WheelSpeedFL
        0xE8, 0x03, // WheelSpeedFR
        0xE8, 0x03, // WheelSpeedRL
        0xE8, 0x03, // WheelSpeedRR
    ];
    frame.resize(64, 0x00);
    frame
}

// ---------------------------------------------------------------------------
// LTL properties and build-frame signal values
// ---------------------------------------------------------------------------

/// `G(min <= signal <= max)` over integer bounds.
fn always_between(signal: &str, min: i64, max: i64) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(Predicate::Between {
        signal: signal.to_string(),
        min: Rational::integer(min),
        max: Rational::integer(max),
    })))
}

/// `G(signal < value)`.
fn always_less_than(signal: &str, value: Rational) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(Predicate::less_than(
        signal, value,
    ))))
}

fn can20_properties() -> Vec<Formula> {
    vec![
        always_between("EngineSpeed", 0, 8000),
        always_between("EngineTemp", -40, 215),
    ]
}

fn canfd_properties() -> Vec<Formula> {
    vec![
        always_between("GPSSpeed", 0, 655),
        always_between("YawRate", -327, 327),
        always_between("WheelSpeedFL", 0, 655),
    ]
}

/// The property templates for the scaling sweep (rotated to reach a count).
fn scaling_property(index: usize) -> Formula {
    match index % 10 {
        0 => always_between("EngineSpeed", 0, 8000),
        1 => always_between("EngineTemp", -40, 215),
        2 => always_less_than("BrakePressure", r(13107, 2)),
        3 => always_less_than("EngineSpeed", Rational::integer(7000)),
        4 => always_less_than("EngineTemp", Rational::integer(200)),
        5 => always_less_than("BrakePressure", Rational::integer(5000)),
        6 => always_between("EngineSpeed", 500, 7500),
        7 => always_between("EngineTemp", -20, 180),
        8 => always_between("BrakePressure", 0, 4000),
        _ => always_less_than("EngineSpeed", Rational::integer(6000)),
    }
}

fn make_properties(count: usize) -> Vec<Formula> {
    (0..count).map(scaling_property).collect()
}

fn can20_signals() -> Vec<SignalValue> {
    vec![
        SignalValue {
            name: "EngineSpeed".to_string(),
            value: Rational::integer(2000),
        },
        SignalValue {
            name: "EngineTemp".to_string(),
            value: Rational::integer(90),
        },
    ]
}

fn canfd_signals() -> Vec<SignalValue> {
    vec![
        SignalValue {
            name: "GPSSpeed".to_string(),
            value: Rational::integer(20),
        },
        SignalValue {
            name: "YawRate".to_string(),
            value: Rational::integer(0),
        },
        SignalValue {
            name: "WheelSpeedFL".to_string(),
            value: Rational::integer(10),
        },
        SignalValue {
            name: "WheelSpeedFR".to_string(),
            value: Rational::integer(10),
        },
    ]
}

// ---------------------------------------------------------------------------
// Statistics helpers (matching the Go / C++ formulas: sample stdev, linear-
// interpolated percentiles, round-to-one-decimal for the wire).
// ---------------------------------------------------------------------------

fn mean(xs: &[f64]) -> f64 {
    if xs.is_empty() {
        return 0.0;
    }
    xs.iter().sum::<f64>() / xs.len() as f64
}

fn sample_stdev(xs: &[f64]) -> f64 {
    if xs.len() < 2 {
        return 0.0;
    }
    let m = mean(xs);
    let ss: f64 = xs.iter().map(|x| (x - m) * (x - m)).sum();
    (ss / (xs.len() as f64 - 1.0)).sqrt()
}

fn min_of(xs: &[f64]) -> f64 {
    xs.iter().copied().fold(f64::INFINITY, f64::min)
}

fn max_of(xs: &[f64]) -> f64 {
    xs.iter().copied().fold(f64::NEG_INFINITY, f64::max)
}

fn percentile(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let k = (sorted.len() as f64 - 1.0) * p / 100.0;
    let f = k as usize;
    let c = if f + 1 < sorted.len() { f + 1 } else { f };
    sorted[f] + (k - f as f64) * (sorted[c] - sorted[f])
}

fn round1(x: f64) -> f64 {
    (x * 10.0).round() / 10.0
}

fn round3(x: f64) -> f64 {
    (x * 1000.0).round() / 1000.0
}

// ---------------------------------------------------------------------------
// System info & timestamp
// ---------------------------------------------------------------------------

/// The Rust toolchain that compiled this benchmark, queried at runtime (std
/// exposes no baked-in equivalent of Go's `runtime.Version()`); `"unknown"` if
/// `rustc` is not on `PATH`.
fn rustc_version() -> String {
    std::process::Command::new("rustc")
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn system_json() -> Value {
    let cores = std::thread::available_parallelism().map_or(0, std::num::NonZeroUsize::get);
    json!({
        "cpu": std::env::consts::ARCH,
        "cores": cores,
        "platform": std::env::consts::OS,
        "rust": rustc_version(),
    })
}

/// Format the current UTC time as `YYYY-MM-DDTHH:MM:SSZ` (Go's RFC3339 shape),
/// using a std-only civil-date conversion so the benchmark takes no new
/// dependency for a metadata field.
fn iso_timestamp() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs()) as i64;
    let days = secs.div_euclid(86_400);
    let tod = secs.rem_euclid(86_400);
    let (hh, mm, ss) = (tod / 3600, (tod % 3600) / 60, tod % 60);
    let (y, m, d) = civil_from_days(days);
    format!("{y:04}-{m:02}-{d:02}T{hh:02}:{mm:02}:{ss:02}Z")
}

/// Days-since-Unix-epoch -> `(year, month, day)` (Howard Hinnant's algorithm).
fn civil_from_days(days: i64) -> (i64, i64, i64) {
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// Progress/diagnostic line: stderr under `--json` (so stdout carries only the
/// JSON report), stdout otherwise.
fn log_line(json: bool, line: &str) {
    if json {
        eprintln!("{line}");
    } else {
        println!("{line}");
    }
}

// ---------------------------------------------------------------------------
// Per-lane workloads — each owns a fresh Client (fresh StreamState); the core
// library and GHC RTS are process-global, so this is cheap and mirrors the Go
// binding's per-lane client / the C++ binding's per-lane backend.
// ---------------------------------------------------------------------------

fn new_client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

fn bench_streaming(
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    props: &[Formula],
    num_frames: u64,
) -> f64 {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    client.set_properties(props).expect("set properties");
    client.start_stream().expect("start stream");
    let start = Instant::now();
    for i in 0..num_frames {
        client
            .send_frame(Timestamp(i), id, dlc, frame, None, None)
            .expect("send frame");
    }
    let elapsed = start.elapsed().as_secs_f64();
    client.end_stream().expect("end stream");
    num_frames as f64 / elapsed
}

fn bench_extraction(dbc: &Dbc, id: CanId, dlc: Dlc, frame: &[u8], num_frames: u64) -> f64 {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    let start = Instant::now();
    for _ in 0..num_frames {
        client
            .extract_signals(id, dlc, frame)
            .expect("extract signals");
    }
    let elapsed = start.elapsed().as_secs_f64();
    num_frames as f64 / elapsed
}

fn bench_building(dbc: &Dbc, dlc: Dlc, signals: &[SignalValue], num_frames: u64) -> f64 {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    let message = &dbc.messages[0];
    let start = Instant::now();
    for _ in 0..num_frames {
        client
            .build_frame(message, dlc, signals)
            .expect("build frame");
    }
    let elapsed = start.elapsed().as_secs_f64();
    num_frames as f64 / elapsed
}

// ---------------------------------------------------------------------------
// Throughput mode
// ---------------------------------------------------------------------------

/// One throughput lane: its wire name and a `frames -> fps` runner.
type Lane<'a> = (&'static str, Box<dyn Fn(u64) -> f64 + 'a>);

fn run_throughput(frames: u64, runs: usize, warmup: usize, json: bool) -> Vec<Value> {
    let dbc20 = can20_dbc();
    let dbcfd = canfd_dbc();
    let f20 = can20_frame();
    let ffd = canfd_frame();
    let id20 = CanId::standard(0x100).expect("valid standard id");
    let idfd = CanId::standard(0x200).expect("valid standard id");
    let dlc20 = Dlc::new(8).expect("valid dlc");
    let dlcfd = Dlc::new(15).expect("valid dlc");
    let p20 = can20_properties();
    let pfd = canfd_properties();
    let s20 = can20_signals();
    let sfd = canfd_signals();

    let lanes: Vec<Lane> = vec![
        (
            "CAN 2.0B: Stream LTL (2 props)",
            Box::new(|n| bench_streaming(&dbc20, id20, dlc20, &f20, &p20, n)),
        ),
        (
            "CAN 2.0B: Signal Extraction",
            Box::new(|n| bench_extraction(&dbc20, id20, dlc20, &f20, n)),
        ),
        (
            "CAN 2.0B: Frame Building",
            Box::new(|n| bench_building(&dbc20, dlc20, &s20, n)),
        ),
        (
            "CAN-FD:   Stream LTL (3 props)",
            Box::new(|n| bench_streaming(&dbcfd, idfd, dlcfd, &ffd, &pfd, n)),
        ),
        (
            "CAN-FD:   Signal Extraction",
            Box::new(|n| bench_extraction(&dbcfd, idfd, dlcfd, &ffd, n)),
        ),
        (
            "CAN-FD:   Frame Building",
            Box::new(|n| bench_building(&dbcfd, dlcfd, &sfd, n)),
        ),
    ];

    let mut results = Vec::new();
    for (name, run) in &lanes {
        let name: &str = name;
        log_line(json, &format!("\n{name}:"));
        for _ in 0..warmup {
            let _ = run(frames / 10);
        }
        let mut fps_list = Vec::new();
        for idx in 0..runs {
            let fps = run(frames);
            log_line(
                json,
                &format!("  Run {}/{}: {fps:.0} ops/sec", idx + 1, runs),
            );
            fps_list.push(fps);
        }
        if fps_list.is_empty() {
            continue;
        }
        let m = mean(&fps_list);
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        results.push(json!({
            "name": name,
            "frames": frames,
            "runs": runs,
            "fps_mean": round1(m),
            "fps_stdev": round1(sample_stdev(&fps_list)),
            "fps_min": round1(min_of(&fps_list)),
            "fps_max": round1(max_of(&fps_list)),
            "us_per_frame": round1(us_per_frame),
        }));
    }
    results
}

// ---------------------------------------------------------------------------
// Latency mode
// ---------------------------------------------------------------------------

fn measure_stream_lat(
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    props: &[Formula],
    ops: usize,
    warmup: usize,
) -> Vec<f64> {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    client.set_properties(props).expect("set properties");
    client.start_stream().expect("start stream");
    for i in 0..warmup {
        client
            .send_frame(Timestamp(i as u64), id, dlc, frame, None, None)
            .expect("send frame");
    }
    let mut latencies = Vec::with_capacity(ops);
    for i in 0..ops {
        let start = Instant::now();
        client
            .send_frame(Timestamp((warmup + i) as u64), id, dlc, frame, None, None)
            .expect("send frame");
        latencies.push(start.elapsed().as_nanos() as f64 / 1000.0);
    }
    client.end_stream().expect("end stream");
    latencies
}

fn measure_extract_lat(
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    ops: usize,
    warmup: usize,
) -> Vec<f64> {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    for _ in 0..warmup {
        client
            .extract_signals(id, dlc, frame)
            .expect("extract signals");
    }
    let mut latencies = Vec::with_capacity(ops);
    for _ in 0..ops {
        let start = Instant::now();
        client
            .extract_signals(id, dlc, frame)
            .expect("extract signals");
        latencies.push(start.elapsed().as_nanos() as f64 / 1000.0);
    }
    latencies
}

fn measure_build_lat(
    dbc: &Dbc,
    dlc: Dlc,
    signals: &[SignalValue],
    ops: usize,
    warmup: usize,
) -> Vec<f64> {
    let client = new_client();
    client.parse_dbc(dbc).expect("parse dbc");
    let message = &dbc.messages[0];
    for _ in 0..warmup {
        client
            .build_frame(message, dlc, signals)
            .expect("build frame");
    }
    let mut latencies = Vec::with_capacity(ops);
    for _ in 0..ops {
        let start = Instant::now();
        client
            .build_frame(message, dlc, signals)
            .expect("build frame");
        latencies.push(start.elapsed().as_nanos() as f64 / 1000.0);
    }
    latencies
}

fn analyze_latencies(name: &str, raw: &[f64]) -> Value {
    let mut sorted = raw.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("latencies are finite"));
    json!({
        "name": name,
        "count": raw.len(),
        "mean_us": round1(mean(raw)),
        "min_us": round1(min_of(raw)),
        "max_us": round1(max_of(raw)),
        "p50_us": round1(percentile(&sorted, 50.0)),
        "p90_us": round1(percentile(&sorted, 90.0)),
        "p99_us": round1(percentile(&sorted, 99.0)),
        "p999_us": round1(percentile(&sorted, 99.9)),
    })
}

/// Parameters describing one latency suite (one frame type × three lanes),
/// bundled so the runner takes a single argument.
struct LatSuite<'a> {
    label: &'a str,
    dbc: &'a Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &'a [u8],
    props: &'a [Formula],
    signals: &'a [SignalValue],
    ops: usize,
    warmup: usize,
}

fn run_latency_suite(s: &LatSuite) -> Vec<Value> {
    let stream = measure_stream_lat(s.dbc, s.id, s.dlc, s.frame, s.props, s.ops, s.warmup);
    let extract = measure_extract_lat(s.dbc, s.id, s.dlc, s.frame, s.ops, s.warmup);
    let build = measure_build_lat(s.dbc, s.dlc, s.signals, s.ops, s.warmup);
    vec![
        analyze_latencies(&format!("{} Streaming LTL", s.label), &stream),
        analyze_latencies(&format!("{} Signal Extraction", s.label), &extract),
        analyze_latencies(&format!("{} Frame Building", s.label), &build),
    ]
}

fn run_latency(ops: usize, warmup: usize, json: bool) -> Vec<Value> {
    let dbc20 = can20_dbc();
    let dbcfd = canfd_dbc();
    let f20 = can20_frame();
    let ffd = canfd_frame();
    let p20 = can20_properties();
    let pfd = canfd_properties();
    let s20 = can20_signals();
    let sfd = canfd_signals();

    log_line(json, "\nMeasuring CAN 2.0B latency...");
    let mut results = run_latency_suite(&LatSuite {
        label: "CAN 2.0B",
        dbc: &dbc20,
        id: CanId::standard(0x100).expect("valid standard id"),
        dlc: Dlc::new(8).expect("valid dlc"),
        frame: &f20,
        props: &p20,
        signals: &s20,
        ops,
        warmup,
    });
    log_line(json, "\nMeasuring CAN-FD latency...");
    results.extend(run_latency_suite(&LatSuite {
        label: "CAN-FD",
        dbc: &dbcfd,
        id: CanId::standard(0x200).expect("valid standard id"),
        dlc: Dlc::new(15).expect("valid dlc"),
        frame: &ffd,
        props: &pfd,
        signals: &sfd,
        ops,
        warmup,
    }));
    results
}

// ---------------------------------------------------------------------------
// Scaling mode (property-count sweep, CAN 2.0B)
// ---------------------------------------------------------------------------

fn run_scaling(frames: u64, runs: usize, json: bool) -> Vec<Value> {
    let dbc20 = can20_dbc();
    let f20 = can20_frame();
    let id20 = CanId::standard(0x100).expect("valid standard id");
    let dlc20 = Dlc::new(8).expect("valid dlc");
    let counts = [1usize, 2, 3, 5, 7, 10];

    // Warmup with a single property.
    let _ = bench_streaming(&dbc20, id20, dlc20, &f20, &make_properties(1), frames / 10);

    let mut results = Vec::new();
    let mut baseline: Option<f64> = None;
    for &count in &counts {
        let props = make_properties(count);
        let mut fps_list = Vec::new();
        for _ in 0..runs {
            fps_list.push(bench_streaming(&dbc20, id20, dlc20, &f20, &props, frames));
        }
        if fps_list.is_empty() {
            continue;
        }
        let m = mean(&fps_list);
        let base = *baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        log_line(
            json,
            &format!("  {count} props: {m:.0} fps ({relative:.2}x)"),
        );
        results.push(json!({
            "properties": count,
            "fps": round1(m),
            "us_per_frame": round1(us_per_frame),
            "relative": round3(relative),
        }));
    }
    results
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

struct Args {
    mode: String,
    frames: u64,
    runs: usize,
    warmup: usize,
    ops: usize,
    json: bool,
}

fn parse_num<T: std::str::FromStr>(argv: &[String], i: usize, flag: &str) -> T {
    argv.get(i).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        eprintln!("{flag} requires a numeric argument");
        std::process::exit(1);
    })
}

fn parse_args() -> Args {
    let argv: Vec<String> = std::env::args().skip(1).collect();

    // First positional argument (not a flag) selects the mode.
    let mut i = 0;
    let mut mode = "throughput".to_string();
    if let Some(first) = argv.first() {
        if !first.starts_with('-') {
            mode = first.clone();
            i = 1;
        }
    }

    let mut frames: Option<u64> = None;
    let mut runs: Option<usize> = None;
    let mut warmup: Option<usize> = None;
    let mut ops: Option<usize> = None;
    let mut json = false;
    let mut quick = false;

    while i < argv.len() {
        match argv[i].as_str() {
            "--json" => json = true,
            "--quick" => quick = true,
            "--frames" => {
                i += 1;
                frames = Some(parse_num(&argv, i, "--frames"));
            }
            "--runs" => {
                i += 1;
                runs = Some(parse_num(&argv, i, "--runs"));
            }
            "--warmup" => {
                i += 1;
                warmup = Some(parse_num(&argv, i, "--warmup"));
            }
            "--ops" => {
                i += 1;
                ops = Some(parse_num(&argv, i, "--ops"));
            }
            other => {
                eprintln!("Unknown option: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    // `--quick` lowers the default sizes for a fast smoke run; explicit flags
    // still take precedence. It is a Rust-only convenience (Go/C++ have no such
    // flag) — `run_all.sh` drives the suite with explicit sizes, never `--quick`.
    let (def_frames, def_runs, def_ops) = if quick {
        (1000u64, 2usize, 1000usize)
    } else {
        (10_000u64, 5usize, 5000usize)
    };

    Args {
        mode,
        frames: frames.unwrap_or(def_frames),
        runs: runs.unwrap_or(def_runs),
        warmup: warmup.unwrap_or(2),
        ops: ops.unwrap_or(def_ops),
        json,
    }
}

fn main() {
    let args = parse_args();
    let lib = std::env::var("ALETHEIA_LIB").unwrap_or_else(|_| "libaletheia-ffi.so".to_string());
    log_line(
        args.json,
        &format!("Aletheia Rust Benchmark ({})", args.mode),
    );
    log_line(args.json, &format!("Library: {lib}"));

    let results = match args.mode.as_str() {
        "throughput" => {
            log_line(args.json, &format!("Frames per run: {}", args.frames));
            log_line(args.json, &format!("Runs: {}", args.runs));
            run_throughput(args.frames, args.runs, args.warmup, args.json)
        }
        "latency" => {
            log_line(args.json, &format!("Operations: {}", args.ops));
            run_latency(args.ops, args.warmup, args.json)
        }
        "scaling" => {
            log_line(args.json, &format!("Frames per run: {}", args.frames));
            run_scaling(args.frames, args.runs, args.json)
        }
        other => {
            eprintln!("Unknown mode: {other} (use throughput, latency, or scaling)");
            std::process::exit(1);
        }
    };

    if args.json {
        let output = json!({
            "benchmark": args.mode,
            "language": "rust",
            "timestamp": iso_timestamp(),
            "system": system_json(),
            "results": results,
        });
        println!(
            "{}",
            serde_json::to_string_pretty(&output).expect("serialize benchmark JSON")
        );
    }
}

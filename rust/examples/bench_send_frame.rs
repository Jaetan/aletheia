// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Micro-benchmark: per-`send_frame` cost through the binary FFI fast path.
//!
//! Measures the steady-state throughput of [`Client::send_frame`] against the
//! real shared library — the loop every production consumer sits in. Run it
//! release-built, pointing `ALETHEIA_LIB` at the built core:
//!
//! ```sh
//! ALETHEIA_LIB=/path/to/build/libaletheia-ffi.so \
//!     cargo run --release --example bench_send_frame [frames]
//! ```
//!
//! The workload mirrors `tests/typed_client.rs`: parse the shared corpus DBC,
//! bind one property (`G(EngineSpeed < 1000)`), start the stream, then send
//! `frames` (default 100 000) non-violating frames — each one an `ack`, so the
//! numbers isolate the frame path rather than verdict decoding. WSL2 caveat:
//! back-to-back runs jitter about ±5%; compare medians of several runs.

use std::time::Instant;

use aletheia::{CanId, Client, Dlc, Formula, FrameResponse, Predicate, Rational, Timestamp};

/// The shared corpus fixture: `EngineSpeed` in message 256, bits 0..16,
/// little-endian, factor 0.25 (raw `N` decodes to `N * 0.25` rpm).
const DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

/// Frames sent before the timed window (RTS + allocator warm-up).
const WARMUP_FRAMES: u64 = 1_000;
/// Timed frames when no count is given on the command line.
const DEFAULT_FRAMES: u64 = 100_000;

fn engine_speed_frame(rpm: u32) -> [u8; 8] {
    let raw = (rpm * 4) as u16; // raw = rpm / 0.25
    [raw as u8, (raw >> 8) as u8, 0, 0, 0, 0, 0, 0]
}

fn main() {
    let frames: u64 = std::env::args().nth(1).map_or(DEFAULT_FRAMES, |arg| {
        arg.parse().expect("frame count must be a positive integer")
    });

    let client =
        Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?");
    client.parse_dbc_text(DBC).expect("parse DBC text");

    // One bound property, never decided by the frames below (500 rpm < 1000),
    // so every send is the cheap `ack` path.
    let prop = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "EngineSpeed".to_string(),
        value: Rational::integer(1000),
    })));
    client.set_properties(&[prop]).expect("set properties");
    client.start_stream().expect("start stream");

    let id = CanId::standard(256).expect("256 is a valid standard ID");
    let dlc = Dlc::new(8).expect("8 is a valid DLC");
    let data = engine_speed_frame(500);

    let mut acks: u64 = 0;
    let mut send = |ts: u64| {
        let resp = client
            .send_frame(Timestamp(ts), id, dlc, &data, None, None)
            .expect("send frame");
        if matches!(resp, FrameResponse::Ack) {
            acks += 1;
        }
    };

    for ts in 0..WARMUP_FRAMES {
        send(ts);
    }

    let start = Instant::now();
    for ts in WARMUP_FRAMES..WARMUP_FRAMES + frames {
        send(ts);
    }
    let elapsed = start.elapsed();

    let _final = client.end_stream().expect("end stream");

    assert_eq!(
        acks,
        WARMUP_FRAMES + frames,
        "every non-violating frame must ack"
    );

    let secs = elapsed.as_secs_f64();
    let per_call_ns = elapsed.as_nanos() as f64 / frames as f64;
    println!("frames:        {frames}");
    println!("elapsed:       {secs:.3} s");
    println!("per send_frame: {per_call_ns:.0} ns");
    println!("throughput:    {:.0} frames/sec", frames as f64 / secs);
}

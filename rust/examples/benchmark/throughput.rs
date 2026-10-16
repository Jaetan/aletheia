// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The client, the per-operation kernels and the throughput mode.

use std::io;
use std::time::Instant;

use aletheia::{CanId, Client, Dbc, Dlc, Formula, SignalValue, Timestamp};
use serde_json::{json, Value};

use crate::fixtures::{
    can20_dbc, can20_frame, can20_properties, can20_signals, canfd_dbc, canfd_frame,
    canfd_properties, canfd_signals,
};
use crate::stats::{max_of, mean, min_of, round1, sample_stdev};
use crate::Output;

// ---------------------------------------------------------------------------
// Per-lane workloads — each owns a fresh Client (fresh StreamState); the core
// library and GHC RTS are process-global, so this is cheap and mirrors the Go
// binding's per-lane client / the C++ binding's per-lane backend.
// ---------------------------------------------------------------------------

pub(crate) fn new_client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

pub(crate) fn bench_streaming(
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

pub(crate) fn run_throughput(
    out: &mut Output<'_>,
    frames: u64,
    runs: usize,
    warmup: usize,
) -> io::Result<Vec<Value>> {
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
        out.line(&format!("\n{name}:"))?;
        for _ in 0..warmup {
            let _ = run(frames / 10);
        }
        let mut fps_list = Vec::new();
        for idx in 0..runs {
            let fps = run(frames);
            out.line(&format!("  Run {}/{}: {fps:.0} ops/sec", idx + 1, runs))?;
            fps_list.push(fps);
        }
        // A lane with no measurement is a hard error, never an omitted row: an
        // omitted lane makes the report silently non-conformant with
        // benchmarks/SCHEMA.yaml and reads as "not measured yet" rather than
        // "broken".  Measurement errors already abort (the bench fns panic), so
        // this is reachable only for `--runs 0`.
        assert!(
            !fps_list.is_empty(),
            "lane {name:?} produced no measurement (runs = {runs})"
        );
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
    Ok(results)
}

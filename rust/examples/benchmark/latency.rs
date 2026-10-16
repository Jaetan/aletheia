// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Latency mode: each operation timed on its own, every lane reported by its
//! mean, its extremes and its percentiles.

use std::io;
use std::time::Instant;

use aletheia::{CanId, Dbc, Dlc, Formula, SignalValue, Timestamp};
use serde_json::{json, Value};

use crate::fixtures::{
    can20_dbc, can20_frame, can20_properties, can20_signals, canfd_dbc, canfd_frame,
    canfd_properties, canfd_signals,
};
use crate::stats::{max_of, mean, min_of, percentile, round1};
use crate::throughput::new_client;
use crate::Output;

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
    // Same rule as the throughput and scaling lanes: no sample is a fatal error,
    // never a published row.  Without this, `--ops 0` emits a schema-CONFORMANT
    // row of fabricated values (count 0, mean 0.0, min/max null) and exits 0 — a
    // lane reported as measured that never ran, which the baseline schema gate
    // cannot distinguish from a real one.
    assert!(
        !raw.is_empty(),
        "latency lane {name:?} produced no measurement (ops = 0)"
    );
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

pub(crate) fn run_latency(
    out: &mut Output<'_>,
    ops: usize,
    warmup: usize,
) -> io::Result<Vec<Value>> {
    let dbc20 = can20_dbc();
    let dbcfd = canfd_dbc();
    let f20 = can20_frame();
    let ffd = canfd_frame();
    let p20 = can20_properties();
    let pfd = canfd_properties();
    let s20 = can20_signals();
    let sfd = canfd_signals();

    out.line("\nMeasuring CAN 2.0B latency...")?;
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
    out.line("\nMeasuring CAN-FD latency...")?;
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
    Ok(results)
}

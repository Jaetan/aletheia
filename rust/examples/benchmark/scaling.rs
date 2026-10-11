// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Scaling mode: the sweeps the report carries under its dict-shaped results.

use std::time::Instant;

use aletheia::{CanId, Dbc, Dlc, Formula, Predicate, Rational};
use serde_json::{json, Value};

use crate::fixtures::{
    always_between, always_less_than, can20_dbc, can20_frame, canfd_dbc, canfd_frame,
    make_properties, r, sized_dbc,
};
use crate::log_line;
use crate::stats::{mean, min_of, round1, round3, round4};
use crate::throughput::{bench_streaming, new_client};

// ---------------------------------------------------------------------------
// Scaling mode: the sweeps under one dict-shaped payload, in the order the
// cross-binding schema (benchmarks/SCHEMA.yaml, tools/check_bench_schema.py)
// pins across all four bindings: trace_size_can20, trace_size_canfd,
// property_count, property_complexity, dbc_size. A streaming sweep's point is
// the MEAN fps over `runs` streaming passes, `relative = fps / (fps of the
// first row)`; a dbc_size point is the MINIMUM load time over `runs` loads,
// `relative = messages_per_sec / (messages_per_sec of the first row)`.
// Rounding: fps / us_per_frame / messages_per_sec -> 1 dp, relative -> 3 dp,
// seconds -> 4 dp (identical to Go / Python).
// ---------------------------------------------------------------------------

/// Mean streaming fps over `runs` passes (the robust methodology — noise on an
/// un-averaged baseline row would multiply into every `relative` in the sweep).
fn mean_fps(
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    props: &[Formula],
    num_frames: u64,
    runs: usize,
) -> f64 {
    let mut fps_list = Vec::with_capacity(runs);
    for _ in 0..runs {
        fps_list.push(bench_streaming(dbc, id, dlc, frame, props, num_frames));
    }
    // Never average an empty sample: `mean` would yield a fabricated 0.0 that is
    // reported as a measurement and divides through every `relative` in the
    // sweep.  Measurement errors already abort (the bench fns panic), so this is
    // reachable only for `--runs 0`.
    assert!(
        !fps_list.is_empty(),
        "scaling point ({num_frames} frames) has no measurement (runs = {runs})"
    );
    mean(&fps_list)
}

/// Trace-size sweep points; `--quick` drops the largest.
fn trace_sizes(quick: bool) -> Vec<u64> {
    if quick {
        vec![1000, 5000, 10000, 50000]
    } else {
        vec![1000, 5000, 10000, 50000, 100000]
    }
}

/// Sweep one frame type over trace sizes; rows carry `{frames, fps, relative}`.
#[allow(clippy::too_many_arguments)]
fn scan_trace_size(
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    props: &[Formula],
    sizes: &[u64],
    runs: usize,
    json: bool,
    label: &str,
) -> Vec<Value> {
    let mut rows = Vec::new();
    let mut baseline: Option<f64> = None;
    for &size in sizes {
        let m = mean_fps(dbc, id, dlc, frame, props, size, runs);
        let base = *baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        log_line(
            json,
            &format!("  {label} {size} frames: {m:.0} fps ({relative:.2}x)"),
        );
        rows.push(json!({
            "frames": size,
            "fps": round1(m),
            "relative": round3(relative),
        }));
    }
    rows
}

/// The five property-complexity levels (verbatim labels, CAN 2.0B), in order.
/// The `Implication` level uses the binding's `Formula::implies` helper; the
/// `BrakePressure` bound in `Three predicates` is the rational `13107/2`.
fn complexity_levels() -> Vec<(&'static str, Vec<Formula>)> {
    let implication = Formula::Always(Box::new(Formula::implies(
        Formula::Atomic(Predicate::less_than("EngineSpeed", Rational::integer(1000))),
        Formula::Atomic(Predicate::less_than("EngineTemp", Rational::integer(100))),
    )));
    vec![
        (
            "Simple predicate",
            vec![always_less_than("EngineSpeed", Rational::integer(8000))],
        ),
        (
            "Range predicate",
            vec![always_between("EngineSpeed", 0, 8000)],
        ),
        (
            "Two predicates (AND)",
            vec![
                always_between("EngineSpeed", 0, 8000),
                always_between("EngineTemp", -40, 215),
            ],
        ),
        (
            "Three predicates",
            vec![
                always_between("EngineSpeed", 0, 8000),
                always_between("EngineTemp", -40, 215),
                always_less_than("BrakePressure", r(13107, 2)),
            ],
        ),
        ("Implication", vec![implication]),
    ]
}

/// DBC-size sweep points (messages per DBC), each double the one before;
/// `--quick` drops the smallest.
fn dbc_sizes(quick: bool) -> Vec<u32> {
    if quick {
        vec![2500, 5000, 10000]
    } else {
        vec![1250, 2500, 5000, 10000]
    }
}

/// Wall-clock seconds of one `parse_dbc` of `dbc` into a fresh client. Only the
/// call is timed: the client is created before the clock starts, and the loaded
/// document and the client (whose drop closes it) are dropped after it stops.
fn load_seconds(dbc: &Dbc) -> f64 {
    let client = new_client();
    let start = Instant::now();
    let loaded = client.parse_dbc(dbc).expect("parse dbc");
    let elapsed = start.elapsed().as_secs_f64();
    drop(loaded);
    elapsed
}

/// Minimum load time over `runs` loads: the sweep compares two sizes' times,
/// and the minimum is the least noisy estimate of the work.
fn min_load_seconds(dbc: &Dbc, runs: usize) -> f64 {
    let secs_list: Vec<f64> = (0..runs).map(|_| load_seconds(dbc)).collect();
    // Never take the minimum of an empty sample: `min_of` would yield a
    // fabricated infinity reported as a measurement.  Load errors already abort
    // (`load_seconds` panics), so this is reachable only for `--runs 0`.
    assert!(
        !secs_list.is_empty(),
        "dbc_size point ({} messages) has no measurement (runs = {runs})",
        dbc.messages.len()
    );
    min_of(&secs_list)
}

/// Sweep DBC sizes; rows carry `{messages, seconds, messages_per_sec, relative}`.
fn scan_dbc_size(sizes: &[u32], runs: usize, json: bool) -> Vec<Value> {
    let mut rows = Vec::new();
    let mut baseline: Option<f64> = None;
    for &size in sizes {
        let secs = min_load_seconds(&sized_dbc(size), runs);
        let per_sec = f64::from(size) / secs;
        let base = *baseline.get_or_insert(per_sec);
        let relative = if base > 0.0 { per_sec / base } else { 0.0 };
        log_line(
            json,
            &format!("  {size} messages: {secs:.4} s, {per_sec:.0} messages/sec ({relative:.2}x)"),
        );
        rows.push(json!({
            "messages": size,
            "seconds": round4(secs),
            "messages_per_sec": round1(per_sec),
            "relative": round3(relative),
        }));
    }
    rows
}

/// Run the scaling sweeps and return them as ordered `(key, rows)` pairs
/// (the caller emits them in this order — the schema pins it).
pub(crate) fn run_scaling(runs: usize, quick: bool, json: bool) -> Vec<(&'static str, Value)> {
    let dbc20 = can20_dbc();
    let dbcfd = canfd_dbc();
    let f20 = can20_frame();
    let ffd = canfd_frame();
    let id20 = CanId::standard(0x100).expect("valid standard id");
    let idfd = CanId::standard(0x200).expect("valid standard id");
    let dlc20 = Dlc::new(8).expect("valid dlc");
    let dlcfd = Dlc::new(15).expect("valid dlc");
    let num_frames: u64 = if quick { 5000 } else { 10000 };
    let sizes = trace_sizes(quick);

    // Warmup with a single property.
    let _ = bench_streaming(&dbc20, id20, dlc20, &f20, &make_properties(1), 1000);

    // 1 & 2: trace-size sweeps (CAN 2.0B then CAN-FD).
    log_line(json, "\nTrace size scaling (CAN 2.0B):");
    let trace20 = scan_trace_size(
        &dbc20,
        id20,
        dlc20,
        &f20,
        &[always_between("EngineSpeed", 0, 8000)],
        &sizes,
        runs,
        json,
        "CAN 2.0B",
    );
    log_line(json, "\nTrace size scaling (CAN-FD):");
    let tracefd = scan_trace_size(
        &dbcfd,
        idfd,
        dlcfd,
        &ffd,
        &[always_between("GPSSpeed", 0, 655)],
        &sizes,
        runs,
        json,
        "CAN-FD",
    );

    // 3: property-count sweep (10 templates cycled by i mod 10), CAN 2.0B.
    log_line(json, "\nProperty count scaling (CAN 2.0B):");
    let counts = [1usize, 2, 3, 5, 7, 10];
    let mut pc_rows = Vec::new();
    let mut pc_baseline: Option<f64> = None;
    for &count in &counts {
        let props = make_properties(count);
        let m = mean_fps(&dbc20, id20, dlc20, &f20, &props, num_frames, runs);
        let base = *pc_baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        log_line(
            json,
            &format!("  {count} props: {m:.0} fps ({relative:.2}x)"),
        );
        pc_rows.push(json!({
            "properties": count,
            "fps": round1(m),
            "us_per_frame": round1(us_per_frame),
            "relative": round3(relative),
        }));
    }

    // 4: property-complexity sweep, CAN 2.0B.
    log_line(json, "\nProperty complexity scaling (CAN 2.0B):");
    let mut cx_rows = Vec::new();
    let mut cx_baseline: Option<f64> = None;
    for (label, props) in complexity_levels() {
        let m = mean_fps(&dbc20, id20, dlc20, &f20, &props, num_frames, runs);
        let base = *cx_baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        log_line(json, &format!("  {label}: {m:.0} fps ({relative:.2}x)"));
        cx_rows.push(json!({
            "complexity": label,
            "fps": round1(m),
            "us_per_frame": round1(us_per_frame),
            "relative": round3(relative),
        }));
    }

    // 5: DBC-size sweep, after one untimed warm-up load of a 500-message DBC.
    let _ = load_seconds(&sized_dbc(500));
    log_line(json, "\nDBC size scaling:");
    let dbc_rows = scan_dbc_size(&dbc_sizes(quick), runs, json);

    vec![
        ("trace_size_can20", Value::Array(trace20)),
        ("trace_size_canfd", Value::Array(tracefd)),
        ("property_count", Value::Array(pc_rows)),
        ("property_complexity", Value::Array(cx_rows)),
        ("dbc_size", Value::Array(dbc_rows)),
    ]
}

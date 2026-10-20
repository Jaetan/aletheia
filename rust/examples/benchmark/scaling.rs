// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Scaling mode: the sweeps the report carries under its dict-shaped results.

use std::io;
use std::time::Instant;

use aletheia::{CanId, Client, Dbc, Dlc, Formula, ParsedDbc, Predicate, Rational};
use serde_json::{json, Value};

use crate::fixtures::{
    always_between, always_less_than, can20_dbc, can20_frame, canfd_dbc, canfd_frame,
    make_properties, r, sized_dbc,
};
use crate::stats::{mean, min_of, round1, round3, round4};
use crate::throughput::{bench_streaming, new_client};
use crate::Output;

// ---------------------------------------------------------------------------
// Scaling mode: the sweeps under one dict-shaped payload, in the order the
// cross-binding schema (benchmarks/SCHEMA.yaml, tools/check_bench_schema.py)
// pins across all four bindings: trace_size_can20, trace_size_canfd,
// property_count, property_complexity, dbc_size, text_literal_length,
// json_literal_length. A streaming sweep's point is the MEAN fps over `runs`
// streaming passes, `relative = fps / (fps of the first row)`; a load sweep's
// point (dbc_size and the two literal sweeps) is the MINIMUM load time and the
// MINIMUM allocated bytes over `runs` loads, `relative` its messages_per_sec or
// digits_per_sec over the first row's.
// Rounding: fps / us_per_frame / messages_per_sec / digits_per_sec -> 1 dp,
// relative -> 3 dp, seconds -> 4 dp, allocated_bytes an integer (identical to
// Go / Python).
// ---------------------------------------------------------------------------

/// Mean streaming fps over `runs` passes (the robust methodology; noise on an
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
    out: &mut Output<'_>,
    dbc: &Dbc,
    id: CanId,
    dlc: Dlc,
    frame: &[u8],
    props: &[Formula],
    sizes: &[u64],
    runs: usize,
    label: &str,
) -> io::Result<Vec<Value>> {
    let mut rows = Vec::new();
    let mut baseline: Option<f64> = None;
    for &size in sizes {
        let m = mean_fps(dbc, id, dlc, frame, props, size, runs);
        let base = *baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        out.line(&format!(
            "  {label} {size} frames: {m:.0} fps ({relative:.2}x)"
        ))?;
        rows.push(json!({
            "frames": size,
            "fps": round1(m),
            "relative": round3(relative),
        }));
    }
    Ok(rows)
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

/// The literal sweeps' points (zeros after `1.` in the one factor), each
/// double the one before; `--quick` drops the smallest.
fn literal_lengths(quick: bool) -> Vec<u32> {
    if quick {
        vec![25000, 50000, 100000]
    } else {
        vec![12500, 25000, 50000, 100000]
    }
}

/// The DBC text of one message and one signal whose factor is `1.` followed
/// by `digits` zeros, which the kernel reduces to 1, so the load succeeds at
/// any length the kernel's DBC text bound admits.
fn literal_dbc_text(digits: u32) -> String {
    format!(
        concat!(
            "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n",
            "BO_ 200 Msg: 8 ECU\n",
            " SG_ Sel : 0|8@1+ (1.{zeros},0) [0|255] \"\" ECU\n",
        ),
        zeros = "0".repeat(digits as usize),
    )
}

/// The `parseDBC` command of [`literal_dbc_text`]'s DBC, one line of JSON
/// with no spaces. The factor is spliced in as written, since a JSON encoder
/// would write the number as 1.
fn literal_dbc_command(digits: u32) -> String {
    const HEAD: &str = concat!(
        r#"{"type":"command","command":"parseDBC","dbc":{"version":"","messages":[{"id":200,"#,
        r#""name":"Msg","dlc":8,"sender":"ECU","senders":[],"extended":false,"signals":[{"#,
        r#""name":"Sel","startBit":0,"length":8,"byteOrder":"little_endian","signed":false,"#,
        r#""factor":1."#,
    );
    const TAIL: &str = concat!(
        r#","offset":0,"minimum":0,"maximum":255,"unit":"","presence":"always","#,
        r#""receivers":["ECU"],"valueDescriptions":[]}]}],"signalGroups":[],"#,
        r#""environmentVars":[],"valueTables":[],"nodes":[{"name":"ECU"}],"comments":[],"#,
        r#""attributes":[],"unresolvedValueDescs":[]}}"#,
    );
    format!("{HEAD}{zeros}{TAIL}", zeros = "0".repeat(digits as usize))
}

/// Load `dbc` into `client`.
fn load_dbc(client: &Client, dbc: &Dbc) -> ParsedDbc {
    client.parse_dbc(dbc).expect("parse dbc")
}

/// Load `text`, the [`literal_dbc_text`] of `digits` zeros, into `client`: a
/// refusal ends the program naming it, and is never a recorded point.
fn load_text(client: &Client, text: &str, digits: u32) -> ParsedDbc {
    client.parse_dbc_text(text).unwrap_or_else(|err| {
        panic!("the text_literal_length load at {digits} digits was refused: {err}")
    })
}

/// What a load leaves, accepted once the count is read on both sides of the
/// load, so the acceptance is neither timed nor counted.
trait Loaded {
    /// Accept the load, or end the program naming its refusal.
    fn accept(self);
}

/// A typed load ends the program on a refusal, so the document it leaves is
/// accepted as it is.
impl Loaded for ParsedDbc {
    fn accept(self) {}
}

/// The kernel's raw answer to the [`literal_dbc_command`] of `digits` zeros.
struct Answer {
    digits: u32,
    raw: String,
}

/// An answer other than a success ends the program naming it, and is never a
/// recorded point.
impl Loaded for Answer {
    fn accept(self) {
        let answer: Value = serde_json::from_str(&self.raw).unwrap_or(Value::Null);
        assert!(
            answer["status"] == "success",
            "the json_literal_length load at {} digits was refused: {}",
            self.digits,
            self.raw
        );
    }
}

/// Send `command`, the [`literal_dbc_command`] of `digits` zeros, through
/// `client`'s raw command path.
fn send_command(client: &Client, command: &str, digits: u32) -> Answer {
    let raw = client.process(command).unwrap_or_else(|err| {
        panic!("the json_literal_length command at {digits} digits failed: {err}")
    });
    Answer { digits, raw }
}

/// One load's cost: its wall time, and the bytes the runtime allocated
/// across it.
struct LoadCost {
    seconds: f64,
    allocated_bytes: u64,
}

/// The bytes the kernel's runtime has allocated so far in the process.
fn allocated() -> u64 {
    aletheia::allocated_bytes()
        .expect("an open client has started the runtime, so there is a count to read")
}

/// The cost of one `load` into a fresh client. Only the call is timed, and
/// the count is read on both sides of the timed span, each read running a
/// collection: the client is opened before the first read, so its session is
/// not the load's, and what the load leaves is accepted, and the client
/// (whose drop closes it) dropped, after the second.
fn load_cost<T: Loaded>(load: impl FnOnce(&Client) -> T) -> LoadCost {
    let client = new_client();
    let before = allocated();
    let start = Instant::now();
    let loaded = load(&client);
    let seconds = start.elapsed().as_secs_f64();
    let after = allocated();
    loaded.accept();
    LoadCost {
        seconds,
        allocated_bytes: after
            .checked_sub(before)
            .expect("the runtime's allocation count never falls"),
    }
}

/// The least time and the least allocated bytes over `runs` loads, each taken
/// on its own: a sweep compares two sizes' costs, and the minimum is the least
/// noisy estimate of the work. `point` names the point in a failure.
fn min_load_cost<T: Loaded>(point: &str, runs: usize, load: impl Fn(&Client) -> T) -> LoadCost {
    let costs: Vec<LoadCost> = (0..runs).map(|_| load_cost(&load)).collect();
    // Never take the minimum of an empty sample: `min_of` would yield a
    // fabricated infinity reported as a measurement.  Load errors already abort
    // (each load panics), so this is reachable only for `--runs 0`.
    assert!(
        !costs.is_empty(),
        "{point} has no measurement (runs = {runs})"
    );
    let seconds: Vec<f64> = costs.iter().map(|cost| cost.seconds).collect();
    LoadCost {
        seconds: min_of(&seconds),
        allocated_bytes: costs
            .iter()
            .map(|cost| cost.allocated_bytes)
            .min()
            .expect("a sample that is not empty has a least cost"),
    }
}

/// Sweep one load over `sizes`, each a count of `unit`: a point is the
/// [`min_load_cost`] of the load `load_of(size)` makes, its rate the size over
/// the seconds, and `relative` the rate over the first row's. Rows carry
/// `{<unit>, seconds, allocated_bytes, <unit>_per_sec, relative}`, and the
/// table ends on the line `Expected: <expected>`.
fn scan_load<T: Loaded, L: Fn(&Client) -> T>(
    out: &mut Output<'_>,
    sweep: &str,
    unit: &str,
    expected: &str,
    sizes: &[u32],
    runs: usize,
    load_of: impl Fn(u32) -> L,
) -> io::Result<Vec<Value>> {
    let rate = format!("{unit}_per_sec");
    let mut rows = Vec::new();
    let mut baseline: Option<f64> = None;
    for &size in sizes {
        let cost = min_load_cost(
            &format!("{sweep} point ({size} {unit})"),
            runs,
            load_of(size),
        );
        let (secs, bytes) = (cost.seconds, cost.allocated_bytes);
        let per_sec = f64::from(size) / secs;
        let base = *baseline.get_or_insert(per_sec);
        let relative = if base > 0.0 { per_sec / base } else { 0.0 };
        out.line(&format!(
            "  {size} {unit}: {secs:.4} s, {bytes} bytes allocated, \
             {per_sec:.0} {unit}/sec ({relative:.2}x)"
        ))?;
        // The size's key is the unit, and the rate's is `rate`.
        rows.push(json!({
            unit: size,
            "seconds": round4(secs),
            "allocated_bytes": bytes,
            rate.as_str(): round1(per_sec),
            "relative": round3(relative),
        }));
    }
    out.line(&format!("Expected: {expected}"))?;
    Ok(rows)
}

/// Run the scaling sweeps and return them as ordered `(key, rows)` pairs
/// (the caller emits them in this order, which the schema pins).
pub(crate) fn run_scaling(
    out: &mut Output<'_>,
    runs: usize,
    quick: bool,
) -> io::Result<Vec<(&'static str, Value)>> {
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
    out.line("\nTrace size scaling (CAN 2.0B):")?;
    let trace20 = scan_trace_size(
        out,
        &dbc20,
        id20,
        dlc20,
        &f20,
        &[always_between("EngineSpeed", 0, 8000)],
        &sizes,
        runs,
        "CAN 2.0B",
    )?;
    out.line("\nTrace size scaling (CAN-FD):")?;
    let tracefd = scan_trace_size(
        out,
        &dbcfd,
        idfd,
        dlcfd,
        &ffd,
        &[always_between("GPSSpeed", 0, 655)],
        &sizes,
        runs,
        "CAN-FD",
    )?;

    // 3: property-count sweep (10 templates cycled by i mod 10), CAN 2.0B.
    out.line("\nProperty count scaling (CAN 2.0B):")?;
    let counts = [1usize, 2, 3, 5, 7, 10];
    let mut pc_rows = Vec::new();
    let mut pc_baseline: Option<f64> = None;
    for &count in &counts {
        let props = make_properties(count);
        let m = mean_fps(&dbc20, id20, dlc20, &f20, &props, num_frames, runs);
        let base = *pc_baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        out.line(&format!("  {count} props: {m:.0} fps ({relative:.2}x)"))?;
        pc_rows.push(json!({
            "properties": count,
            "fps": round1(m),
            "us_per_frame": round1(us_per_frame),
            "relative": round3(relative),
        }));
    }

    // 4: property-complexity sweep, CAN 2.0B.
    out.line("\nProperty complexity scaling (CAN 2.0B):")?;
    let mut cx_rows = Vec::new();
    let mut cx_baseline: Option<f64> = None;
    for (label, props) in complexity_levels() {
        let m = mean_fps(&dbc20, id20, dlc20, &f20, &props, num_frames, runs);
        let base = *cx_baseline.get_or_insert(m);
        let relative = if base > 0.0 { m / base } else { 0.0 };
        let us_per_frame = if m > 0.0 { 1_000_000.0 / m } else { 0.0 };
        out.line(&format!("  {label}: {m:.0} fps ({relative:.2}x)"))?;
        cx_rows.push(json!({
            "complexity": label,
            "fps": round1(m),
            "us_per_frame": round1(us_per_frame),
            "relative": round3(relative),
        }));
    }

    // 5: DBC-size sweep, after one untimed warm-up load of a 500-message DBC.
    let warm_dbc = sized_dbc(500);
    let _ = load_cost(|client| load_dbc(client, &warm_dbc));
    out.line("\nDBC size scaling:")?;
    let dbc_rows = scan_load(
        out,
        "dbc_size",
        "messages",
        "the allocated bytes double with the messages \
         (the check gates them; the time decides nothing)",
        &dbc_sizes(quick),
        runs,
        |size| {
            let dbc = sized_dbc(size);
            move |client: &Client| load_dbc(client, &dbc)
        },
    )?;

    // 6 & 7: the literal sweeps, through the DBC text route and then through
    // a parseDBC command on the raw command path, each after one untimed
    // warm-up load of a 1000-digit literal on its route, so the route's
    // once-per-process allocation lands in no point.
    let literal_expected = "the allocated bytes double with the digits \
                            (the check gates them; the time decides nothing)";
    let warm_text = literal_dbc_text(1000);
    let _ = load_cost(|client| load_text(client, &warm_text, 1000));
    out.line("\nText literal length scaling:")?;
    let text_literal_rows = scan_load(
        out,
        "text_literal_length",
        "digits",
        literal_expected,
        &literal_lengths(quick),
        runs,
        |digits| {
            let text = literal_dbc_text(digits);
            move |client: &Client| load_text(client, &text, digits)
        },
    )?;
    let warm_command = literal_dbc_command(1000);
    let _ = load_cost(|client| send_command(client, &warm_command, 1000));
    out.line("\nJSON literal length scaling:")?;
    let json_literal_rows = scan_load(
        out,
        "json_literal_length",
        "digits",
        literal_expected,
        &literal_lengths(quick),
        runs,
        |digits| {
            let command = literal_dbc_command(digits);
            move |client: &Client| send_command(client, &command, digits)
        },
    )?;

    Ok(vec![
        ("trace_size_can20", Value::Array(trace20)),
        ("trace_size_canfd", Value::Array(tracefd)),
        ("property_count", Value::Array(pc_rows)),
        ("property_complexity", Value::Array(cx_rows)),
        ("dbc_size", Value::Array(dbc_rows)),
        ("text_literal_length", Value::Array(text_literal_rows)),
        ("json_literal_length", Value::Array(json_literal_rows)),
    ])
}

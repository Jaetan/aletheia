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
//! `scaling` (`--runs N --quick`; sweeps of trace size CAN 2.0B / CAN-FD,
//! property count, property complexity and DBC size, emitted as a dict-shaped
//! `results` payload). `--json` sends the human-readable progress to stderr and prints
//! the JSON report to stdout. `--quick` shrinks the default sizes for a fast
//! smoke run (and selects the reduced scaling magnitudes the schema pins).

mod fixtures;
mod latency;
mod scaling;
mod stats;
mod throughput;

use std::io::{self, Write};
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::{json, Value};

use latency::run_latency;
use scaling::run_scaling;
use throughput::run_throughput;

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

/// Where a run writes. Without `--json` its text is the report, on `stdout`;
/// under `--json` the text is progress on `stderr`, and the report is the JSON
/// written to `stdout` once the lanes are done. A write to `stdout` that fails
/// returns its error, which fails the run; progress `stderr` cannot take is
/// lost, and the run goes on.
pub(crate) struct Output<'a> {
    stdout: &'a mut dyn Write,
    stderr: &'a mut dyn Write,
    json: bool,
}

impl Output<'_> {
    /// One line of the run's text.
    pub(crate) fn line(&mut self, line: &str) -> io::Result<()> {
        if self.json {
            let _ = writeln!(self.stderr, "{line}");
            Ok(())
        } else {
            self.write(line)
        }
    }

    /// The JSON report, under `--json`.
    fn json_report(&mut self, report: &str) -> io::Result<()> {
        self.write(report)
    }

    /// Write `text` as a line and flush it, so a writer that holds what it is
    /// given fails here rather than when dropped, where its error is lost.
    fn write(&mut self, text: &str) -> io::Result<()> {
        writeln!(self.stdout, "{text}")?;
        self.stdout.flush()
    }
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

/// The benchmark a run measures, named by its first argument.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Throughput,
    Latency,
    Scaling,
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Throughput => "throughput",
            Mode::Latency => "latency",
            Mode::Scaling => "scaling",
        }
    }
}

impl std::str::FromStr for Mode {
    type Err = String;

    fn from_str(name: &str) -> Result<Self, String> {
        match name {
            "throughput" => Ok(Mode::Throughput),
            "latency" => Ok(Mode::Latency),
            "scaling" => Ok(Mode::Scaling),
            other => Err(format!(
                "Unknown mode: {other} (use throughput, latency, or scaling)"
            )),
        }
    }
}

struct Args {
    mode: Mode,
    frames: u64,
    runs: usize,
    warmup: usize,
    ops: usize,
    json: bool,
    quick: bool,
}

fn parse_num<T: std::str::FromStr>(argv: &[String], i: usize, flag: &str) -> Result<T, String> {
    argv.get(i)
        .and_then(|s| s.parse().ok())
        .ok_or_else(|| format!("{flag} requires a numeric argument"))
}

/// The run `argv` asks for, or the line it is refused with. Every refusal
/// comes before the run writes anything.
fn parse_args(argv: &[String]) -> Result<Args, String> {
    // First positional argument (not a flag) selects the mode.
    let mut i = 0;
    let mut mode = Mode::Throughput;
    if let Some(first) = argv.first() {
        if !first.starts_with('-') {
            mode = first.parse()?;
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
                frames = Some(parse_num(argv, i, "--frames")?);
            }
            "--runs" => {
                i += 1;
                runs = Some(parse_num(argv, i, "--runs")?);
            }
            "--warmup" => {
                i += 1;
                warmup = Some(parse_num(argv, i, "--warmup")?);
            }
            "--ops" => {
                i += 1;
                ops = Some(parse_num(argv, i, "--ops")?);
            }
            other => return Err(format!("Unknown option: {other}")),
        }
        i += 1;
    }

    // `--quick` lowers the default sizes for a fast smoke run; explicit flags
    // still take precedence. In `scaling` mode it selects the reduced sweep
    // magnitudes the cross-binding schema pins (matching Go / Python). For
    // throughput / latency it is a convenience — `run_all.sh` drives those with
    // explicit sizes, never `--quick`.
    let (def_frames, def_runs, def_ops) = if quick {
        (1000u64, 2usize, 1000usize)
    } else {
        (10_000u64, 5usize, 5000usize)
    };
    // A mode run without `--warmup` warms as the other bindings' harnesses do:
    // two untimed passes before a throughput lane, five hundred untimed
    // operations before a latency lane.
    let def_warmup = if mode == Mode::Latency { 500 } else { 2 };

    Ok(Args {
        mode,
        frames: frames.unwrap_or(def_frames),
        runs: runs.unwrap_or(def_runs),
        warmup: warmup.unwrap_or(def_warmup),
        ops: ops.unwrap_or(def_ops),
        json,
        quick,
    })
}

/// The JSON report of a list-container mode (throughput / latency).
/// `parameters` holds the flags the mode read, `--json` aside, under the
/// flag's name (`parameters` in `benchmarks/SCHEMA.yaml`).
fn list_report(mode: &str, parameters: Value, results: Vec<Value>) -> String {
    let output = json!({
        "benchmark": mode,
        "language": "rust",
        "timestamp": iso_timestamp(),
        "system": system_json(),
        "parameters": parameters,
        "results": results,
    });
    serde_json::to_string_pretty(&output).expect("serialize benchmark JSON")
}

/// The scaling report: a dict-container mode whose `results` object keys
/// MUST appear in schema order. `serde_json::Value` objects (a `BTreeMap`
/// without the `preserve_order` feature) would sort the keys, so the results
/// object is assembled by hand to pin the sub-benchmark order the gate checks.
fn scaling_report(mode: &str, parameters: &Value, sweeps: &[(&str, Value)]) -> String {
    let inner: Vec<String> = sweeps
        .iter()
        .map(|(key, rows)| {
            let rows_json =
                serde_json::to_string_pretty(rows).expect("serialize scaling sweep rows");
            // Indent the multi-line array body under the results object.
            let indented = rows_json.replace('\n', "\n    ");
            format!("    {}: {indented}", Value::String((*key).to_string()))
        })
        .collect();
    let results_body = inner.join(",\n");
    let system = serde_json::to_string_pretty(&system_json()).expect("serialize system info");
    let system_indented = system.replace('\n', "\n  ");
    let parameters =
        serde_json::to_string_pretty(parameters).expect("serialize scaling parameters");
    let parameters_indented = parameters.replace('\n', "\n  ");
    format!(
        "{{\n  {}: {},\n  {}: {},\n  {}: {},\n  {}: {},\n  {}: {},\n  {}: {{\n{results_body}\n  }}\n}}",
        Value::String("benchmark".to_string()),
        Value::String(mode.to_string()),
        Value::String("language".to_string()),
        Value::String("rust".to_string()),
        Value::String("timestamp".to_string()),
        Value::String(iso_timestamp()),
        Value::String("system".to_string()),
        system_indented,
        Value::String("parameters".to_string()),
        parameters_indented,
        Value::String("results".to_string()),
    )
}

/// Measure the mode `args` selects and write what it reports to `out`. The
/// first lane loads the kernel, after the banner.
fn measure(args: &Args, lib: &str, out: &mut Output<'_>) -> io::Result<()> {
    let mode = args.mode.name();
    out.line(&format!("Aletheia Rust Benchmark ({mode})"))?;
    out.line(&format!("Library: {lib}"))?;

    match args.mode {
        Mode::Throughput => {
            out.line(&format!("Frames per run: {}", args.frames))?;
            out.line(&format!("Runs: {}", args.runs))?;
            let results = run_throughput(out, args.frames, args.runs, args.warmup)?;
            if args.json {
                let parameters =
                    json!({"frames": args.frames, "runs": args.runs, "warmup": args.warmup});
                out.json_report(&list_report(mode, parameters, results))?;
            }
        }
        Mode::Latency => {
            out.line(&format!("Operations: {}", args.ops))?;
            let results = run_latency(out, args.ops, args.warmup)?;
            if args.json {
                let parameters = json!({"ops": args.ops, "warmup": args.warmup});
                out.json_report(&list_report(mode, parameters, results))?;
            }
        }
        Mode::Scaling => {
            out.line(&format!("Runs: {}", args.runs))?;
            out.line(&format!("Quick: {}", args.quick))?;
            let sweeps = run_scaling(out, args.runs, args.quick)?;
            if args.json {
                let parameters = json!({"runs": args.runs, "quick": args.quick});
                out.json_report(&scaling_report(mode, &parameters, &sweeps))?;
            }
        }
    }
    Ok(())
}

/// Run the benchmark `argv` asks for, writing to `stdout` and `stderr`. The
/// error is the line the program exits 1 on: an argument refused, or a report
/// write that failed, naming the mode's report.
fn run(
    argv: &[String],
    lib: &str,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> Result<(), String> {
    let args = parse_args(argv)?;
    let mut out = Output {
        stdout,
        stderr,
        json: args.json,
    };
    measure(&args, lib, &mut out)
        .map_err(|err| format!("writing the {} report failed: {err}", args.mode.name()))
}

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let lib = std::env::var("ALETHEIA_LIB").unwrap_or_else(|_| "libaletheia-ffi.so".to_string());
    let mut stderr = io::stderr().lock();
    let outcome = run(&argv, &lib, &mut io::stdout().lock(), &mut stderr);
    if let Err(message) = outcome {
        // A line stderr cannot take is lost; the exit status still tells.
        let _ = writeln!(stderr, "{message}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests;

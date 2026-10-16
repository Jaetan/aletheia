// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The benchmark example's exit status, which `benchmarks/run_all.sh` reads to
//! tell a run from a failure and which only a process of its own has. The
//! example's own tests build it as a test harness in place of the program, so
//! a cargo of this test's own builds the program, into a target directory
//! under the target's temporary directory, and neither the build nor the
//! program carries the instrumentation a coverage run sets. Each stream of the
//! program is a file it writes itself, or `/dev/full`, which takes no write.
//!
//! A refused argument exits 1 before the kernel loads, the library pointed at
//! nothing so a refusal moved after the load names the load instead. Against
//! the kernel `ALETHEIA_LIB` names, a report that cannot be written exits 1
//! naming it, and progress that cannot be written is dropped, the run writing
//! its report and exiting 0.

mod instrumentation;

use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The device that refuses every write, with no space left on it.
const FULL: &str = "/dev/full";

/// The smallest throughput run: it loads the kernel and writes a report.
const THROUGHPUT: [&str; 7] = [
    "throughput",
    "--frames",
    "1",
    "--runs",
    "1",
    "--warmup",
    "0",
];

/// The refusal of a mode the program does not run.
const UNKNOWN_MODE: &str = "Unknown mode: bogus (use throughput, latency, or scaling)\n";

/// The directory this test builds and runs the program in.
fn work() -> PathBuf {
    Path::new(env!("CARGO_TARGET_TMPDIR")).join("benchmark_program")
}

/// A command for `program` with none of the instrumentation a coverage run sets.
fn uninstrumented(program: impl AsRef<OsStr>) -> Command {
    let mut command = Command::new(program);
    for key in instrumentation::variables() {
        command.env_remove(key);
    }
    command
}

/// The benchmark program, built by a cargo of this test's own.
fn program() -> PathBuf {
    let target = work().join("target");
    let cargo = env::var_os("CARGO").expect("CARGO, which cargo sets for the tests it runs");
    let build = uninstrumented(cargo)
        .args([
            "build",
            "--offline",
            "--example",
            "benchmark",
            "--message-format=short",
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .env("CARGO_TARGET_DIR", &target)
        .output()
        .expect("run cargo build");
    assert!(
        build.status.success(),
        "cargo build --example benchmark failed ({}):\n{}",
        build.status,
        String::from_utf8_lossy(&build.stderr)
    );
    target.join("debug").join("examples").join("benchmark")
}

/// The kernel the suite runs against.
fn kernel() -> OsString {
    env::var_os("ALETHEIA_LIB")
        .expect("ALETHEIA_LIB names the built libaletheia-ffi.so the program runs against")
}

/// A library path that names no file.
fn absent() -> OsString {
    work().join("absent.so").into_os_string()
}

/// The files a test's run writes its streams to, in a directory of the test's own.
fn streams(test: &str) -> (PathBuf, PathBuf) {
    let dir = work().join(test);
    fs::create_dir_all(&dir).expect("create the test's directory");
    (dir.join("stdout"), dir.join("stderr"))
}

/// Run the program with `args` and `ALETHEIA_LIB` at `lib`, writing its stdout
/// and its stderr to the files at those paths, and answer its exit code, none
/// when a signal ended it.
fn run(args: &[&str], lib: &OsStr, stdout: &Path, stderr: &Path) -> Option<i32> {
    let open = |path: &Path| File::create(path).expect("open a stream of the program");
    uninstrumented(program())
        .args(args)
        .env("ALETHEIA_LIB", lib)
        .stdin(Stdio::null())
        .stdout(open(stdout))
        .stderr(open(stderr))
        .status()
        .expect("run the benchmark program")
        .code()
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).expect("read what the program wrote")
}

/// The system's message for a write `/dev/full` refuses, as the program's
/// failure names it.
fn no_space() -> String {
    File::create(FULL)
        .expect("open /dev/full")
        .write_all(b"\n")
        .expect_err("/dev/full refuses every write")
        .to_string()
}

/// `THROUGHPUT` under `--json`.
fn throughput_json() -> Vec<&'static str> {
    [&THROUGHPUT[..], &["--json"]].concat()
}

/// Assert that `stdout` holds a throughput report with results.
fn assert_report(stdout: &Path) {
    let text = read(stdout);
    let report: serde_json::Value = serde_json::from_str(&text)
        .unwrap_or_else(|err| panic!("stdout is not the JSON report ({err}):\n{text}"));
    assert_eq!(report["benchmark"], "throughput", "{text}");
    assert!(
        report["results"].as_array().is_some_and(|r| !r.is_empty()),
        "the report has no results:\n{text}"
    );
}

/// A mode the program does not run exits 1 with its refusal on stderr, and
/// nothing on stdout, the banner included.
#[test]
fn an_unknown_mode_exits_1_before_the_banner() {
    let (stdout, stderr) = streams("unknown_mode");
    for args in [&["bogus"][..], &["bogus", "--json"]] {
        assert_eq!(run(args, &absent(), &stdout, &stderr), Some(1), "{args:?}");
        assert_eq!(read(&stderr), UNKNOWN_MODE, "{args:?}");
        assert_eq!(read(&stdout), "", "{args:?}");
    }
}

/// A refusal stderr cannot take is lost, and the program still exits 1.
#[test]
fn a_refusal_exits_1_when_stderr_takes_no_write() {
    let (stdout, _) = streams("refusal_on_full_stderr");
    assert_eq!(
        run(&["bogus"], &absent(), &stdout, Path::new(FULL)),
        Some(1)
    );
    assert_eq!(read(&stdout), "");
}

/// Without `--json` the text is the report, so a stdout that takes no write
/// fails the run at the banner, before the kernel loads.
#[test]
fn a_text_report_that_cannot_be_written_exits_1() {
    let (_, stderr) = streams("text_report_on_full_stdout");
    assert_eq!(
        run(&THROUGHPUT, &absent(), Path::new(FULL), &stderr),
        Some(1)
    );
    assert_eq!(
        read(&stderr),
        format!("writing the throughput report failed: {}\n", no_space())
    );
}

/// Under `--json` the report is the JSON on stdout: one that cannot be written
/// exits 1 naming it, after the progress the lanes wrote to stderr.
#[test]
fn a_json_report_that_cannot_be_written_exits_1() {
    let (_, stderr) = streams("json_report_on_full_stdout");
    let code = run(&throughput_json(), &kernel(), Path::new(FULL), &stderr);
    let text = read(&stderr);
    assert_eq!(code, Some(1), "stderr:\n{text}");
    assert!(
        text.starts_with("Aletheia Rust Benchmark (throughput)\n"),
        "{text}"
    );
    let failure = format!("\nwriting the throughput report failed: {}\n", no_space());
    assert!(text.ends_with(&failure), "{text}");
}

/// Under `--json` the report goes to stdout and the progress to stderr, and a
/// run that writes both exits 0.
#[test]
fn a_json_report_goes_to_stdout_and_its_progress_to_stderr() {
    let (stdout, stderr) = streams("json_report");
    let code = run(&throughput_json(), &kernel(), &stdout, &stderr);
    let text = read(&stderr);
    assert_eq!(code, Some(0), "stderr:\n{text}");
    assert_report(&stdout);
    assert!(
        text.starts_with("Aletheia Rust Benchmark (throughput)\n"),
        "{text}"
    );
}

/// Progress is not the report: a stderr that takes no write loses it, and the
/// run still writes its report and exits 0.
#[test]
fn progress_that_cannot_be_written_neither_panics_nor_fails_the_run() {
    let (stdout, _) = streams("progress_on_full_stderr");
    let code = run(&throughput_json(), &kernel(), &stdout, Path::new(FULL));
    assert_eq!(code, Some(0));
    assert_report(&stdout);
}

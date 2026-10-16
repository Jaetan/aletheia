// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The harness's refusals, its report writes and its progress, driven
//! in-process. Every run here ends before its first lane loads the kernel.

use std::io::{self, Write};

use super::{parse_args, run, Mode, Output};

const LIB: &str = "libaletheia-ffi.so";

/// The text each mode writes before its first lane loads the kernel, in order,
/// for the arguments that run it.
const TEXT_BEFORE_THE_KERNEL: [(&[&str], &str, &[&str]); 3] = [
    (
        &[
            "throughput",
            "--frames",
            "1",
            "--runs",
            "1",
            "--warmup",
            "0",
        ],
        "throughput",
        &[
            "Aletheia Rust Benchmark (throughput)",
            "Library: libaletheia-ffi.so",
            "Frames per run: 1",
            "Runs: 1",
            "\nCAN 2.0B: Stream LTL (2 props):",
        ],
    ),
    (
        &["latency", "--ops", "1", "--warmup", "0"],
        "latency",
        &[
            "Aletheia Rust Benchmark (latency)",
            "Library: libaletheia-ffi.so",
            "Operations: 1",
            "\nMeasuring CAN 2.0B latency...",
        ],
    ),
    (
        &["scaling", "--runs", "1", "--quick"],
        "scaling",
        &[
            "Aletheia Rust Benchmark (scaling)",
            "Library: libaletheia-ffi.so",
            "Runs: 1",
            "Quick: true",
        ],
    ),
];

/// A report stream that takes writes until one carries `refuse_from`, then
/// refuses that write and every later one, counting what it refuses.
struct Stream {
    refuse_from: Option<&'static str>,
    refusing: bool,
    flush_refused: bool,
    written: Vec<u8>,
    refusals: usize,
}

impl Stream {
    fn new(refuse_from: Option<&'static str>, flush_refused: bool) -> Self {
        Stream {
            refuse_from,
            refusing: false,
            flush_refused,
            written: Vec::new(),
            refusals: 0,
        }
    }

    fn taking_all() -> Self {
        Stream::new(None, false)
    }

    fn refusing_from(text: &'static str) -> Self {
        Stream::new(Some(text), false)
    }

    /// A stream that takes every write and refuses to flush, as a writer that
    /// holds what it is given does when it cannot pass it on.
    fn refusing_flush() -> Self {
        Stream::new(None, true)
    }

    fn text(&self) -> String {
        String::from_utf8(self.written.clone()).expect("the harness writes UTF-8")
    }
}

impl Write for Stream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let text = String::from_utf8_lossy(buf);
        self.refusing = self.refusing || self.refuse_from.is_some_and(|t| text.contains(t));
        if self.refusing {
            self.refusals += 1;
            return Err(io::Error::other("refused"));
        }
        self.written.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.flush_refused {
            self.refusals += 1;
            return Err(io::Error::other("refused"));
        }
        Ok(())
    }
}

fn argv(args: &[&str]) -> Vec<String> {
    args.iter().map(ToString::to_string).collect()
}

/// A mode this program does not run is refused before the banner, so the run
/// writes nothing to either stream.
#[test]
fn an_unknown_mode_is_refused_before_any_text() {
    for args in [&["bogus"][..], &["bogus", "--json"]] {
        let (mut stdout, mut stderr) = (Stream::taking_all(), Stream::taking_all());
        assert_eq!(
            run(&argv(args), LIB, &mut stdout, &mut stderr),
            Err("Unknown mode: bogus (use throughput, latency, or scaling)".to_string()),
            "{args:?}"
        );
        assert_eq!(stdout.text(), "", "{args:?} wrote text before its refusal");
        assert_eq!(stderr.text(), "", "{args:?} wrote progress first");
    }
}

/// Every other refused argument is refused before any text, too.
#[test]
fn a_refused_argument_writes_no_text() {
    for (args, message) in [
        (&["throughput", "--bogus"][..], "Unknown option: --bogus"),
        (&["--json", "latency"], "Unknown option: latency"),
        (&["latency", "--ops"], "--ops requires a numeric argument"),
        (
            &["scaling", "--runs", "many"],
            "--runs requires a numeric argument",
        ),
        (
            &["throughput", "--frames", "-1"],
            "--frames requires a numeric argument",
        ),
        (
            &["latency", "--warmup", "1.5"],
            "--warmup requires a numeric argument",
        ),
    ] {
        let (mut stdout, mut stderr) = (Stream::taking_all(), Stream::taking_all());
        assert_eq!(
            run(&argv(args), LIB, &mut stdout, &mut stderr),
            Err(message.to_string()),
            "{args:?}"
        );
        assert_eq!(stdout.text(), "", "{args:?} wrote text before its refusal");
        assert_eq!(stderr.text(), "", "{args:?} wrote progress first");
    }
}

/// A run without `--warmup` warms as the other bindings' harnesses do, and
/// `--warmup` overrides that.
#[test]
fn the_warmup_defaults_to_the_modes_own() {
    for (args, warmup) in [
        (&[][..], 2),
        (&["throughput"], 2),
        (&["latency"], 500),
        (&["scaling"], 2),
        (&["latency", "--warmup", "7"], 7),
    ] {
        let parsed = parse_args(&argv(args)).expect("the arguments are accepted");
        assert_eq!(parsed.warmup, warmup, "{args:?}");
    }
}

/// A run that names no mode measures throughput.
#[test]
fn a_run_naming_no_mode_measures_throughput() {
    let parsed = parse_args(&argv(&[])).expect("the arguments are accepted");
    assert!(parsed.mode == Mode::Throughput);
}

/// Without `--json` the text is the report: a line that cannot be written ends
/// the run there, with the line the program exits 1 on naming the report, and
/// nothing is written after it.
#[test]
fn a_text_report_line_that_cannot_be_written_fails_the_run() {
    for (args, mode, lines) in TEXT_BEFORE_THE_KERNEL {
        for (at, line) in lines.iter().enumerate() {
            let (mut stream, mut stderr) = (Stream::refusing_from(line), Stream::taking_all());
            assert_eq!(
                run(&argv(args), LIB, &mut stream, &mut stderr),
                Err(format!("writing the {mode} report failed: refused")),
                "{mode}, refused at {line:?}"
            );
            let before: String = lines[..at].iter().map(|l| format!("{l}\n")).collect();
            assert_eq!(stream.text(), before, "{mode}, refused at {line:?}");
            assert_eq!(stream.refusals, 1, "{mode}: a write followed {line:?}");
            assert_eq!(stderr.text(), "", "{mode}: the text report wrote to stderr");
        }
    }
}

/// Under `--json` the report is the JSON on stdout: a write of it that fails
/// returns its error, and one that succeeds writes the report followed by a
/// newline.
#[test]
fn the_json_report_reaches_stdout_or_returns_its_error() {
    let mut refusing = Stream::refusing_from("{");
    let written = Output {
        stdout: &mut refusing,
        stderr: &mut Stream::taking_all(),
        json: true,
    }
    .json_report("{}");
    assert_eq!(
        written.map_err(|e| e.to_string()),
        Err("refused".to_string())
    );

    let mut taking = Stream::taking_all();
    let written = Output {
        stdout: &mut taking,
        stderr: &mut Stream::taking_all(),
        json: true,
    }
    .json_report("{}");
    assert!(written.is_ok());
    assert_eq!(taking.text(), "{}\n");
}

/// Under `--json` the text is progress on stderr, never written to stdout.
#[test]
fn progress_under_json_is_written_to_stderr_and_not_to_stdout() {
    let (mut stdout, mut stderr) = (Stream::refusing_from(""), Stream::taking_all());
    let written = Output {
        stdout: &mut stdout,
        stderr: &mut stderr,
        json: true,
    }
    .line("progress");
    assert!(written.is_ok());
    assert_eq!(stdout.refusals, 0);
    assert_eq!(stderr.text(), "progress\n");
}

/// Progress stderr cannot take is lost, and the run goes on: the line returns
/// no error, and stdout is not written in its place.
#[test]
fn refused_progress_is_lost_and_the_run_goes_on() {
    let (mut stdout, mut stderr) = (Stream::taking_all(), Stream::refusing_from(""));
    let written = Output {
        stdout: &mut stdout,
        stderr: &mut stderr,
        json: true,
    }
    .line("progress");
    assert!(written.is_ok());
    assert_eq!(stderr.refusals, 1);
    assert_eq!(stdout.text(), "");
}

/// A write the writer holds and cannot pass on fails at the flush that follows
/// it, for a line of the text report and for the JSON report alike.
#[test]
fn a_report_write_fails_when_its_flush_fails() {
    let mut text = Stream::refusing_flush();
    let written = Output {
        stdout: &mut text,
        stderr: &mut Stream::taking_all(),
        json: false,
    }
    .line("text");
    assert_eq!(
        written.map_err(|e| e.to_string()),
        Err("refused".to_string())
    );

    let mut json = Stream::refusing_flush();
    let written = Output {
        stdout: &mut json,
        stderr: &mut Stream::taking_all(),
        json: true,
    }
    .json_report("{}");
    assert_eq!(
        written.map_err(|e| e.to_string()),
        Err("refused".to_string())
    );
}

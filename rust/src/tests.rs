// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

use std::cell::Cell;
use std::rc::Rc;

use super::*;

/// Correctness gate for the binary extraction fast path: the packed-binary
/// decode (values keyed by positional signal INDEX via the name cache) must
/// yield the IDENTICAL [`ExtractionResult`] as the trusted JSON path. This is
/// what proves the name-cache order aligns with the kernel's index assignment
/// — a misalignment would pair the right values with the wrong names on the
/// binary path only, so the two paths would disagree. The 3-signal message
/// makes any index off-by-one observable.
///
/// Needs the real `.so` (run_ci sets `ALETHEIA_LIB`); skips observably when it
/// cannot load — the pure `decode_extraction_bin` tests plus the `frame_ops`
/// integration tests give the offset-arithmetic + binary-path coverage that
/// does not depend on this test running.
#[test]
fn extract_binary_path_matches_json_path() {
    const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");
    let Ok(c) = Client::new() else {
        eprintln!(
            "SKIP extract_binary_path_matches_json_path: libaletheia-ffi.so \
                 not loadable (set ALETHEIA_LIB)"
        );
        return;
    };
    let id = CanId::standard(256).expect("valid id");
    let dlc = Dlc::new(8).expect("valid dlc");

    // Run one frame through both paths on the same client: the cache is
    // (re)populated → binary path, then cleared → JSON path.
    let both = |frame: &[u8]| -> (ExtractionResult, ExtractionResult) {
        c.parse_dbc_text(MINIMAL).expect("parse DBC"); // (re)populate the name cache
        let via_binary = c.extract_signals(id, dlc, frame).expect("binary extract");
        c.signal_names.borrow_mut().clear(); // force the JSON path
        let via_json = c.extract_signals(id, dlc, frame).expect("json extract");
        (via_binary, via_json)
    };

    // All-zero frame: 3 in-range values, no errors/absent. With no errors the
    // paths agree EXACTLY — the values-section index→name alignment gate (a
    // mis-ordered name cache would pair the wrong name with a value on the
    // binary path only).
    let (bin, json) = both(&[0u8; 8]);
    assert!(!bin.values.is_empty(), "expected the 3 EngineStatus values");
    assert_eq!(
        bin, json,
        "binary and JSON must agree exactly when there are no errors"
    );

    // EngineSpeed raw 0xFFFF (16-bit little-endian) → 16383.75 rpm, past the
    // signal's [0, 8000] range → the kernel emits an `errors` entry. The
    // binary wire carries the kernel-minted reason string (byte-identical to
    // the JSON path's), so the two paths agree EXACTLY on the error frame
    // too — including error signal names AND reasons.
    let (bin, json) = both(&[0xFF, 0xFF, 0, 0, 0, 0, 0, 0]);
    assert!(
        !bin.errors.is_empty(),
        "expected an out-of-bounds error for EngineSpeed"
    );
    assert_eq!(
        bin, json,
        "binary and JSON must agree exactly, error reasons included"
    );
    assert!(
        bin.errors[0].reason.contains("16383.75"),
        "the reason must be the kernel's detailed string naming the \
             offending value, got: {:?}",
        bin.errors[0].reason
    );
}

/// A diagnostic that references no signals is unreachable through the
/// formula DSL (every predicate names a signal), so this drives the private
/// state directly: when no todo diagnostic wants any signal, end-of-stream
/// enrichment must skip the frame snapshot + extraction loop entirely (zero
/// backend calls, hence no extraction refusal to return) while still
/// attaching the no-values enrichment to every todo result.
#[test]
fn enrich_eos_skips_extraction_when_no_diag_wants_signals() {
    let m = MockBackend::new();
    let c = Client::with_backend(Box::new(m.clone()));
    *c.diags.borrow_mut() = vec![PropertyDiagnostic {
        signals: Vec::new(),
        formula_desc: "always(TRUE)".to_string(),
    }];
    // A cached frame is available — proving the skip comes from the empty
    // union, not from an empty frame store. No extraction response is
    // queued, so any extraction attempt would fail the mock loudly.
    c.last_frames.borrow_mut().insert(
        CanId::standard(256).expect("valid id"),
        (Dlc::new(8).expect("valid dlc"), vec![0u8; 8]),
    );
    let mut results = vec![PropertyResult {
        property_index: 0,
        verdict: Verdict::Fails,
        reason: "x".to_string(),
        timestamp: None,
        enrichment: None,
    }];

    c.enrich_eos(&mut results)
        .expect("a skipped extraction refuses nothing");

    assert!(
        !m.captured()
            .iter()
            .any(|s| s == "<binary:extractAllSignals>"),
        "an empty wanted-signal union must skip extraction entirely"
    );
    let e = results[0]
        .enrichment
        .as_ref()
        .expect("enrichment still attaches when the frame loop is skipped");
    assert!(e.signals.is_empty(), "no values were extracted");
    assert_eq!(
        e.enriched_reason, "violated: always(TRUE) [core: x]",
        "the no-values fallback reason must be used"
    );
}

/// A backend that hands every call to the FFI backend and counts the
/// extractions by path: `binary` the packed buffer, which the client reads
/// with its cached signal names, `json` the kernel's JSON reply, which it
/// reads without them.
struct PathCounting {
    inner: FfiBackend,
    binary: Rc<Cell<usize>>,
    json: Rc<Cell<usize>>,
}

impl Backend for PathCounting {
    fn process(&self, input: &str) -> Result<String, Error> {
        self.inner.process(input)
    }
    fn send_frame_binary(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<String, Error> {
        self.inner.send_frame_binary(ts, id, dlc, data, brs, esi)
    }
    fn send_error_binary(&self, ts: Timestamp) -> Result<String, Error> {
        self.inner.send_error_binary(ts)
    }
    fn send_remote_binary(&self, ts: Timestamp, id: CanId) -> Result<String, Error> {
        self.inner.send_remote_binary(ts, id)
    }
    fn start_stream_binary(&self) -> Result<String, Error> {
        self.inner.start_stream_binary()
    }
    fn end_stream_binary(&self) -> Result<String, Error> {
        self.inner.end_stream_binary()
    }
    fn format_dbc_binary(&self) -> Result<String, Error> {
        self.inner.format_dbc_binary()
    }
    fn extract_signals_binary(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<String, Error> {
        self.json.set(self.json.get() + 1);
        self.inner.extract_signals_binary(id, dlc, data)
    }
    fn extract_signals_bin(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<Vec<u8>, Error> {
        self.binary.set(self.binary.get() + 1);
        self.inner.extract_signals_bin(id, dlc, data)
    }
    fn build_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        self.inner.build_frame_bin(id, extended, dlc, signals)
    }
    fn update_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        frame: &[u8],
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        self.inner
            .update_frame_bin(id, extended, dlc, frame, signals)
    }
}

/// Each typed method keeps the signal-name cache, since each knows what its
/// command changes in the core: an extraction after `set_properties`,
/// `validate_dbc` or `format_dbc_text` takes the binary path, as one right
/// after the typed load does. A raw `process` empties the cache, so the
/// extraction after it takes the JSON path. A typed `parse_dbc` refills the
/// cache before each method, so each path is that one method's.
#[test]
fn every_typed_method_keeps_the_signal_name_cache_and_process_empties_it() {
    const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");
    let binary = Rc::new(Cell::new(0));
    let json = Rc::new(Cell::new(0));
    let c = Client::with_backend(Box::new(PathCounting {
        inner: FfiBackend::new(None, None, LogLevel::Warn)
            .expect("load libaletheia-ffi.so for test (is ALETHEIA_LIB set?)"),
        binary: Rc::clone(&binary),
        json: Rc::clone(&json),
    }));
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC").dbc;
    let id = CanId::standard(256).expect("valid id");
    let dlc = Dlc::new(8).expect("valid dlc");
    let property = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "EngineSpeed".to_owned(),
        value: Rational::integer(1000),
    })));
    let raw = wire_json::command("validateDBC", "dbc", &Wire(&dbc)).expect("a raw command");

    // The path the next extraction takes, read from the counts it moves.
    let next_path = || {
        let before = (binary.get(), json.get());
        c.extract_signals(id, dlc, &[0u8; 8]).expect("extract");
        match (binary.get() - before.0, json.get() - before.1) {
            (1, 0) => "binary",
            (0, 1) => "json",
            moved => panic!("one extraction moved the counts by {moved:?}"),
        }
    };
    let steps: [(&str, &dyn Fn()); 5] = [
        ("parse_dbc", &|| {}),
        ("set_properties", &|| {
            c.set_properties(std::slice::from_ref(&property))
                .expect("set properties");
        }),
        ("validate_dbc", &|| {
            c.validate_dbc(&dbc).expect("validate DBC");
        }),
        ("format_dbc_text", &|| {
            c.format_dbc_text(&dbc).expect("format DBC text");
        }),
        ("process", &|| {
            c.process(&raw).expect("raw command");
        }),
    ];
    let paths: Vec<(&str, &str)> = steps
        .iter()
        .map(|(method, step)| {
            c.parse_dbc(&dbc).expect("the typed load refills the cache");
            step();
            (*method, next_path())
        })
        .collect();
    assert_eq!(
        paths,
        [
            ("parse_dbc", "binary"),
            ("set_properties", "binary"),
            ("validate_dbc", "binary"),
            ("format_dbc_text", "binary"),
            ("process", "json"),
        ]
    );
}

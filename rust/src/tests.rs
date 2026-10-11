// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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
/// backend calls, hence no `enrichment.extraction_failed` warns) while
/// still attaching the no-values enrichment to every todo result.
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

    c.enrich_eos(&mut results);

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

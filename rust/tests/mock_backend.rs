// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The [`Backend`] dependency-injection seam and the [`MockBackend`] test double.
//! The seam exercises the [`Client`] against a recorded/replayed mock
//! command backend. Most tests need no `libaletheia-ffi.so`; the ones that build
//! checks do, because the kernel checks a check as it is built and
//! `set_properties` renders each predicate threshold, both through process-global
//! MAlonzo exports that always load the real `.so` and are vocal while the RTS is
//! down: they call [`rts_up`] to bring the RTS up. The mock only ever replaces the
//! command backend, never the property check or the renderer.

use std::sync::{Arc, Mutex};

use aletheia::log::events;
use aletheia::{
    check, Backend, CanId, Client, Dlc, Error, FrameResponse, LogField, LogRecord, LogValue,
    MockBackend, Rational, SignalInjection, Timestamp, Verdict,
};

/// Bring the GHC RTS up via a throwaway real backend, so the check builders and
/// the rational renderer work while the rest of the flow runs over the mock. Both
/// are process-global MAlonzo exports that always load the real `.so`; the RTS is
/// one-shot, so the throwaway client can drop immediately (the init stays latched).
/// Mirrors the C++ `rts_setup_listener` / Python `rts_up` fixture.
fn rts_up() {
    drop(Client::new().expect("init GHC RTS (set ALETHEIA_LIB to a built libaletheia-ffi.so)"));
}

/// The kernel's answer to `set_properties` and `start_stream`.
const SUCCESS: &str = r#"{"status":"success"}"#;
/// The kernel's answer to a frame that decided nothing.
const ACK: &str = r#"{"status":"ack"}"#;

/// The check most tests install, once the runtime is up.
fn speed_at_most_1000() -> aletheia::Check {
    check::signal("EngineSpeed")
        .never_exceeds(1000)
        .expect("check")
}

/// A frame's answer failing property `property_index` at timestamp 0 with
/// `reason`.
fn violation_at(property_index: u32, reason: &str) -> String {
    format!(
        r#"{{"type":"property_batch","results":[{{"type":"property","status":"fails","property_index":{property_index},"timestamp":0,"reason":"{reason}"}}]}}"#
    )
}

/// The end of a stream failing each property of `indices` at timestamp 5.
fn end_stream_failing(indices: &[u32]) -> String {
    let results: Vec<String> = indices
        .iter()
        .map(|i| format!(r#"{{"status":"fails","property_index":{i},"timestamp":5,"reason":"x"}}"#))
        .collect();
    format!(
        r#"{{"status":"complete","results":[{}],"warnings":[]}}"#,
        results.join(",")
    )
}

/// An extraction's JSON answer carrying each `(name, value)` of `values`.
fn extraction_of(values: &[(&str, i64)]) -> String {
    let values: Vec<String> = values
        .iter()
        .map(|(name, value)| format!(r#"{{"name":"{name}","value":{value}}}"#))
        .collect();
    format!(
        r#"{{"status":"success","values":[{}],"errors":[],"absent":[]}}"#,
        values.join(",")
    )
}

/// The mock records the exact `<binary:OP>` sentinel for every binary-path op —
/// never a fabricated JSON command the real backend would not emit (the
/// cross-binding mock-fidelity convention). Tested at the [`Backend`] level so
/// it is independent of how the [`Client`] decodes responses.
#[test]
fn mock_records_the_canonical_binary_sentinels() {
    let m = MockBackend::new();
    let ts = Timestamp(0);
    let id = CanId::standard(256).expect("id");
    let dlc = Dlc::new(8).expect("dlc");
    let no_signals = SignalInjection { values: &[] };

    // One queued response per call, popped FIFO in call order.
    m.respond_json(r#"{"r":"process"}"#)
        .respond_json(r#"{"r":"frame"}"#)
        .respond_json(r#"{"r":"error"}"#)
        .respond_json(r#"{"r":"remote"}"#)
        .respond_json(r#"{"r":"start"}"#)
        .respond_json(r#"{"r":"end"}"#)
        .respond_json(r#"{"r":"format"}"#)
        .respond_json(r#"{"r":"extract"}"#)
        .respond_bytes(vec![1, 2, 3, 4, 5, 6, 7, 8])
        .respond_bytes(vec![9, 10, 11, 12, 13, 14, 15, 16]);

    assert_eq!(
        m.process("the-command").expect("process"),
        r#"{"r":"process"}"#
    );
    m.send_frame_binary(ts, id, dlc, &[0u8; 8], None, None)
        .expect("send_frame");
    m.send_error_binary(ts).expect("send_error");
    m.send_remote_binary(ts, id).expect("send_remote");
    m.start_stream_binary().expect("start_stream");
    m.end_stream_binary().expect("end_stream");
    m.format_dbc_binary().expect("format_dbc");
    m.extract_signals_binary(id, dlc, &[0u8; 8])
        .expect("extract_signals");
    assert_eq!(
        m.build_frame_bin(256, false, dlc, no_signals)
            .expect("build"),
        vec![1, 2, 3, 4, 5, 6, 7, 8]
    );
    assert_eq!(
        m.update_frame_bin(256, false, dlc, &[0u8; 8], no_signals)
            .expect("update"),
        vec![9, 10, 11, 12, 13, 14, 15, 16]
    );

    assert_eq!(
        m.captured(),
        vec![
            "the-command".to_string(),
            "<binary:sendFrame>".to_string(),
            "<binary:sendError>".to_string(),
            "<binary:sendRemote>".to_string(),
            "<binary:startStream>".to_string(),
            "<binary:endStream>".to_string(),
            "<binary:formatDBC>".to_string(),
            "<binary:extractAllSignals>".to_string(),
            "<binary:buildFrameBin>".to_string(),
            "<binary:updateFrameBin>".to_string(),
        ]
    );
}

/// A [`Client`] built over an injected mock runs a full streaming flow — the mock
/// services the command backend, while the rational renderer (a process-global
/// MAlonzo export) still loads the real `.so`, so [`rts_up`] brings the GHC RTS up.
/// A decided violation fans out to a *second*, hidden backend call
/// (`extract_signals_binary`) for client-side enrichment; the test pins both the
/// fan-out and the enrichment.
#[test]
fn client_over_mock_enriches_via_a_hidden_extract_call() {
    rts_up(); // add_checks → set_properties renders the threshold via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks → set_properties (process)
        .respond_json(SUCCESS) // start_stream
        .respond_json(violation_at(0, "over limit")) // send_frame → a violation
        .respond_json(extraction_of(&[("EngineSpeed", 4000)])); // the hidden extract for enrichment

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    let resp = c
        .send_frame(
            Timestamp(0),
            CanId::standard(256).unwrap(),
            Dlc::new(8).unwrap(),
            &[0u8; 8],
            None,
            None,
        )
        .expect("send_frame");

    let FrameResponse::Verdicts(results) = resp else {
        panic!("expected a property_batch with a violation, got Ack");
    };
    let v = results
        .iter()
        .find(|r| r.verdict == Verdict::Fails)
        .expect("a Fails verdict");
    let e = v
        .enrichment
        .as_ref()
        .expect("the violation must carry client-side enrichment from the extract call");
    assert!(
        e.signals
            .iter()
            .any(|(n, val)| n == "EngineSpeed" && *val == Rational::integer(4000)),
        "enrichment signals: {:?}",
        e.signals
    );

    // The hidden extract call is visible in the capture log: set_properties
    // (a JSON command), then the three binary sentinels in order.
    let cap = m.captured();
    assert!(
        cap[0].contains("setProperties"),
        "first request: {}",
        cap[0]
    );
    assert_eq!(
        &cap[1..],
        [
            "<binary:startStream>",
            "<binary:sendFrame>",
            "<binary:extractAllSignals>",
        ]
    );
}

/// `Clone` shares the queue + capture log (interior mutability), so a test can
/// keep one clone to inspect after injecting another into the [`Client`].
#[test]
fn clone_shares_the_capture_log() {
    let m = MockBackend::new();
    m.respond_json(SUCCESS);
    let c = Client::with_backend(Box::new(m.clone()));
    c.start_stream().expect("start_stream");
    // The original clone observes what the client's clone captured.
    assert_eq!(m.captured(), vec!["<binary:startStream>".to_string()]);
}

/// An exhausted queue is an explicit error — the no-surprise contract shared
/// by all four bindings' mocks (none synthesises a default response).
#[test]
fn exhausted_queue_is_an_error() {
    // Keep a clone to inspect after injection (shared interior-mutable state),
    // so we can assert the starved call was recorded — matching the peer
    // bindings' record-before-error checks (Go `Inputs()`, C++ `last_captured()`).
    let mock = MockBackend::new();
    let probe = mock.clone();
    let c = Client::with_backend(Box::new(mock));
    let err = c.start_stream().expect_err("empty queue must error");
    // Pin the EXACT message, which Display renders unchanged, so the
    // cross-binding unified shape cannot drift. The op token is
    // the `<binary:OP>` sentinel (identical to Python/Go/C++), not a Rust method
    // name; `Error::Protocol` is Rust's wrong-state category (see mock.rs).
    match &err {
        Error::Protocol(msg) => assert_eq!(
            msg.as_str(),
            "mock backend: no queued response for <binary:startStream>"
        ),
        other => panic!("expected Error::Protocol, got {other:?}"),
    }
    // Record-before-error: the starved sentinel is captured on the erroring call.
    assert_eq!(probe.captured(), vec!["<binary:startStream>".to_string()]);
}

/// A queued [`Error`] surfaces unchanged through the [`Client`].
#[test]
fn queued_error_propagates() {
    let m = MockBackend::new();
    m.respond_err(Error::Core {
        code: "no_dbc".to_string(),
        message: "no DBC loaded".to_string(),
    });
    let c = Client::with_backend(Box::new(m));
    let err = c.start_stream().expect_err("queued error must surface");
    assert!(matches!(err, Error::Core { .. }), "got {err:?}");
}

/// `build_with_backend` applies the builder's logger and skips the FFI entirely:
/// `rts_cores` is ignored (no RTS init to fail) and the client works with no
/// `.so` loaded.
#[test]
fn build_with_backend_applies_logger_and_ignores_rts_cores() {
    let captured: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let m = MockBackend::new();
    m.respond_json(SUCCESS);

    let c = Client::builder()
        .rts_cores(4) // ignored on the injection path — no FFI, no RTS
        .logger(move |rec: &LogRecord| sink.lock().expect("lock").push(rec.event.to_string()))
        .build_with_backend(Box::new(m.clone()));
    c.start_stream().expect("start_stream");

    assert_eq!(m.captured(), vec!["<binary:startStream>".to_string()]);
    let names = captured.lock().expect("lock").clone();
    assert!(
        names.iter().any(|e| e == events::STREAM_STARTED),
        "logger should have captured stream.started, got: {names:?}"
    );
}

/// A NUL inside a command reaches the backend whole: no layer ends the command
/// there, the core being the one that refuses it.
#[test]
fn a_nul_inside_a_command_reaches_the_backend_whole() {
    let m = MockBackend::new();
    m.respond_json(r#"{"status":"error"}"#);
    let c = Client::with_backend(Box::new(m.clone()));
    c.process("a\0b").expect("the mock answers");
    assert_eq!(m.captured(), vec!["a\0b".to_string()]);
}

/// The kernel's refusal of the extraction a violation's enrichment needs: an
/// error envelope on the extraction's JSON path.
const NO_DBC: &str = r#"{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}"#;

/// A client over `m` logging each record's event into the returned list.
fn logged_client(m: &MockBackend) -> (Client, Arc<Mutex<Vec<String>>>) {
    let captured: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let c = Client::builder()
        .logger(move |rec: &LogRecord| sink.lock().expect("lock").push(rec.event.to_string()))
        .build_with_backend(Box::new(m.clone()));
    (c, captured)
}

/// `err` is the kernel's `handler_no_dbc` refusal, its message kept, and the
/// extraction that met it was logged as `extraction.parse_failed`, every event
/// logged one the vocabulary names.
fn assert_the_extraction_refusal(err: &Error, captured: &Arc<Mutex<Vec<String>>>) {
    match err {
        Error::Core { code, message } => {
            assert_eq!(code, "handler_no_dbc");
            assert_eq!(message, "no DBC loaded");
        }
        other => panic!("expected the kernel's handler_no_dbc refusal, got {other:?}"),
    }
    let names = captured.lock().expect("lock").clone();
    assert!(
        names.iter().any(|e| e == events::EXTRACTION_PARSE_FAILED),
        "expected extraction.parse_failed, got: {names:?}"
    );
    assert!(
        names.iter().all(|e| events::ALL.contains(&e.as_str())),
        "every event logged is one the vocabulary names, got: {names:?}"
    );
}

/// An extraction the enrichment of a frame's violation needs and the kernel
/// refuses is returned by `send_frame` with the kernel's code and message,
/// rather than the violation going without its enrichment.
#[test]
fn a_refused_extraction_is_returned_by_the_frame_whose_violation_needs_it() {
    rts_up(); // the check's build and set_properties' render need the runtime
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(violation_at(0, "x")) // a violation needing enrichment
        .respond_json(NO_DBC); // the enrichment extract call is refused
    let (c, captured) = logged_client(&m);
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    let err = c
        .send_frame(
            Timestamp(0),
            CanId::standard(256).unwrap(),
            Dlc::new(8).unwrap(),
            &[0u8; 8],
            None,
            None,
        )
        .expect_err("the refused extraction is returned");
    assert_the_extraction_refusal(&err, &captured);
    // The extract WAS attempted (the violation triggered enrichment).
    assert!(m
        .captured()
        .contains(&"<binary:extractAllSignals>".to_string()));
}

/// An extraction the enrichment of a final verdict needs and the kernel
/// refuses is returned by `end_stream` with the kernel's code and message.
#[test]
fn a_refused_extraction_is_returned_by_the_end_of_the_stream() {
    rts_up(); // the check's build and set_properties' render need the runtime
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame (caches last_frames)
        .respond_json(end_stream_failing(&[0])) // end_stream → enrich_eos
        .respond_json(NO_DBC); // the enrichment extract call is refused
    let (c, captured) = logged_client(&m);
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    let err = c
        .end_stream()
        .expect_err("the refused extraction is returned");
    assert_the_extraction_refusal(&err, &captured);
}

/// A backend error from the public `extract_signals` (the FFI/process boundary)
/// is logged as `extraction.process_failed` and surfaced — mirroring Go's
/// `extractSignalsLocked` process-failure path. Because the enrichment loop
/// funnels through this same `extract_signals`, the one emit site covers both.
#[test]
fn extract_signals_process_failure_is_logged() {
    // Capture (event, carries canId=256, carries a non-empty error) so the test
    // pins the structured fields — not just the event name — locking in the
    // cross-binding `canId` + `error` field contract Go/Python/C++ also emit.
    let captured: Arc<Mutex<Vec<(String, bool, bool)>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let m = MockBackend::new();
    m.respond_err(Error::Core {
        code: "boom".to_string(),
        message: "backend unavailable".to_string(),
    });
    let c = Client::builder()
        .logger(move |rec: &LogRecord| {
            let has_can_id = rec
                .fields
                .contains(&LogField::new("canId", LogValue::U64(256)));
            let has_error = rec
                .fields
                .iter()
                .any(|f| f.key == "error" && matches!(f.value, LogValue::Str(s) if !s.is_empty()));
            sink.lock()
                .expect("lock")
                .push((rec.event.to_string(), has_can_id, has_error));
        })
        .build_with_backend(Box::new(m.clone()));
    let err = c
        .extract_signals(
            CanId::standard(256).unwrap(),
            Dlc::new(8).unwrap(),
            &[0u8; 8],
        )
        .expect_err("a backend error must surface");
    assert!(matches!(err, Error::Core { .. }), "got: {err:?}");
    let records = captured.lock().expect("lock").clone();
    let process = records
        .iter()
        .find(|(e, _, _)| e == events::EXTRACTION_PROCESS_FAILED)
        .expect("expected extraction.process_failed");
    assert!(process.1, "extraction.process_failed must carry canId=256");
    assert!(
        process.2,
        "extraction.process_failed must carry a non-empty error"
    );
    assert!(
        !records
            .iter()
            .any(|(e, _, _)| e == events::EXTRACTION_PARSE_FAILED),
        "a process failure must not also emit parse_failed"
    );
}

/// A well-formed backend call whose payload cannot be decoded is logged as
/// `extraction.parse_failed` and surfaced — the parse-boundary peer of
/// `extraction.process_failed`.
#[test]
fn extract_signals_parse_failure_is_logged() {
    // Same field-level assertion as the process-failure peer (see that test).
    let captured: Arc<Mutex<Vec<(String, bool, bool)>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let m = MockBackend::new();
    m.respond_json("not a valid extraction object"); // backend OK, decode fails
    let c = Client::builder()
        .logger(move |rec: &LogRecord| {
            let has_can_id = rec
                .fields
                .contains(&LogField::new("canId", LogValue::U64(256)));
            let has_error = rec
                .fields
                .iter()
                .any(|f| f.key == "error" && matches!(f.value, LogValue::Str(s) if !s.is_empty()));
            sink.lock()
                .expect("lock")
                .push((rec.event.to_string(), has_can_id, has_error));
        })
        .build_with_backend(Box::new(m.clone()));
    let err = c
        .extract_signals(
            CanId::standard(256).unwrap(),
            Dlc::new(8).unwrap(),
            &[0u8; 8],
        )
        .expect_err("an unparseable response must surface");
    assert!(matches!(err, Error::Protocol(_)), "got: {err:?}");
    let records = captured.lock().expect("lock").clone();
    let parse = records
        .iter()
        .find(|(e, _, _)| e == events::EXTRACTION_PARSE_FAILED)
        .expect("expected extraction.parse_failed");
    assert!(parse.1, "extraction.parse_failed must carry canId=256");
    assert!(
        parse.2,
        "extraction.parse_failed must carry a non-empty error"
    );
    assert!(
        !records
            .iter()
            .any(|(e, _, _)| e == events::EXTRACTION_PROCESS_FAILED),
        "a parse failure must not also emit process_failed"
    );
}

/// Exercises the end-of-stream early break: the frame loop stops as soon as
/// every signal wanted by a todo diagnostic has been merged. Two frames are
/// cached, but the first extracted frame (id 256 — lowest first, by the
/// deterministic (canID, extended) sort) already yields the only wanted signal,
/// so the second cached frame is never extracted: exactly one extraction call,
/// and only one extraction response is queued (a second attempt would fail the
/// mock loudly).
#[test]
fn enrich_eos_stops_extracting_once_wanted_signals_merged() {
    rts_up(); // add_checks → set_properties renders the threshold via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame id 256 (caches last_frames)
        .respond_json(ACK) // send_frame id 512 (caches last_frames)
        .respond_json(end_stream_failing(&[0])) // end_stream → enrich_eos
        .respond_json(extraction_of(&[("EngineSpeed", 100)])); // frame 256 satisfies the union

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    c.send_frame(
        Timestamp(1),
        CanId::standard(512).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 512");
    let result = c.end_stream().expect("end_stream");

    let pr = result
        .results
        .iter()
        .find(|r| r.verdict == Verdict::Fails)
        .expect("a Fails verdict");
    let e = pr
        .enrichment
        .as_ref()
        .expect("the EOS violation carries enrichment from the first cached frame");
    assert!(
        e.signals
            .contains(&("EngineSpeed".to_string(), Rational::integer(100))),
        "enrichment should carry EngineSpeed from frame 256, got: {:?}",
        e.signals
    );
    let extract_calls = m
        .captured()
        .iter()
        .filter(|s| *s == "<binary:extractAllSignals>")
        .count();
    assert_eq!(
        extract_calls, 1,
        "frame 256 yields every wanted signal, so the loop must stop before frame 512"
    );
}

/// Exercises the end-of-stream multi-frame merge loop — the counterpart of the
/// early-break pin above: while a wanted signal is still missing, the loop
/// keeps extracting. Frame 256 yields only a signal no diagnostic wants, so
/// frame 512 is extracted too and supplies the wanted one. NOTE: the mock
/// returns extraction responses positionally, so it cannot observe the
/// `HashMap` iteration order that the (canID, extended) sort makes
/// deterministic; that ordering (lowest-CAN-id wins for a same-name contention)
/// is a total-order-by-construction guarantee, exercised live by the
/// real-`.so` `enrichment.rs` tests.
#[test]
fn enrich_eos_merges_across_frames_until_wanted_signals_found() {
    rts_up(); // add_checks → set_properties renders the threshold via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame id 256 (caches last_frames)
        .respond_json(ACK) // send_frame id 512 (caches last_frames)
        .respond_json(end_stream_failing(&[0])) // end_stream → enrich_eos
        .respond_json(extraction_of(&[("CoolantTemp", 90)])) // frame 256: nothing wanted → keep going
        .respond_json(extraction_of(&[("EngineSpeed", 200)])); // frame 512: the wanted signal

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    c.send_frame(
        Timestamp(1),
        CanId::standard(512).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 512");
    let result = c.end_stream().expect("end_stream");

    let pr = result
        .results
        .iter()
        .find(|r| r.verdict == Verdict::Fails)
        .expect("a Fails verdict");
    let e = pr
        .enrichment
        .as_ref()
        .expect("the EOS violation carries enrichment merged from the second frame");
    assert!(
        e.signals
            .contains(&("EngineSpeed".to_string(), Rational::integer(200))),
        "enrichment should carry EngineSpeed from frame 512, got: {:?}",
        e.signals
    );
    let extract_calls = m
        .captured()
        .iter()
        .filter(|s| *s == "<binary:extractAllSignals>")
        .count();
    assert_eq!(
        extract_calls, 2,
        "a still-missing wanted signal must keep the frame loop extracting"
    );
}

/// The multi-property-single-extract scenario: two failing properties (two
/// diagnostics — one wanting EngineSpeed, one CoolantTemp) over the same two
/// cached frames. The extract-once shape runs ONE extraction pass over the
/// frames — exactly one call per frame extracted, never one per property —
/// then distributes the merged map filtered per diagnostic, so each result's
/// enrichment carries only its own diagnostic's signals. Only two extraction
/// responses are queued: a per-property re-walk of the frames would exhaust
/// the queue and fail the mock loudly.
#[test]
fn enrich_eos_two_properties_share_one_extraction_pass() {
    rts_up(); // add_checks → set_properties renders the thresholds via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame id 256 (caches last_frames)
        .respond_json(ACK) // send_frame id 512 (caches last_frames)
        .respond_json(end_stream_failing(&[0, 1])) // end_stream → enrich_eos, two todo diagnostics
        .respond_json(extraction_of(&[("EngineSpeed", 100)])) // frame 256: property 0's signal
        .respond_json(extraction_of(&[("CoolantTemp", 90)])); // frame 512: property 1's signal

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[
        speed_at_most_1000(),
        check::signal("CoolantTemp")
            .never_exceeds(120)
            .expect("check"),
    ])
    .expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    c.send_frame(
        Timestamp(1),
        CanId::standard(512).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 512");
    let result = c.end_stream().expect("end_stream");

    let extract_calls = m
        .captured()
        .iter()
        .filter(|s| *s == "<binary:extractAllSignals>")
        .count();
    assert_eq!(
        extract_calls, 2,
        "one extraction call per cached frame — the pass is shared across properties, not repeated per property"
    );
    let p0 = result
        .results
        .iter()
        .find(|r| r.property_index == 0)
        .expect("property 0's result");
    let e0 = p0
        .enrichment
        .as_ref()
        .expect("property 0 carries enrichment");
    assert_eq!(
        e0.signals,
        vec![("EngineSpeed".to_string(), Rational::integer(100))],
        "property 0's enrichment must carry only its own diagnostic's signal"
    );
    let p1 = result
        .results
        .iter()
        .find(|r| r.property_index == 1)
        .expect("property 1's result");
    let e1 = p1
        .enrichment
        .as_ref()
        .expect("property 1 carries enrichment");
    assert_eq!(
        e1.signals,
        vec![("CoolantTemp".to_string(), Rational::integer(90))],
        "property 1's enrichment must carry only its own diagnostic's signal"
    );
}

/// The first-frame-wins discriminator: EngineSpeed is extractable from BOTH
/// cached frames with different values (frame 256 → 1, frame 512 → 2), and
/// the wanted union {EngineSpeed, CoolantTemp} is only completed by frame
/// 512's CoolantTemp, so the early break demonstrably does NOT fire after
/// frame 256 — the loop reaches frame 512 (two extraction calls). The
/// first-seen merge must keep frame 256's EngineSpeed = 1; an
/// overwrite/last-wins merge would surface 2. (The disjoint-signal merge
/// test above cannot tell those apart; this one pins first-wins.)
#[test]
fn enrich_eos_first_frame_wins_for_a_contended_signal() {
    rts_up(); // add_checks → set_properties renders the thresholds via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame id 256 (caches last_frames)
        .respond_json(ACK) // send_frame id 512 (caches last_frames)
        .respond_json(end_stream_failing(&[0, 1])) // end_stream → enrich_eos
        .respond_json(extraction_of(&[("EngineSpeed", 1)])) // frame 256: EngineSpeed's first (winning) value
        .respond_json(extraction_of(&[("EngineSpeed", 2), ("CoolantTemp", 3)])); // frame 512: a contending EngineSpeed + the still-missing CoolantTemp

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[
        speed_at_most_1000(),
        check::signal("CoolantTemp")
            .never_exceeds(120)
            .expect("check"),
    ])
    .expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    c.send_frame(
        Timestamp(1),
        CanId::standard(512).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 512");
    let result = c.end_stream().expect("end_stream");

    let extract_calls = m
        .captured()
        .iter()
        .filter(|s| *s == "<binary:extractAllSignals>")
        .count();
    assert_eq!(
        extract_calls, 2,
        "CoolantTemp is still missing after frame 256, so frame 512 must be extracted too"
    );
    let e0 = result
        .results
        .iter()
        .find(|r| r.property_index == 0)
        .expect("property 0's result")
        .enrichment
        .as_ref()
        .expect("property 0 carries enrichment");
    assert_eq!(
        e0.signals,
        vec![("EngineSpeed".to_string(), Rational::integer(1))],
        "first frame wins: frame 256's EngineSpeed = 1 must survive frame 512's contending value 2"
    );
    let e1 = result
        .results
        .iter()
        .find(|r| r.property_index == 1)
        .expect("property 1's result")
        .enrichment
        .as_ref()
        .expect("property 1 carries enrichment");
    assert_eq!(
        e1.signals,
        vec![("CoolantTemp".to_string(), Rational::integer(3))],
        "CoolantTemp arrives from frame 512"
    );
}

/// End-of-stream with no verdict needing enrichment (`Holds` only): the frame
/// snapshot + extraction loop must not run at all — zero extraction calls, even
/// though a frame is cached (no extraction response is queued, so an attempt
/// would fail the mock loudly).
#[test]
fn enrich_eos_no_todo_makes_no_extract_calls() {
    rts_up(); // add_checks → set_properties renders the threshold via the kernel
    let m = MockBackend::new();
    m.respond_json(SUCCESS) // add_checks
        .respond_json(SUCCESS) // start_stream
        .respond_json(ACK) // send_frame (caches last_frames)
        .respond_json(
            r#"{"status":"complete","results":[{"status":"holds","property_index":0}],"warnings":[]}"#,
        ); // end_stream → nothing to enrich

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[speed_at_most_1000()]).expect("add_checks");
    c.start_stream().expect("start_stream");
    c.send_frame(
        Timestamp(0),
        CanId::standard(256).unwrap(),
        Dlc::new(8).unwrap(),
        &[0u8; 8],
        None,
        None,
    )
    .expect("send 256");
    let result = c.end_stream().expect("end_stream");

    assert!(
        result.results[0].enrichment.is_none(),
        "a Holds verdict must not be enriched"
    );
    assert!(
        !m.captured()
            .contains(&"<binary:extractAllSignals>".to_string()),
        "no todo verdict → no extraction call"
    );
}

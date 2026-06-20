// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The [`Backend`] dependency-injection seam and the [`MockBackend`] test double
//! (Slice R5). Unlike every other Rust test file, these run **without**
//! `libaletheia-ffi.so`: the whole point of the seam is to exercise the
//! [`Client`] against a recorded/replayed mock. No `ALETHEIA_LIB` is needed.

use std::sync::{Arc, Mutex};

use aletheia::log::events;
use aletheia::{
    check, Backend, CanId, Client, Dlc, Error, FrameResponse, LogRecord, MockBackend, Rational,
    SignalInjection, Timestamp, Verdict,
};

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
    let no_signals = SignalInjection {
        indices: &[],
        nums: &[],
        dens: &[],
    };

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

/// A [`Client`] built over an injected mock runs a full streaming flow with no
/// `.so` loaded — and a decided violation fans out to a *second*, hidden backend
/// call (`extract_signals_binary`) for client-side enrichment. The mock must
/// service that extra call; the test pins both the fan-out and the enrichment.
#[test]
fn client_over_mock_enriches_via_a_hidden_extract_call() {
    let m = MockBackend::new();
    m.respond_json(r#"{"status":"ack"}"#) // add_checks → set_properties (process)
        .respond_json(r#"{"status":"ack"}"#) // start_stream
        .respond_json(
            r#"{"type":"property_batch","results":[{"status":"fails","property_index":0,"reason":"over limit"}]}"#,
        ) // send_frame → a violation
        .respond_json(r#"{"values":[{"name":"EngineSpeed","value":{"numerator":4000,"denominator":1}}]}"#); // the hidden extract for enrichment

    let c = Client::with_backend(Box::new(m.clone()));
    c.add_checks(&[check::signal("EngineSpeed").never_exceeds(1000)])
        .expect("add_checks");
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
    m.respond_json(r#"{"status":"ack"}"#);
    let c = Client::with_backend(Box::new(m.clone()));
    c.start_stream().expect("start_stream");
    // The original clone observes what the client's clone captured.
    assert_eq!(m.captured(), vec!["<binary:startStream>".to_string()]);
}

/// An exhausted queue is an explicit error (the Rust-idiomatic, no-surprise
/// contract — the peer Python/C++ mocks synthesise a default instead).
#[test]
fn exhausted_queue_is_an_error() {
    let c = Client::with_backend(Box::new(MockBackend::new()));
    let err = c.start_stream().expect_err("empty queue must error");
    assert!(matches!(err, Error::Protocol(_)), "got {err:?}");
    assert!(
        err.to_string().contains("no queued response"),
        "message: {err}"
    );
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
    m.respond_json(r#"{"status":"ack"}"#);

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

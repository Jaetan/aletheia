// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Structured-logging behaviour against the real `libaletheia-ffi.so` (Slice
//! R4a). Set `ALETHEIA_LIB` to the built shared library. Drives a minimal
//! streaming flow through a capturing [`aletheia::Logger`] and asserts the
//! lifecycle / frame events fire — and that every captured event is a member of
//! the known vocabulary (the dynamic half of the cross-binding parity lock; the
//! static half is `log_events.rs`).

use std::sync::{Arc, Mutex};

use aletheia::log::events;
use aletheia::{check, CanId, Client, Dlc, LogRecord, Rational, SignalValue, Timestamp};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

/// The full set of event names the Rust client may emit.
const KNOWN: &[&str] = &[
    events::DBC_PARSED,
    events::PROPERTIES_SET,
    events::STREAM_STARTED,
    events::STREAM_ENDED,
    events::RTS_CORES_MISMATCH,
    events::FRAME_PROCESSED,
    events::ERROR_EVENT_SENT,
    events::REMOTE_EVENT_SENT,
    events::ENDSTREAM_UNCACHED_ATOM,
];

#[test]
fn lifecycle_events_fire_and_are_all_known() {
    let captured: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let c = Client::builder()
        .logger(move |rec: &LogRecord| {
            sink.lock().expect("lock").push(rec.event.to_string());
        })
        .build()
        .expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?");

    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");

    c.add_checks(&[check::signal("EngineSpeed").never_exceeds(1000)])
        .expect("add_checks");
    c.start_stream().expect("start stream");
    let frame = c
        .build_frame(
            msg,
            dlc,
            &[SignalValue {
                name: "EngineSpeed".to_string(),
                value: Rational::integer(100),
            }],
        )
        .expect("build_frame");
    c.send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send frame");
    let _ = c.end_stream().expect("end stream");

    let names = captured.lock().expect("lock").clone();
    // The expected lifecycle / frame events all fired.
    for want in [
        events::DBC_PARSED,
        events::PROPERTIES_SET,
        events::STREAM_STARTED,
        events::FRAME_PROCESSED,
        events::STREAM_ENDED,
    ] {
        assert!(names.iter().any(|e| e == want), "missing event {want:?}");
    }
    // Every captured event is a known vocabulary member (no rogue strings).
    for e in &names {
        assert!(KNOWN.contains(&e.as_str()), "unknown event emitted: {e:?}");
    }
}

#[test]
fn min_level_filters_below_threshold() {
    // With min_level = Warn, the debug `frame.processed` must not reach the sink,
    // but a warn/info event would (none fire in this DBC-only flow, so we just
    // assert the debug event is filtered).
    let captured: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&captured);
    let c = Client::builder()
        .logger(move |rec: &LogRecord| sink.lock().expect("lock").push(rec.event.to_string()))
        .min_level(aletheia::LogLevel::Warn)
        .build()
        .expect("init client");
    let _ = c.parse_dbc_text(MINIMAL).expect("parse DBC text"); // dbc.parsed is Info → filtered
    let names = captured.lock().expect("lock").clone();
    assert!(
        !names.iter().any(|e| e == events::DBC_PARSED),
        "Info event must be filtered at min_level=Warn, got: {names:?}"
    );
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Frame construction / update / batch-send tests against the real
//! `libaletheia-ffi.so`. Set `ALETHEIA_LIB` to the built shared library.

use aletheia::{
    CanId, Client, Dlc, ExtractionResult, Formula, Frame, FrameResponse, Predicate, Rational,
    SignalValue, Timestamp,
};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");
const EXTENDED: &str = include_str!("../../python/tests/fixtures/dbc_corpus/extended_can.dbc");
const MUX: &str = include_str!("../../python/tests/fixtures/dbc_corpus/multiplexing.dbc");

fn client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

/// A `(name, value)` signal injection.
fn sv(name: &str, num: i64, den: i64) -> SignalValue {
    SignalValue {
        name: name.to_string(),
        value: Rational::new(num, den).expect("valid rational"),
    }
}

/// Cross-multiply value equality — robust to reduced vs unreduced rationals.
fn value_is(ex: &ExtractionResult, name: &str, num: i64, den: i64) -> bool {
    ex.values
        .iter()
        .find(|v| v.name == name)
        .is_some_and(|v| v.value.numerator() * den == num * v.value.denominator())
}

#[test]
fn build_frame_encodes_signals_to_exact_bytes() {
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let msg = dbc
        .message_by_id(CanId::standard(256).expect("id"))
        .expect("EngineStatus");
    // EngineSpeed factor 1/4 @ bits 0..16 LE: 100 → raw 400 = 0x0190 → [0x90,0x01].
    // CoolantLevel factor 1 @ byte 3: 50 → 0x32.
    let bytes = c
        .build_frame(
            msg,
            Dlc::new(8).expect("dlc"),
            &[sv("EngineSpeed", 100, 1), sv("CoolantLevel", 50, 1)],
        )
        .expect("build_frame");
    assert_eq!(bytes.len(), 8);
    assert_eq!(bytes[0], 0x90, "EngineSpeed raw low byte");
    assert_eq!(bytes[1], 0x01, "EngineSpeed raw high byte");
    assert_eq!(bytes[3], 50, "CoolantLevel byte");
}

#[test]
fn build_then_extract_round_trips_representable_values() {
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    let bytes = c
        .build_frame(
            msg,
            dlc,
            &[sv("EngineSpeed", 100, 1), sv("EngineTemp", 25, 1)],
        )
        .expect("build_frame");
    let ex = c.extract_signals(id, dlc, &bytes).expect("extract_signals");
    assert!(value_is(&ex, "EngineSpeed", 100, 1), "{:?}", ex.values);
    assert!(value_is(&ex, "EngineTemp", 25, 1), "{:?}", ex.values);
}

#[test]
fn build_extract_round_trips_extended_id() {
    // The extended branch: message.extended → ext=1 to the build/extract FFI.
    let c = client();
    let dbc = c.parse_dbc_text(EXTENDED).expect("parse DBC text").dbc;
    let id = CanId::extended(256).expect("ext id");
    let msg = dbc.message_by_id(id).expect("Ext message");
    assert!(msg.extended, "id 256 extended message");
    let dlc = Dlc::new(8).expect("dlc");
    let bytes = c
        .build_frame(msg, dlc, &[sv("PayloadExt", 1234, 1)])
        .expect("build_frame");
    let ex = c.extract_signals(id, dlc, &bytes).expect("extract_signals");
    assert!(value_is(&ex, "PayloadExt", 1234, 1), "{:?}", ex.values);
}

#[test]
fn update_frame_splices_one_signal_and_preserves_the_rest() {
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    // Populate three signals, splice one, and confirm the other two survive —
    // catches both rebuild-from-zero and clobbering of untouched bytes (the
    // read-modify-write contract update_frame exists for).
    let base = c
        .build_frame(
            msg,
            dlc,
            &[
                sv("EngineSpeed", 100, 1),
                sv("EngineTemp", 25, 1),
                sv("CoolantLevel", 50, 1),
            ],
        )
        .expect("build_frame");
    let updated = c
        .update_frame(msg, dlc, &base, &[sv("EngineSpeed", 200, 1)])
        .expect("update_frame");
    let ex = c
        .extract_signals(id, dlc, &updated)
        .expect("extract_signals");
    assert!(
        value_is(&ex, "EngineSpeed", 200, 1),
        "spliced: {:?}",
        ex.values
    );
    assert!(
        value_is(&ex, "EngineTemp", 25, 1),
        "preserved: {:?}",
        ex.values
    );
    assert!(
        value_is(&ex, "CoolantLevel", 50, 1),
        "preserved: {:?}",
        ex.values
    );
}

#[test]
fn extract_signals_selects_by_mux_value() {
    let c = client();
    let dbc = c.parse_dbc_text(MUX).expect("parse DBC text").dbc;
    let id = CanId::standard(100).expect("id");
    let msg = dbc.message_by_id(id).expect("BasicMux");
    let dlc = Dlc::new(8).expect("dlc");

    // Mode=0 selects PayloadA (m0).
    let f0 = c
        .build_frame(msg, dlc, &[sv("Mode", 0, 1), sv("PayloadA", 500, 1)])
        .expect("build mode0");
    let e0 = c.extract_signals(id, dlc, &f0).expect("extract mode0");
    assert!(
        value_is(&e0, "PayloadA", 500, 1),
        "PayloadA present at Mode=0: {e0:?}"
    );

    // Mode=1 deselects PayloadA — it lands in the absent list, not values.
    let f1 = c
        .build_frame(msg, dlc, &[sv("Mode", 1, 1)])
        .expect("build mode1");
    let e1 = c.extract_signals(id, dlc, &f1).expect("extract mode1");
    assert!(
        e1.absent.iter().any(|n| n == "PayloadA"),
        "PayloadA absent at Mode=1: {e1:?}"
    );
    // Non-vacuous: Mode=1 selects PayloadB (m1), so the extraction is populated,
    // not empty/errored.
    assert!(
        value_is(&e1, "PayloadB", 0, 1),
        "PayloadB present at Mode=1: {e1:?}"
    );
}

#[test]
fn send_frames_batches_and_returns_per_frame_responses() {
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    let data1 = c
        .build_frame(msg, dlc, &[sv("EngineSpeed", 100, 1)])
        .expect("b1");
    let data2 = c
        .build_frame(msg, dlc, &[sv("EngineSpeed", 200, 1)])
        .expect("b2");

    let prop = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "EngineSpeed".to_string(),
        value: Rational::integer(1000),
    })));
    c.set_properties(&[prop]).expect("set properties");
    c.start_stream().expect("start stream");

    let frames = vec![
        Frame {
            timestamp: Timestamp(0),
            id,
            dlc,
            data: data1,
            brs: None,
            esi: None,
        },
        Frame {
            timestamp: Timestamp(1000),
            id,
            dlc,
            data: data2,
            brs: None,
            esi: None,
        },
    ];
    let (responses, err) = c.send_frames(&frames);
    assert!(err.is_none(), "no transport error: {err:?}");
    assert_eq!(responses.len(), 2, "one response per frame");
    let _final = c.end_stream().expect("end stream");
}

#[test]
fn send_frames_iter_matches_eager_responses_and_state() {
    // Equivalence — the contract's load-bearing test: identical frames through
    // send_frames (eager) and send_frames_iter (lazy) must yield identical
    // per-frame responses AND leave the stream in the identical final state.
    // This is what guarantees the eager and lazy loop wrappers cannot drift.
    let setup = client();
    let dbc = setup.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    let mk = |speed: i64, ts: u64| Frame {
        timestamp: Timestamp(ts),
        id,
        dlc,
        data: setup
            .build_frame(msg, dlc, &[sv("EngineSpeed", speed, 1)])
            .expect("build"),
        brs: None,
        esi: None,
    };
    // The middle frame violates Always(EngineSpeed < 1000) — a non-trivial mix
    // of ack and verdict responses, so equality is a real check, not all-acks.
    let frames = vec![mk(100, 0), mk(2000, 1000), mk(300, 2000)];
    let prop = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "EngineSpeed".to_string(),
        value: Rational::integer(1000),
    })));
    let streaming = |p: Formula| -> Client {
        let c = client();
        c.parse_dbc_text(MINIMAL).expect("parse DBC text");
        c.set_properties(&[p]).expect("set properties");
        c.start_stream().expect("start stream");
        c
    };

    let a = streaming(prop.clone());
    let (eager, eager_err) = a.send_frames(&frames);
    let a_end = a.end_stream().expect("end a");

    let b = streaming(prop);
    let lazy: Vec<FrameResponse> = b
        .send_frames_iter(frames.clone())
        .map(|r| r.expect("lazy frame ok"))
        .collect();
    let b_end = b.end_stream().expect("end b");

    assert!(eager_err.is_none(), "eager transport error: {eager_err:?}");
    assert_eq!(eager.len(), 3, "one response per frame");
    assert_eq!(eager, lazy, "identical per-frame responses");
    assert_eq!(a_end, b_end, "identical final stream state");
}

#[test]
fn build_frame_with_no_signals_is_zero_filled() {
    // Exercises the empty-array path (numSignals=0 → null array pointers).
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let msg = dbc
        .message_by_id(CanId::standard(256).expect("id"))
        .expect("EngineStatus");
    let bytes = c
        .build_frame(msg, Dlc::new(8).expect("dlc"), &[])
        .expect("build_frame");
    assert_eq!(bytes, vec![0u8; 8]);
}

#[test]
fn payload_length_must_match_dlc() {
    // The data-length-vs-DLC invariant is enforced before the FFI (Copilot review).
    let c = client();
    let dbc = c.parse_dbc_text(MINIMAL).expect("parse DBC text").dbc;
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    let short = [0u8; 4]; // 4 bytes for an 8-byte DLC
    assert!(
        c.extract_signals(id, dlc, &short).is_err(),
        "extract_signals must reject a length/DLC mismatch"
    );
    assert!(
        c.update_frame(msg, dlc, &short, &[sv("EngineSpeed", 100, 1)])
            .is_err(),
        "update_frame must reject a length/DLC mismatch"
    );
}

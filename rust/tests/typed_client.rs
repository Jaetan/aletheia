// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed-surface integration tests against the real `libaletheia-ffi.so`.
//!
//! Exercises the binary-FFI streaming path end-to-end: load a DBC, bind a
//! property, stream a violating frame, and confirm the typed verdict. Set
//! `ALETHEIA_LIB` to the built shared library (run_ci / CI does this).

use aletheia::{
    CanId, Client, Dlc, Formula, FrameResponse, Predicate, Rational, Timestamp, Verdict,
};

/// A known-good DBC the verified text parser accepts (the shared corpus
/// `minimal.dbc`). `EngineSpeed` lives in message 256 at bits 0..16, little-
/// endian, factor 0.25 — so raw `N` decodes to `N * 0.25` rpm.
const DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

fn engine_speed_frame(rpm: u32) -> [u8; 8] {
    let raw = (rpm * 4) as u16; // raw = rpm / 0.25
    [raw as u8, (raw >> 8) as u8, 0, 0, 0, 0, 0, 0]
}

#[test]
fn streaming_detects_violation() {
    let client =
        Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?");

    client.parse_dbc_text(DBC).expect("parse DBC text");

    // G(EngineSpeed < 1000): a 4000 rpm frame (in range [0,8000]) violates it.
    let prop = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "EngineSpeed".to_string(),
        value: Rational::integer(1000),
    })));
    client.set_properties(&[prop]).expect("set properties");
    client.start_stream().expect("start stream");

    let id = CanId::standard(256).unwrap();
    let dlc = Dlc::new(8).unwrap();
    let resp = client
        .send_frame(Timestamp(0), id, dlc, &engine_speed_frame(4000), None, None)
        .expect("send frame");

    match resp {
        FrameResponse::Verdicts(results) => {
            let violation = results
                .iter()
                .find(|r| r.verdict == Verdict::Fails)
                .expect("expected a Fails verdict for a 4000 rpm frame under G(EngineSpeed<1000)");
            // The raw core response carries the reason; client-side enrichment
            // (attaching signal values) is a separate binding feature, tracked
            // `planned` for Rust, so `enrichment` is absent here.
            assert!(
                !violation.reason.is_empty(),
                "expected a non-empty core reason on the violation"
            );
            assert_eq!(violation.property_index, 0);
        }
        FrameResponse::Ack => panic!("expected a property_batch violation, got Ack"),
    }

    let _final = client.end_stream().expect("end stream");
}

#[test]
fn extract_signals_decodes_values() {
    let client = Client::new().expect("init client");
    client.parse_dbc_text(DBC).expect("parse DBC text");

    let id = CanId::standard(256).unwrap();
    let dlc = Dlc::new(8).unwrap();
    let result = client
        .extract_signals(id, dlc, &engine_speed_frame(4000))
        .expect("extract signals");

    assert!(
        result.values.iter().any(|s| s.name == "EngineSpeed"),
        "expected EngineSpeed among extracted values: {:?}",
        result.values
    );
    assert!(
        result.errors.is_empty(),
        "unexpected extraction errors: {:?}",
        result.errors
    );
}

#[test]
fn out_of_range_value_is_an_extraction_error() {
    // raw 0xFFFF = 16383.75 rpm exceeds EngineSpeed's declared max (8000); the
    // core reports it as an extraction error rather than a value (matching the
    // behaviour proven across the other bindings).
    let client = Client::new().expect("init client");
    client.parse_dbc_text(DBC).expect("parse DBC text");

    let id = CanId::standard(256).unwrap();
    let dlc = Dlc::new(8).unwrap();
    let result = client
        .extract_signals(id, dlc, &[0xFF, 0xFF, 0, 0, 0, 0, 0, 0])
        .expect("extract signals");

    assert!(
        !result.errors.is_empty(),
        "expected an out-of-range extraction error, got values {:?}",
        result.values
    );
}

#[test]
fn typed_constructors_reject_invalid_input() {
    // These need no shared library — pure construction-time validation.
    assert!(
        CanId::standard(2048).is_err(),
        "2048 exceeds the 11-bit range"
    );
    assert!(
        CanId::extended(1 << 29).is_err(),
        "2^29 exceeds the 29-bit range"
    );
    assert!(Dlc::new(16).is_err(), "DLC 16 is out of range");
    assert!(Rational::new(1, 0).is_err(), "zero denominator is rejected");
    assert!(
        Rational::new(1, -2).is_err(),
        "negative denominator is rejected"
    );
    assert!(CanId::standard(2047).is_ok());
    assert!(Dlc::new(15).is_ok());
}

#[test]
fn canfd_frame_with_brs_esi_is_accepted() {
    // Behaviourally back the `can_fd` + `canfd_brs_esi_fields` matrix claims:
    // a CAN-FD frame (DLC 10 → 16-byte payload) with BRS/ESI set must be
    // accepted by the core (the kernel passes BRS/ESI through as metadata).
    let client = Client::new().expect("init client");
    client.parse_dbc_text(DBC).expect("parse DBC text");
    client.start_stream().expect("start stream");

    let id = CanId::standard(256).unwrap();
    let dlc = Dlc::new(10).unwrap();
    assert_eq!(
        dlc.to_bytes(),
        16,
        "DLC 10 encodes a 16-byte CAN-FD payload"
    );

    let data = [0u8; 16];
    client
        .send_frame(Timestamp(0), id, dlc, &data, Some(true), Some(false))
        .expect("CAN-FD frame with BRS=true, ESI=false must be accepted");

    let _final = client.end_stream().expect("end stream");
}

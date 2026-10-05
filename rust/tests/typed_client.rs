// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed-surface integration tests against the real `libaletheia-ffi.so`.
//!
//! Exercises the binary-FFI streaming path end-to-end: load a DBC, bind a
//! property, stream a violating frame, and confirm the typed verdict. Set
//! `ALETHEIA_LIB` to the built shared library (run_ci / CI does this).

use aletheia::{
    CanId, Client, Dlc, Error, Formula, FrameResponse, IssueCode, IssueSeverity, Predicate,
    Rational, Timestamp, Verdict,
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
fn parse_dbc_text_lifts_validation_failure() {
    // A syntactically valid DBC that fails structural validation must surface
    // as the typed Error::ValidationFailed carrying the issue list — not the
    // generic Error::Core. Derive the invalid input from the known-good corpus
    // fixture by renaming EngineTemp to EngineSpeed, so message 256 carries a
    // duplicate signal name.
    let client = Client::new().expect("init client");

    let broken = DBC.replace("SG_ EngineTemp ", "SG_ EngineSpeed ");
    assert_ne!(broken, DBC, "the derivation must rewrite a signal name");

    let err = client
        .parse_dbc_text(&broken)
        .expect_err("a duplicate signal name must fail validation");
    match err {
        Error::ValidationFailed {
            code,
            message,
            has_errors,
            issues,
        } => {
            assert_eq!(code, "handler_validation_failed");
            assert!(
                !message.is_empty(),
                "the legacy wire message must be carried unchanged"
            );
            assert!(has_errors, "a duplicate signal name is error-severity");
            assert!(
                issues.iter().any(|i| i.severity == IssueSeverity::Error
                    && i.code == IssueCode::DuplicateSignalName),
                "expected an error-severity duplicate_signal_name issue, got {issues:?}"
            );
        }
        other => panic!("expected Error::ValidationFailed, got {other:?}"),
    }
}

#[test]
fn a_declared_range_beyond_the_bits_refuses_the_dbc() {
    // CoolantLevel is 8 bits unsigned at factor 1, offset 0, so its bits carry
    // [0, 255]: widening either declared bound past that refuses the DBC with
    // an error-severity range_exceeds_bits issue naming the bound.
    let client = Client::new().expect("init client");
    let original = "SG_ CoolantLevel : 24|8@1+ (1,0) [0|255]";
    let cases = [
        (
            "SG_ CoolantLevel : 24|8@1+ (1,0) [0|1000]",
            "Message 'EngineStatus', signal 'CoolantLevel': \
             declared maximum lies above the values its bits carry",
        ),
        (
            "SG_ CoolantLevel : 24|8@1+ (1,0) [-5|255]",
            "Message 'EngineStatus', signal 'CoolantLevel': \
             declared minimum lies below the values its bits carry",
        ),
    ];
    for (declared, detail) in cases {
        let widened = DBC.replace(original, declared);
        assert_ne!(widened, DBC, "the derivation must rewrite CoolantLevel");
        match client.parse_dbc_text(&widened) {
            Err(Error::ValidationFailed {
                code,
                has_errors,
                issues,
                ..
            }) => {
                assert_eq!(code, "handler_validation_failed");
                assert!(has_errors, "range_exceeds_bits is error-severity");
                let named: Vec<_> = issues
                    .iter()
                    .filter(|i| i.code == IssueCode::RangeExceedsBits)
                    .collect();
                assert_eq!(named.len(), 1, "one issue per bound, got {issues:?}");
                assert_eq!(named[0].severity, IssueSeverity::Error);
                assert_eq!(named[0].detail, detail);
            }
            other => panic!("expected Error::ValidationFailed, got {other:?}"),
        }
    }
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

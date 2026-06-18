// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Check-DSL + `add_checks` tests against the real `libaletheia-ffi.so`
//! (Slice R3a). Set `ALETHEIA_LIB` to the built shared library.

use aletheia::{
    check, CanId, Client, Dlc, FrameResponse, Rational, SignalValue, Timestamp, Verdict,
};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

fn client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

#[test]
fn add_checks_binds_a_dsl_check_and_detects_a_violation() {
    let c = client();
    let (dbc, _) = c.parse_dbc_text(MINIMAL).expect("parse DBC text");
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");

    // A check built via the fluent DSL, attached with add_checks.
    let chk = check::signal("EngineSpeed")
        .never_exceeds(1000)
        .named("speed-limit")
        .with_severity("error");
    c.add_checks(&[chk]).expect("add_checks");
    c.start_stream().expect("start stream");

    // 4000 rpm violates G(EngineSpeed < 1000).
    let frame = c
        .build_frame(
            msg,
            dlc,
            &[SignalValue {
                name: "EngineSpeed".to_string(),
                value: Rational::integer(4000),
            }],
        )
        .expect("build_frame");
    let resp = c
        .send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send frame");

    match resp {
        FrameResponse::Verdicts(results) => {
            let v = results
                .iter()
                .find(|r| r.verdict == Verdict::Fails)
                .expect("expected a Fails verdict for 4000 rpm under never_exceeds(1000)");
            // property_index is the position of the check in the add_checks slice.
            assert_eq!(v.property_index, 0);
        }
        FrameResponse::Ack => panic!("expected a violation, got Ack"),
    }
    let _final = c.end_stream().expect("end stream");
}

#[test]
fn add_checks_holds_for_a_conforming_frame() {
    let c = client();
    let (dbc, _) = c.parse_dbc_text(MINIMAL).expect("parse DBC text");
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");

    c.add_checks(&[check::signal("EngineSpeed").never_exceeds(1000)])
        .expect("add_checks");
    c.start_stream().expect("start stream");

    // 100 rpm conforms — no Fails verdict.
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
    let resp = c
        .send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send frame");
    // A conforming frame produces no violation — either `Ack` (G has not decided)
    // or `Verdicts` with no `Fails`. Check both branches so the assert is never
    // vacuous; `Ack` is a valid, expected outcome here (not a failure).
    let has_fail = match resp {
        FrameResponse::Ack => false,
        FrameResponse::Verdicts(results) => results.iter().any(|r| r.verdict == Verdict::Fails),
    };
    assert!(
        !has_fail,
        "conforming frame must not produce a Fails verdict"
    );
    let _final = c.end_stream().expect("end stream");
}

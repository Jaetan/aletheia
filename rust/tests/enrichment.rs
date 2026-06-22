// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Client-side violation enrichment against the real `libaletheia-ffi.so`
//! (Slice R4b). Set `ALETHEIA_LIB` to the built shared library. A streaming
//! violation must carry an [`aletheia::Enrichment`] computed client-side: the
//! referenced signal's value, the formula description, and a combined reason.

use aletheia::{
    check, CanId, Client, Dlc, FrameResponse, Rational, SignalValue, Timestamp, Verdict,
};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

#[test]
fn streaming_violation_carries_enrichment() {
    let c = Client::new().expect("init client — is ALETHEIA_LIB set?");
    let (dbc, _) = c.parse_dbc_text(MINIMAL).expect("parse DBC text");
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
                value: Rational::integer(4000),
            }],
        )
        .expect("build_frame");
    let resp = c
        .send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send frame");

    let FrameResponse::Verdicts(results) = resp else {
        panic!("expected a violation (Verdicts), got Ack");
    };
    let v = results
        .iter()
        .find(|r| r.verdict == Verdict::Fails)
        .expect("a Fails verdict for 4000 under never_exceeds(1000)");
    let e = v
        .enrichment
        .as_ref()
        .expect("a violation must carry client-side enrichment");

    assert!(
        e.signals
            .iter()
            .any(|(n, val)| n == "EngineSpeed" && *val == Rational::integer(4000)),
        "enrichment signals: {:?}",
        e.signals
    );
    assert!(
        e.formula_desc.contains("EngineSpeed <= 1000"),
        "formula_desc: {}",
        e.formula_desc
    );
    assert!(
        e.enriched_reason.contains("EngineSpeed = 4000"),
        "enriched_reason: {}",
        e.enriched_reason
    );

    let _ = c.end_stream().expect("end stream");
}

#[test]
fn no_enrichment_without_a_violation() {
    let c = Client::new().expect("init client");
    let (dbc, _) = c.parse_dbc_text(MINIMAL).expect("parse DBC text");
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");
    c.add_checks(&[check::signal("EngineSpeed").never_exceeds(1000)])
        .expect("add_checks");
    c.start_stream().expect("start stream");
    // 100 conforms — no Fails, so any Verdicts carry no enrichment.
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
    if let FrameResponse::Verdicts(results) = c
        .send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send")
    {
        assert!(
            results
                .iter()
                .all(|r| r.enrichment.is_none() || r.verdict != Verdict::Fails),
            "conforming frame must not produce an enriched Fails"
        );
    }
    let _ = c.end_stream().expect("end stream");
}

#[test]
fn end_of_stream_violation_carries_enrichment() {
    // The trigger fires (EngineSpeed > 1000) but the response never arrives
    // within the 60s window before the stream ends, so the core finalizes a
    // Fails at end_stream — exercising the enrich_eos path (re-extraction from
    // the last frame seen per CAN id), not the per-frame streaming path.
    let c = Client::new().expect("init client");
    let (dbc, _) = c.parse_dbc_text(MINIMAL).expect("parse DBC text");
    let id = CanId::standard(256).expect("id");
    let msg = dbc.message_by_id(id).expect("EngineStatus");
    let dlc = Dlc::new(8).expect("dlc");

    let chk = check::when("EngineSpeed")
        .exceeds(1000)
        .then("EngineSpeed")
        .equals(0)
        .within(60_000)
        .expect("check");
    c.add_checks(&[chk]).expect("add_checks");
    c.start_stream().expect("start stream");

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
    // Pending during streaming (window not expired) — no verdict yet.
    c.send_frame(Timestamp(0), id, dlc, &frame, None, None)
        .expect("send frame");

    let result = c.end_stream().expect("end stream");
    let pr = result
        .results
        .iter()
        .find(|r| r.verdict == Verdict::Fails)
        .expect("an end-of-stream Fails for the unsatisfied within-window response");
    let e = pr
        .enrichment
        .as_ref()
        .expect("an end-of-stream violation must carry enrichment");
    // enrich_eos re-extracted the signal value from the last frame seen.
    assert!(
        e.signals
            .iter()
            .any(|(n, v)| n == "EngineSpeed" && *v == Rational::integer(4000)),
        "enrichment signals: {:?}",
        e.signals
    );
    assert!(
        e.enriched_reason.contains("EngineSpeed = 4000"),
        "enriched_reason: {}",
        e.enriched_reason
    );
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! AsyncClient against the real `libaletheia-ffi.so` (feature `async`). Set
//! `ALETHEIA_LIB`. Runtime-agnostic: the tests drive futures with
//! `futures::executor::block_on` and cancel a pending call deterministically
//! with `select` against an immediately-ready future — no sleeps.

#![cfg(feature = "async")]

use aletheia::{
    check, AsyncClient, CanId, Dlc, FrameResponse, Rational, SignalValue, Timestamp, Verdict,
};
use futures::executor::block_on;
use futures::future::{ready, select};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");

#[test]
fn async_streaming_flow_carries_enrichment() {
    block_on(async {
        let c = AsyncClient::new().await.expect("init async client");
        let (dbc, _) = c
            .parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("parse DBC text");
        let id = CanId::standard(256).expect("id");
        let msg = dbc.message_by_id(id).expect("EngineStatus").clone();
        let dlc = Dlc::new(8).expect("dlc");

        c.add_checks(vec![check::signal("EngineSpeed").never_exceeds(1000)])
            .await
            .expect("add_checks");
        c.start_stream().await.expect("start stream");

        let frame = c
            .build_frame(
                msg,
                dlc,
                vec![SignalValue {
                    name: "EngineSpeed".to_string(),
                    value: Rational::integer(4000),
                }],
            )
            .await
            .expect("build_frame");
        let resp = c
            .send_frame(Timestamp(0), id, dlc, frame, None, None)
            .await
            .expect("send frame");

        let FrameResponse::Verdicts(results) = resp else {
            panic!("expected a violation (Verdicts), got Ack");
        };
        let v = results
            .iter()
            .find(|r| r.verdict == Verdict::Fails)
            .expect("a Fails verdict");
        assert!(
            v.enrichment
                .as_ref()
                .expect("enrichment on the violation")
                .enriched_reason
                .contains("EngineSpeed = 4000"),
            "enrichment carried across the async boundary"
        );
        let _ = c.end_stream().await.expect("end stream");
    });
}

#[test]
fn cancelled_call_does_not_break_the_client() {
    block_on(async {
        let c = AsyncClient::new().await.expect("init async client");
        // A first call works.
        c.parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("first parse");
        // Race a second call against an immediately-ready future: the ready
        // future wins, so the parse future is polled (its job is sent) then
        // dropped — i.e. cancelled — deterministically, with no sleep.
        let pending = Box::pin(c.parse_dbc_text(MINIMAL.to_string()));
        let _ = select(pending, Box::pin(ready(()))).await;
        // The client still works after a cancelled call (no deadlock / no
        // corruption of the worker's StreamState).
        c.parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("parse after a cancelled call");
    });
}

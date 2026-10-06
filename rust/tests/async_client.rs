// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! AsyncClient tests (feature `async`). Each hosts its sync client on a
//! `TurnExecutor`, so every queued call runs on the test's own thread at its
//! turn, in queue order: no worker thread, no runtime and no sleep. Most drive
//! the real `libaletheia-ffi.so` (set `ALETHEIA_LIB`); the cancellation tests
//! use an injected backend and need no `.so`. A call is cancelled by dropping
//! its future: before its turn (a `select` against an immediately-ready
//! future), or from inside the backend while its turn runs.

#![cfg(feature = "async")]

use std::cell::{Cell, RefCell};
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;
use std::task::{Context, Waker};

use aletheia::testing::TurnExecutor;
use aletheia::{
    check, Backend, CanId, Client, Dlc, Error, Frame, FrameResponse, MockBackend, Rational,
    SignalInjection, SignalValue, Timestamp, Verdict,
};
use futures::future::{ready, select};

const MINIMAL: &str = include_str!("../../python/tests/fixtures/dbc_corpus/minimal.dbc");
const PING: &str = r#"{"command":"ping"}"#;
const ACK: &str = r#"{"status":"ack"}"#;

#[test]
fn async_streaming_flow_carries_enrichment() {
    let turns = TurnExecutor::new();
    let c = turns.adopt(Client::new().expect("init client"));
    turns.block_on(async {
        let dbc = c
            .parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("parse DBC text")
            .dbc;
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

/// A call dropped before its turn never reaches the backend, and the client
/// serves the next one: the worker's queued-cancel guard, reached every run.
#[test]
fn a_call_cancelled_before_its_turn_never_reaches_the_backend() {
    let turns = TurnExecutor::new();
    let mock = MockBackend::new();
    mock.respond_json(ACK).respond_json(ACK);
    let c = turns.adopt(Client::builder().build_with_backend(Box::new(mock.clone())));
    turns.block_on(async {
        assert_eq!(c.process(PING.to_string()).await.expect("first call"), ACK);
        // The ready future wins, so the call is queued on its first poll and
        // then dropped, before any turn has run it.
        let pending = Box::pin(c.process(r#"{"command":"cancelled"}"#.to_string()));
        let _ = select(pending, Box::pin(ready(()))).await;
        assert_eq!(
            c.process(PING.to_string())
                .await
                .expect("call after the cancelled one"),
            ACK
        );
    });
    assert_eq!(
        mock.captured(),
        vec![PING.to_string(), PING.to_string()],
        "the cancelled call was skipped at its turn, never sent",
    );
}

#[test]
fn async_send_frames_stream_yields_per_frame() {
    use futures::StreamExt;
    let turns = TurnExecutor::new();
    let c = turns.adopt(Client::new().expect("init client"));
    turns.block_on(async {
        let dbc = c
            .parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("parse DBC text")
            .dbc;
        let id = CanId::standard(256).expect("id");
        let msg = dbc.message_by_id(id).expect("EngineStatus").clone();
        let dlc = Dlc::new(8).expect("dlc");
        c.add_checks(vec![check::signal("EngineSpeed").never_exceeds(1000)])
            .await
            .expect("add_checks");
        c.start_stream().await.expect("start stream");

        let mut frames = Vec::new();
        for (i, speed) in [100i64, 4000, 200].into_iter().enumerate() {
            let data = c
                .build_frame(
                    msg.clone(),
                    dlc,
                    vec![SignalValue {
                        name: "EngineSpeed".to_string(),
                        value: Rational::integer(speed),
                    }],
                )
                .await
                .expect("build_frame");
            frames.push(Frame {
                timestamp: Timestamp(i as u64 * 1000),
                id,
                dlc,
                data,
                brs: None,
                esi: None,
            });
        }

        // Drain the lazy Stream — one job queued per poll, run at its turn.
        let out: Vec<_> = c.send_frames_stream(frames).collect().await;
        assert_eq!(out.len(), 3, "one item per frame");
        assert!(out.iter().all(Result::is_ok), "all frames sent");
        // The 4000 frame violates never_exceeds(1000) — the stream carries it.
        let violated = out.iter().any(|r| {
            matches!(r, Ok(FrameResponse::Verdicts(v)) if v.iter().any(|p| p.verdict == Verdict::Fails))
        });
        assert!(violated, "the over-limit frame must surface a violation");
        let _ = c.end_stream().await.expect("end stream");
    });
}

#[test]
fn async_send_frames_stream_is_lazy_and_partially_consumable() {
    use futures::StreamExt;
    let turns = TurnExecutor::new();
    let c = turns.adopt(Client::new().expect("init client"));
    turns.block_on(async {
        c.parse_dbc_text(MINIMAL.to_string())
            .await
            .expect("parse DBC text");
        let id = CanId::standard(256).expect("id");
        let dlc = Dlc::new(8).expect("dlc");
        c.start_stream().await.expect("start stream");
        let frames: Vec<Frame> = (0u64..5)
            .map(|i| Frame {
                timestamp: Timestamp(i * 1000),
                id,
                dlc,
                data: vec![0u8; 8],
                brs: None,
                esi: None,
            })
            .collect();

        // Pull only the first 2 of 5 — the remaining 3 frames are never sent
        // (the Stream is pull-driven; `unfold` stops once `take` is satisfied).
        let prefix: Vec<_> = c.send_frames_stream(frames).take(2).collect().await;
        assert_eq!(prefix.len(), 2, "only the consumed prefix is produced");
        assert!(prefix.iter().all(Result::is_ok));
        let _ = c.end_stream().await.expect("end stream");
    });
}

/// A [`Backend`] that counts its calls and runs a hook inside the first one,
/// the moment a call is in flight. It lives on the test's thread, as the turn
/// executor hosts its client there, so it needs neither `Send` nor a lock.
/// What runs inside the first call, once.
type Hook = Rc<RefCell<Option<Box<dyn FnOnce()>>>>;

#[derive(Clone, Default)]
struct HookBackend {
    calls: Rc<Cell<usize>>,
    inside_first_call: Hook,
}

impl Backend for HookBackend {
    fn process(&self, _input: &str) -> Result<String, Error> {
        self.calls.set(self.calls.get() + 1);
        let hook = self.inside_first_call.borrow_mut().take();
        if let Some(hook) = hook {
            hook();
        }
        Ok(ACK.to_string())
    }

    // Only `process` is driven; the typed/binary ops are never reached.
    fn send_frame_binary(
        &self,
        _: Timestamp,
        _: CanId,
        _: Dlc,
        _: &[u8],
        _: Option<bool>,
        _: Option<bool>,
    ) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn send_error_binary(&self, _: Timestamp) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn send_remote_binary(&self, _: Timestamp, _: CanId) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn start_stream_binary(&self) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn end_stream_binary(&self) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn format_dbc_binary(&self) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn extract_signals_binary(&self, _: CanId, _: Dlc, _: &[u8]) -> Result<String, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn build_frame_bin(
        &self,
        _: u32,
        _: bool,
        _: Dlc,
        _: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        unreachable!("the hook backend only drives process")
    }
    fn update_frame_bin(
        &self,
        _: u32,
        _: bool,
        _: Dlc,
        _: &[u8],
        _: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        unreachable!("the hook backend only drives process")
    }
}

/// A call whose future is dropped while it is inside the backend runs to
/// completion, its result is discarded, and the client serves the next call:
/// commit-prefix, no rollback. The drop happens from inside the call, at the
/// one moment the call is in flight, so no rendezvous with a thread is needed.
#[test]
fn a_call_cancelled_in_flight_completes_and_leaves_the_client_usable() {
    type Call = Pin<Box<dyn Future<Output = Result<String, Error>>>>;
    let turns = TurnExecutor::new();
    let backend = HookBackend::default();
    let client =
        Arc::new(turns.adopt(Client::builder().build_with_backend(Box::new(backend.clone()))));

    let caller = Arc::clone(&client);
    let in_flight: Call = Box::pin(async move { caller.process(PING.to_string()).await });
    let slot: Rc<RefCell<Option<Call>>> = Rc::new(RefCell::new(Some(in_flight)));
    // The first poll queues the call and parks on its reply.
    let mut cx = Context::from_waker(Waker::noop());
    assert!(
        slot.borrow_mut()
            .as_mut()
            .expect("the call is held")
            .as_mut()
            .poll(&mut cx)
            .is_pending(),
        "the first poll queues the call",
    );
    let dropped = Rc::clone(&slot);
    *backend.inside_first_call.borrow_mut() =
        Some(Box::new(move || drop(dropped.borrow_mut().take())));

    assert!(turns.run_turn(), "the queued call runs at this turn");
    assert!(
        slot.borrow().is_none(),
        "its future was dropped while the call was inside the backend"
    );
    assert_eq!(
        backend.calls.get(),
        1,
        "the cancelled call ran to completion"
    );

    let next = turns
        .block_on(client.process(PING.to_string()))
        .expect("a call after an in-flight cancellation still succeeds");
    assert_eq!(next, ACK);
    assert_eq!(
        backend.calls.get(),
        2,
        "the next call reached the backend too"
    );
}

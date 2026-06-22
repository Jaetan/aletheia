// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! AsyncClient tests (feature `async`). Most drive the real
//! `libaletheia-ffi.so` (set `ALETHEIA_LIB`); the in-flight cancellation test
//! injects a `Send` gating backend via `ClientBuilder::build_async_with_backend`
//! and needs no `.so`. Runtime-agnostic: futures are driven with
//! `futures::executor::block_on`; pending calls are cancelled deterministically
//! (a `select` against an immediately-ready future, or a hand-driven poll against
//! a backend rendezvous) — never with sleeps.

#![cfg(feature = "async")]

use std::sync::{Arc, Condvar, Mutex};

use aletheia::{
    check, AsyncClient, Backend, CanId, ClientBuilder, Dlc, Error, Frame, FrameResponse, Rational,
    SignalInjection, SignalValue, Timestamp, Verdict,
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

#[test]
fn async_send_frames_stream_yields_per_frame() {
    use futures::StreamExt;
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

        // Drain the lazy Stream — one worker job dispatched per poll.
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
    block_on(async {
        let c = AsyncClient::new().await.expect("init async client");
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

/// Shared rendezvous state for [`GatingBackend`]: `entered` flips when the worker
/// reaches the FFI, `proceed` is the sticky release latch, `calls` counts entries.
#[derive(Default)]
struct GateState {
    entered: bool,
    proceed: bool,
    calls: usize,
}

/// A `Send` gating [`Backend`] for the deterministic in-flight cancellation test.
/// Its [`process`](Backend::process) blocks on a condvar rendezvous so the test
/// can pin the worker *inside* the FFI call — past the queued-cancel guard —
/// exactly mirroring the C++ `HoldingBackend` (entered / proceed flags) and
/// Python's `gated_backend`. The public `MockBackend` cannot serve here: it is
/// `Rc`-based and so `!Send`, but `build_async_with_backend` moves the backend to
/// the worker thread, which requires `Send`.
///
/// `proceed` is **sticky**: once released, every later call passes straight
/// through, so the post-cancel "does a fresh call still work?" probe is not
/// re-gated. `Mutex<GateState>` (a struct, not `Mutex<bool>`) pairs with the
/// `Condvar` and sidesteps `clippy::mutex_atomic`.
#[derive(Clone, Default)]
struct GatingBackend {
    inner: Arc<(Mutex<GateState>, Condvar)>,
}

impl GatingBackend {
    /// Block until `process` has entered the rendezvous (the worker is mid-FFI).
    /// `Condvar` releases the lock while parked, so the worker can still progress.
    fn wait_until_entered(&self) {
        let (mu, cv) = &*self.inner;
        let mut s = mu.lock().expect("gate mutex not poisoned");
        while !s.entered {
            s = cv.wait(s).expect("gate condvar not poisoned");
        }
    }

    /// Release the in-flight call; sticky — every later call passes through.
    fn release(&self) {
        let (mu, cv) = &*self.inner;
        let mut s = mu.lock().expect("gate mutex not poisoned");
        s.proceed = true;
        cv.notify_all();
    }

    /// How many times `process` has been entered.
    fn calls(&self) -> usize {
        self.inner.0.lock().expect("gate mutex not poisoned").calls
    }
}

impl Backend for GatingBackend {
    fn process(&self, _input: &str) -> Result<String, Error> {
        let (mu, cv) = &*self.inner;
        let mut s = mu.lock().expect("gate mutex not poisoned");
        s.calls += 1;
        s.entered = true;
        cv.notify_all(); // wake wait_until_entered
        while !s.proceed {
            s = cv.wait(s).expect("gate condvar not poisoned");
        }
        Ok(r#"{"status":"ack"}"#.to_string())
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
        unreachable!("gating backend only drives process")
    }
    fn send_error_binary(&self, _: Timestamp) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn send_remote_binary(&self, _: Timestamp, _: CanId) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn start_stream_binary(&self) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn end_stream_binary(&self) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn format_dbc_binary(&self) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn extract_signals_binary(&self, _: CanId, _: Dlc, _: &[u8]) -> Result<String, Error> {
        unreachable!("gating backend only drives process")
    }
    fn build_frame_bin(
        &self,
        _: u32,
        _: bool,
        _: Dlc,
        _: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        unreachable!("gating backend only drives process")
    }
    fn update_frame_bin(
        &self,
        _: u32,
        _: bool,
        _: Dlc,
        _: &[u8],
        _: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        unreachable!("gating backend only drives process")
    }
}

/// Deterministically pins the **in-flight** cancellation path (the queued path is
/// covered by `cancelled_call_does_not_break_the_client` above) using an injected
/// `Send` gating backend — no `.so`, no sleeps. We hand-poll a call once to
/// enqueue it, rendezvous until the worker is provably mid-FFI (past the
/// queued-cancel guard), then drop the future to cancel and assert the worker is
/// not wedged: a fresh call still returns the canned ack.
#[test]
fn in_flight_cancel_via_injected_backend_leaves_the_worker_usable() {
    use std::future::Future;
    use std::task::{Context, Waker};

    let gate = GatingBackend::default();
    let probe = gate.clone(); // shares the same Arc rendezvous state

    // Build the async client over the gating backend — no `.so` involved.
    let client = block_on(ClientBuilder::default().build_async_with_backend(Box::new(gate)))
        .expect("build async client over the injected backend");

    // Poll the call once so its job is enqueued. The enqueue (`sender.send(job)`)
    // runs synchronously on the first poll, before the future parks on the reply,
    // so a no-op waker suffices — we never await a wakeup; the rendezvous is
    // driven by hand below. `Box::pin` (not `pin!`) so the future is *owned* here:
    // dropping it below truly drops the future — and its reply receiver — which is
    // the cancellation; a `pin!` would only drop the borrow, never cancelling.
    let mut fut = Box::pin(client.process(r#"{"command":"ping"}"#.to_string()));
    let mut cx = Context::from_waker(Waker::noop());
    assert!(
        fut.as_mut().poll(&mut cx).is_pending(),
        "first poll enqueues the job and parks on the reply",
    );

    // Block until the worker is INSIDE process() — past the queued-cancel guard
    // (async_client.rs `run`: the job runs `f(c)` only while the reply receiver is
    // still alive). Reaching here proves the in-flight path; had the job been
    // skipped, `entered` would never flip and this would hang (CI timeout).
    probe.wait_until_entered();
    assert_eq!(
        probe.calls(),
        1,
        "exactly the in-flight call has entered the FFI"
    );

    // Cancel the in-flight call by dropping its future (drops the reply receiver).
    // The worker is already past the guard, so the call runs to completion and its
    // result is discarded — never aborted mid-FFI (commit-prefix, no rollback).
    drop(fut);
    probe.release();

    // The worker must not be wedged and the StreamState must be intact: a fresh
    // call (sticky-proceed → not re-gated) returns the canned ack.
    let resp = block_on(client.process(r#"{"command":"ping"}"#.to_string()))
        .expect("a call after an in-flight cancellation still succeeds");
    assert_eq!(resp, r#"{"status":"ack"}"#);
    assert_eq!(
        probe.calls(),
        2,
        "the post-cancel call also reached the backend"
    );
}

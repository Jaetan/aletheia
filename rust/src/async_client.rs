// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Runtime-agnostic async client (feature `async`) — an async mirror of
//! [`Client`](crate::Client).
//!
//! The sync `Client` is `!Send` (a thread-pinned `StreamState`), so [`AsyncClient`]
//! owns it on a dedicated **worker thread** and talks to it over a channel: each
//! async method sends a job — a closure capturing its (owned) arguments and a
//! `oneshot` reply sender — and `.await`s the reply. The handle is a
//! `Mutex`-wrapped channel sender, so `AsyncClient` is `Send + Sync`; its
//! borrowing futures are therefore `Send`, so it can be `tokio::spawn`ed on a
//! multi-thread runtime (`mpsc::Sender` is `Send` but `!Sync`, hence the
//! `Mutex` — held only for the brief enqueue, never across an `.await`).
//!
//! It is **runtime-agnostic**: only the reply `oneshot` (from `futures-channel`)
//! is used, never a runtime, so it works under tokio, async-std, or smol — the
//! caller brings the executor.
//!
//! ## Cancellation (the contract: `docs/architecture/CANCELLATION.md`)
//! Dropping a method's future before it resolves cancels the call. Both cases
//! are contract-correct:
//! - **Queued, not yet started:** the worker skips the job (the closure sees the
//!   reply sender is cancelled and returns *without* the FFI call) — no frame is
//!   committed. A queued job is "between FFI calls", where cancellation is honored.
//! - **In-flight (inside the FFI call):** the call runs to completion on the
//!   worker and advances `StreamState`; its result is discarded (commit-prefix,
//!   no rollback). The next call runs after it.

use std::sync::mpsc::{self, Sender};
use std::sync::{Mutex, PoisonError};
use std::thread::{self, JoinHandle};

use futures_channel::oneshot;

use crate::{
    CanId, Check, Client, ClientBuilder, Dbc, DbcMessage, Dlc, Error, ExtractionResult, Formula,
    Frame, FrameResponse, SignalValue, StreamResult, Timestamp, ValidationIssue, ValidationResult,
};

/// A unit of work run on the worker thread against the owned sync [`Client`].
type Job = Box<dyn FnOnce(&Client) + Send>;

/// A runtime-agnostic async mirror of [`Client`]; see the module docs.
pub struct AsyncClient {
    /// The job channel, wrapped in a `Mutex` so `AsyncClient` is `Sync` (the std
    /// `mpsc::Sender` is `Send` but `!Sync`). The lock is held only for the brief
    /// enqueue, never across an `.await`. `None` only transiently during
    /// [`Drop`] — taking it closes the channel.
    jobs: Mutex<Option<Sender<Job>>>,
    /// Joined on [`Drop`]. `JoinHandle` is already `Send + Sync`, so — unlike the
    /// sender — it needs no wrapper.
    worker: Option<JoinHandle<()>>,
}

/// Spawn the worker thread (which builds and owns the sync `Client`) and return
/// the handle once the worker reports a successful init.
pub(crate) async fn spawn(builder: ClientBuilder) -> Result<AsyncClient, Error> {
    let (jobs_tx, jobs_rx) = mpsc::channel::<Job>();
    let (init_tx, init_rx) = oneshot::channel::<Result<(), Error>>();
    let worker = thread::spawn(move || {
        // Build the sync Client ON this thread — it is `!Send` + thread-pinned.
        let client = match builder.build() {
            Ok(c) => {
                if init_tx.send(Ok(())).is_err() {
                    return; // creator dropped before we reported success
                }
                c
            }
            Err(e) => {
                let _ = init_tx.send(Err(e));
                return;
            }
        };
        // Run jobs until the channel closes (AsyncClient dropped). The Client
        // then drops here, so `aletheia_close` runs on this same thread.
        while let Ok(job) = jobs_rx.recv() {
            job(&client);
        }
    });
    match init_rx.await {
        Ok(Ok(())) => Ok(AsyncClient {
            jobs: Mutex::new(Some(jobs_tx)),
            worker: Some(worker),
        }),
        Ok(Err(e)) => {
            let _ = worker.join();
            Err(e)
        }
        // The worker panicked before reporting — surface a generic init failure.
        Err(_) => {
            let _ = worker.join();
            Err(Error::InitFailed)
        }
    }
}

impl AsyncClient {
    /// Build an async client with no logger and the default RTS — the async
    /// analogue of [`Client::new`]. Use [`ClientBuilder::build_async`] to
    /// configure a logger or the RTS core count.
    ///
    /// # Errors
    /// As [`ClientBuilder::build`], propagated from the worker thread.
    pub async fn new() -> Result<Self, Error> {
        ClientBuilder::default().build_async().await
    }

    /// Run `f` on the worker's `Client` and await its result. Dropping the
    /// returned future cancels the call (see the module docs).
    async fn run<T: Send + 'static>(
        &self,
        f: impl FnOnce(&Client) -> Result<T, Error> + Send + 'static,
    ) -> Result<T, Error> {
        let (tx, rx) = oneshot::channel();
        let job: Job = Box::new(move |c: &Client| {
            // Honor cancellation of a still-queued job: if the caller already
            // dropped the future, the receiver is gone — skip the FFI call.
            if tx.is_canceled() {
                return;
            }
            let _ = tx.send(f(c));
        });
        // Hold the lock only to enqueue — release it before awaiting the reply.
        {
            let guard = self.jobs.lock().unwrap_or_else(PoisonError::into_inner);
            let sender = guard
                .as_ref()
                .ok_or_else(|| Error::Protocol("async client closed".to_string()))?;
            sender
                .send(job)
                .map_err(|_| Error::Protocol("async worker stopped".to_string()))?;
        }
        rx.await
            .map_err(|_| Error::Protocol("async worker stopped".to_string()))?
    }

    // ── Async mirror of the Client surface ──────────────────────────────────
    // Each forwards to the sync method on the worker. Arguments are owned (not
    // borrowed): the closure crosses to the worker thread, so it cannot hold a
    // borrow of the caller's data.

    /// Async [`Client::parse_dbc_text`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn parse_dbc_text(&self, text: String) -> Result<(Dbc, Vec<ValidationIssue>), Error> {
        self.run(move |c| c.parse_dbc_text(&text)).await
    }

    /// Async [`Client::parse_dbc`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn parse_dbc(&self, dbc: Dbc) -> Result<(Dbc, Vec<ValidationIssue>), Error> {
        self.run(move |c| c.parse_dbc(&dbc)).await
    }

    /// Async [`Client::validate_dbc`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn validate_dbc(&self, dbc: Dbc) -> Result<ValidationResult, Error> {
        self.run(move |c| c.validate_dbc(&dbc)).await
    }

    /// Async [`Client::format_dbc`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn format_dbc(&self) -> Result<Dbc, Error> {
        self.run(Client::format_dbc).await
    }

    /// Async [`Client::format_dbc_text`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn format_dbc_text(&self, dbc: Dbc) -> Result<String, Error> {
        self.run(move |c| c.format_dbc_text(&dbc)).await
    }

    /// Async [`Client::set_properties`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn set_properties(&self, properties: Vec<Formula>) -> Result<(), Error> {
        self.run(move |c| c.set_properties(&properties)).await
    }

    /// Async [`Client::add_checks`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn add_checks(&self, checks: Vec<Check>) -> Result<(), Error> {
        self.run(move |c| c.add_checks(&checks)).await
    }

    /// Async [`Client::start_stream`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn start_stream(&self) -> Result<(), Error> {
        self.run(Client::start_stream).await
    }

    /// Async [`Client::send_frame`]. Cancellable at the frame boundary.
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn send_frame(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: Vec<u8>,
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<FrameResponse, Error> {
        self.run(move |c| c.send_frame(ts, id, dlc, &data, brs, esi))
            .await
    }

    /// Async [`Client::send_error`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn send_error(&self, ts: Timestamp) -> Result<(), Error> {
        self.run(move |c| c.send_error(ts)).await
    }

    /// Async [`Client::send_remote`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn send_remote(&self, ts: Timestamp, id: CanId) -> Result<(), Error> {
        self.run(move |c| c.send_remote(ts, id)).await
    }

    /// Async [`Client::end_stream`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn end_stream(&self) -> Result<StreamResult, Error> {
        self.run(Client::end_stream).await
    }

    /// Async [`Client::extract_signals`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn extract_signals(
        &self,
        id: CanId,
        dlc: Dlc,
        data: Vec<u8>,
    ) -> Result<ExtractionResult, Error> {
        self.run(move |c| c.extract_signals(id, dlc, &data)).await
    }

    /// Async [`Client::build_frame`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn build_frame(
        &self,
        message: DbcMessage,
        dlc: Dlc,
        signals: Vec<SignalValue>,
    ) -> Result<Vec<u8>, Error> {
        self.run(move |c| c.build_frame(&message, dlc, &signals))
            .await
    }

    /// Async [`Client::update_frame`].
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn update_frame(
        &self,
        message: DbcMessage,
        dlc: Dlc,
        frame: Vec<u8>,
        signals: Vec<SignalValue>,
    ) -> Result<Vec<u8>, Error> {
        self.run(move |c| c.update_frame(&message, dlc, &frame, &signals))
            .await
    }

    /// Async [`Client::send_frames`]. The inner tuple is the batch result
    /// (responses + first transport error); the outer `Result` reports a
    /// closed/stopped async worker.
    ///
    /// **Cancellable at the frame boundary.** Each frame is dispatched as its own
    /// job (not one atomic batch), so dropping this future stops the batch at the
    /// next boundary — committing only a *prefix*, never all N frames (honoring
    /// the commit-prefix contract; see `docs/architecture/CANCELLATION.md`). A
    /// dropped future returns nothing, so to *observe* the committed prefix on
    /// cancellation, loop [`AsyncClient::send_frame`] yourself and keep each
    /// result. Per-frame dispatch also means another task's job on the same
    /// `AsyncClient` may interleave between this batch's frames (a single stream
    /// is sequential, so concurrent streaming on one client is already a misuse).
    ///
    /// # Errors
    /// A closed/stopped async worker.
    pub async fn send_frames(
        &self,
        frames: Vec<Frame>,
    ) -> Result<(Vec<FrameResponse>, Option<Error>), Error> {
        let mut out = Vec::with_capacity(frames.len());
        for f in frames {
            // One cancellable job per frame: the inner `Result` is the transport
            // outcome (first error stops the batch, mirroring the sync method);
            // an outer `Err` is a closed/stopped worker.
            match self
                .run(move |c| Ok(c.send_frame(f.timestamp, f.id, f.dlc, &f.data, f.brs, f.esi)))
                .await
            {
                Ok(Ok(resp)) => out.push(resp),
                Ok(Err(transport)) => return Ok((out, Some(transport))),
                Err(worker) => return Err(worker),
            }
        }
        Ok((out, None))
    }

    /// Async [`Client::process`] — the raw JSON escape hatch.
    ///
    /// # Errors
    /// As the sync method, plus a closed/stopped async worker.
    pub async fn process(&self, command: String) -> Result<String, Error> {
        self.run(move |c| c.process(&command)).await
    }
}

impl Drop for AsyncClient {
    fn drop(&mut self) {
        // Close the channel FIRST (so the worker's recv() returns and it drops
        // the Client → aletheia_close on its own thread), THEN join — joining
        // before dropping the sender would deadlock on the still-blocked recv().
        // We hold `&mut self`, so `get_mut()` needs no real locking; recover from
        // a poisoned lock rather than double-panicking during unwind.
        drop(
            self.jobs
                .get_mut()
                .unwrap_or_else(PoisonError::into_inner)
                .take(),
        );
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use futures_channel::oneshot;

    #[test]
    fn async_client_is_send_and_sync() {
        // The worker-thread design promises AsyncClient is Send + Sync, so
        // &AsyncClient is Send and the futures from its async methods (which
        // borrow &self across .await) are Send — i.e. spawnable on a multi-thread
        // executor like tokio::spawn. The std mpsc::Sender is !Sync, which is why
        // `jobs` is Mutex-wrapped; this compile-time check guards the invariant.
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}
        is_send::<super::AsyncClient>();
        is_sync::<super::AsyncClient>();
    }

    #[test]
    fn method_futures_are_send() {
        // The handle being Send + Sync does NOT imply the borrowing method
        // futures are Send (a future capturing &self + a !Send local would be
        // !Send while the handle stays Send). The documented `tokio::spawn`
        // guarantee is specifically about the *futures*, so pin that directly: if
        // any method future stops being Send, `check`'s body fails to compile.
        fn assert_send<F: core::future::Future + Send>(_: F) {}
        fn check(c: &super::AsyncClient) {
            assert_send(c.start_stream());
            assert_send(c.send_frame(
                super::Timestamp(0),
                super::CanId::standard(0).expect("0 is a valid standard id"),
                super::Dlc::new(0).expect("0 is a valid dlc"),
                Vec::new(),
                None,
                None,
            ));
            assert_send(c.send_frames(Vec::new()));
        }
        // Reference (don't call) `check` so it is type-checked — proving the
        // assertions above — without constructing an AsyncClient (no `.so`).
        let _ = check as fn(&super::AsyncClient);
    }

    #[test]
    fn dropped_receiver_cancels_sender() {
        // The queued-job self-guard skips the FFI call when the reply receiver
        // was dropped (the method future cancelled). It relies on the worker
        // seeing `Sender::is_canceled()` — lock that invariant here.
        let (tx, rx) = oneshot::channel::<i32>();
        assert!(!tx.is_canceled());
        drop(rx);
        assert!(
            tx.is_canceled(),
            "dropping the receiver must cancel the sender — the queued-skip guard"
        );
    }
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A test [`Backend`] that records requests and replays canned responses.
//!
//! [`MockBackend`] lets a unit test drive a [`Client`](crate::Client) without
//! loading `libaletheia-ffi.so`: queue the responses the core would return, run
//! the client, then assert on the requests the client issued. It is the Rust
//! analogue of the Go / Python `MockBackend` (a public, configurable,
//! inspectable mock) and the C++ test-internal `MockBackend`.
//!
//! # Inspecting the mock after injection
//!
//! A [`Client`](crate::Client) takes ownership of its `Box<dyn Backend>`, so the
//! mock would be unreachable once injected. [`MockBackend`] solves this the
//! idiomatic-Rust way: it wraps shared interior-mutable state ([`Rc`] +
//! [`RefCell`]) and is [`Clone`], so the test keeps one clone to assert on while
//! the [`Client`](crate::Client) owns another — both observe the same queue and
//! capture log. This is Rust's equivalent of the peer bindings keeping a pointer
//! to the injected mock.
//!
//! # Binary-path fidelity
//!
//! The binary fast-path operations do not have a JSON wire shape the production
//! backend ever emits, so the mock records a `<binary:OP>` sentinel for each
//! (e.g. `<binary:sendFrame>`) rather than fabricating a JSON command — matching
//! the cross-binding mock-fidelity convention (the exact sentinel strings are
//! shared with the Go / Python / C++ mocks).
//!
//! # Responses
//!
//! This mock **errors** on exhaustion rather than synthesising a default
//! response — the no-surprise contract now shared by all four bindings'
//! `MockBackend`s (an under-provisioned test fails loudly at the missing
//! response). A test queues exactly the responses it expects, including the
//! `extract_signals_binary` calls the client makes during violation enrichment.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

use crate::backend::{Backend, SignalInjection};
use crate::{CanId, Dlc, Error, Timestamp};

/// One queued response: a JSON body (for the JSON-returning ops), a raw payload
/// (for `build_frame_bin` / `update_frame_bin`), or an error to surface.
enum MockResponse {
    Json(String),
    Bytes(Vec<u8>),
    Err(Error),
}

#[derive(Default)]
struct MockState {
    /// Responses to replay, in order.
    responses: VecDeque<MockResponse>,
    /// Every request the client issued — a JSON command for `process`, or a
    /// `<binary:OP>` sentinel for the binary-path ops.
    captured: Vec<String>,
}

/// A configurable, inspectable test [`Backend`]. See the module docs.
///
/// `Clone` shares the same underlying queue and capture log (interior
/// mutability), so a test can clone the mock before injecting it into a
/// [`Client`](crate::Client) and still observe what the client did.
#[derive(Clone, Default)]
pub struct MockBackend {
    state: Rc<RefCell<MockState>>,
}

impl MockBackend {
    /// Create an empty mock — no queued responses, nothing captured.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Queue a JSON response body (returned by the next JSON-returning op).
    pub fn respond_json(&self, json: impl Into<String>) -> &Self {
        self.state
            .borrow_mut()
            .responses
            .push_back(MockResponse::Json(json.into()));
        self
    }

    /// Queue a raw payload (returned by the next `build_frame_bin` /
    /// `update_frame_bin`).
    pub fn respond_bytes(&self, bytes: Vec<u8>) -> &Self {
        self.state
            .borrow_mut()
            .responses
            .push_back(MockResponse::Bytes(bytes));
        self
    }

    /// Queue an [`Error`] for the next operation to return.
    pub fn respond_err(&self, err: Error) -> &Self {
        self.state
            .borrow_mut()
            .responses
            .push_back(MockResponse::Err(err));
        self
    }

    /// The requests the client has issued so far (JSON commands and
    /// `<binary:OP>` sentinels), in order. Returns an owned copy.
    #[must_use]
    pub fn captured(&self) -> Vec<String> {
        self.state.borrow().captured.clone()
    }

    /// Clear both the queued responses and the capture log.
    pub fn clear(&self) {
        let mut s = self.state.borrow_mut();
        s.responses.clear();
        s.captured.clear();
    }

    /// Record one request (a JSON command or a `<binary:OP>` sentinel).
    fn record(&self, input: &str) {
        self.state.borrow_mut().captured.push(input.to_string());
    }

    /// Pop the next response, requiring it be a JSON body.
    ///
    /// On exhaustion this returns [`Error::Protocol`] rather than a dedicated
    /// state-error variant: `Error` has no `State` kind, and Rust already
    /// reports every wrong-lifecycle condition as `Protocol` (e.g. the async
    /// client's "closed" / "worker stopped"). So `Protocol` is this binding's
    /// wrong-state category — the peers' `State` kind (Go / C++ / Python) maps
    /// onto it. Only the message text is unified across bindings (#108).
    fn pop_json(&self, op: &str) -> Result<String, Error> {
        match self.state.borrow_mut().responses.pop_front() {
            Some(MockResponse::Json(s)) => Ok(s),
            Some(MockResponse::Bytes(_)) => Err(Error::Protocol(format!(
                "mock backend: {op} expected a JSON response but a bytes response was queued"
            ))),
            Some(MockResponse::Err(e)) => Err(e),
            None => Err(Error::Protocol(format!(
                "mock backend: no queued response for {op}"
            ))),
        }
    }

    /// Pop the next response, requiring it be a raw payload.
    fn pop_bytes(&self, op: &str) -> Result<Vec<u8>, Error> {
        match self.state.borrow_mut().responses.pop_front() {
            Some(MockResponse::Bytes(b)) => Ok(b),
            Some(MockResponse::Json(_)) => Err(Error::Protocol(format!(
                "mock backend: {op} expected a bytes response but a JSON response was queued"
            ))),
            Some(MockResponse::Err(e)) => Err(e),
            None => Err(Error::Protocol(format!(
                "mock backend: no queued response for {op}"
            ))),
        }
    }
}

impl Backend for MockBackend {
    fn process(&self, input: &str) -> Result<String, Error> {
        // Match FfiBackend's fidelity: an interior NUL cannot cross the C ABI, so
        // reject it before recording (FfiBackend errors at CString::new, before
        // any side effect) — a test driving the mock directly then sees the same
        // error the real backend would raise.
        if input.contains('\0') {
            return Err(Error::NulInString);
        }
        self.record(input);
        self.pop_json("process")
    }

    fn send_frame_binary(
        &self,
        _ts: Timestamp,
        _id: CanId,
        _dlc: Dlc,
        _data: &[u8],
        _brs: Option<bool>,
        _esi: Option<bool>,
    ) -> Result<String, Error> {
        self.record("<binary:sendFrame>");
        self.pop_json("<binary:sendFrame>")
    }

    fn send_error_binary(&self, _ts: Timestamp) -> Result<String, Error> {
        self.record("<binary:sendError>");
        self.pop_json("<binary:sendError>")
    }

    fn send_remote_binary(&self, _ts: Timestamp, _id: CanId) -> Result<String, Error> {
        self.record("<binary:sendRemote>");
        self.pop_json("<binary:sendRemote>")
    }

    fn start_stream_binary(&self) -> Result<String, Error> {
        self.record("<binary:startStream>");
        self.pop_json("<binary:startStream>")
    }

    fn end_stream_binary(&self) -> Result<String, Error> {
        self.record("<binary:endStream>");
        self.pop_json("<binary:endStream>")
    }

    fn format_dbc_binary(&self) -> Result<String, Error> {
        self.record("<binary:formatDBC>");
        self.pop_json("<binary:formatDBC>")
    }

    fn extract_signals_binary(&self, _id: CanId, _dlc: Dlc, _data: &[u8]) -> Result<String, Error> {
        self.record("<binary:extractAllSignals>");
        self.pop_json("<binary:extractAllSignals>")
    }

    fn build_frame_bin(
        &self,
        _id: u32,
        _extended: bool,
        _dlc: Dlc,
        _signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        self.record("<binary:buildFrameBin>");
        self.pop_bytes("<binary:buildFrameBin>")
    }

    fn update_frame_bin(
        &self,
        _id: u32,
        _extended: bool,
        _dlc: Dlc,
        _frame: &[u8],
        _signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        self.record("<binary:updateFrameBin>");
        self.pop_bytes("<binary:updateFrameBin>")
    }
}

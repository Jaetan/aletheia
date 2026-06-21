// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Rust binding for Aletheia — formally verified CAN frame analysis.
//!
//! Like the Go and C++ bindings, this crate loads the GHC-compiled Agda core
//! `libaletheia-ffi.so` at runtime via `dlopen` (the `libloading` crate) rather
//! than statically linking the GHC RTS + MAlonzo into a non-Haskell binary. The
//! verified logic lives entirely in the shared library; this crate is a thin,
//! memory-safe, *typed* wrapper over its stable C ABI.
//!
//! # Surface
//! - **Typed values** ([`CanId`], [`Dlc`], [`Rational`], [`Timestamp`],
//!   [`TimeBound`]) that validate on construction.
//! - **LTL** ([`Predicate`], [`Formula`]) as native, sealed Rust enums.
//! - A [`Client`] over one stream: load the DBC ([`Client::parse_dbc_text`]),
//!   bind properties ([`Client::set_properties`]), then stream frames through the
//!   **binary FFI** ([`Client::start_stream`], [`Client::send_frame`],
//!   [`Client::end_stream`]) — the same fast path the other bindings use in
//!   production. [`Client::process`] remains as a raw JSON escape hatch.
//! - A [`Backend`] dependency-injection seam ([`Client::with_backend`] /
//!   [`ClientBuilder::build_with_backend`]): the [`Client`] is built over a
//!   production FFI backend by default, or a test [`MockBackend`] (or any custom
//!   double) for unit-testing the client without loading the `.so`.
//!
//! Frame streaming uses the binary FFI (`aletheia_send_frame`, …), *not* the
//! JSON command path — that mirrors every other binding and the core's intended
//! hot path. The typed DBC document model, the Check DSL, and CLI affordances
//! are tracked as `planned` in `docs/FEATURE_MATRIX.yaml`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::enrich::PropertyDiagnostic;
use crate::log::events;

use serde_json::json;

#[cfg(feature = "async")]
mod async_client;
mod backend;
pub mod check;
mod dbc;
mod enrich;
mod error;
pub mod log;
mod ltl;
mod mock;
mod response;
mod types;
#[cfg(feature = "yaml")]
pub mod yaml;

#[cfg(feature = "async")]
pub use async_client::AsyncClient;
use backend::FfiBackend;
pub use backend::{Backend, SignalInjection};
pub use check::Check;
pub use dbc::{
    AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment, CommentTarget, Dbc,
    DbcMessage, DbcSignal, EnvironmentVar, Node, Presence, SignalGroup, ValueDescription,
    ValueTable,
};
pub use error::Error;
pub use log::{LogField, LogLevel, LogRecord, LogValue, Logger};
pub use ltl::{Formula, Predicate, MAX_FORMULA_DEPTH};
pub use mock::MockBackend;
pub use response::{
    Enrichment, ExtractionResult, FrameResponse, IssueCode, IssueSeverity, PropertyResult,
    SignalError, SignalValue, StreamResult, StreamWarning, ValidationIssue, ValidationResult,
    Verdict,
};
pub use types::{CanId, Dlc, Rational, TimeBound, Timestamp, MAX_EXTENDED_ID, MAX_STANDARD_ID};
#[cfg(feature = "yaml")]
pub use yaml::{load_checks_from_yaml, load_checks_from_yaml_file};

/// Require a payload's length to match its declared DLC exactly — the CAN
/// invariant every data-bearing op enforces (mirrors Go `validatePayload`).
fn validate_frame_len(dlc: Dlc, data: &[u8]) -> Result<(), Error> {
    let expected = dlc.to_bytes();
    if data.len() != expected {
        return Err(Error::Validation(format!(
            "payload length {} does not match DLC ({expected} bytes expected)",
            data.len()
        )));
    }
    Ok(())
}

/// One frame for batch submission via [`Client::send_frames`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frame {
    /// Timestamp (µs since stream start).
    pub timestamp: Timestamp,
    /// CAN identifier.
    pub id: CanId,
    /// Declared data length.
    pub dlc: Dlc,
    /// Payload bytes.
    pub data: Vec<u8>,
    /// CAN-FD bit-rate-switch bit (`None` ⇒ CAN 2.0B).
    pub brs: Option<bool>,
    /// CAN-FD error-state-indicator bit.
    pub esi: Option<bool>,
}

/// The parallel `(indices, numerators, denominators)` arrays the build/update
/// FFI expects for a set of signal injections.
type SignalArrays = (Vec<u32>, Vec<i64>, Vec<i64>);

/// Resolve `(name, value)` signal injections against a message's signal list to
/// the parallel arrays the build/update FFI expects. The index is the signal's
/// position in `message.signals`.
fn resolve_signal_indices(
    message: &DbcMessage,
    signals: &[SignalValue],
) -> Result<SignalArrays, Error> {
    let mut indices = Vec::with_capacity(signals.len());
    let mut nums = Vec::with_capacity(signals.len());
    let mut dens = Vec::with_capacity(signals.len());
    for sv in signals {
        let pos = message
            .signals
            .iter()
            .position(|s| s.name == sv.name)
            .ok_or_else(|| {
                Error::Validation(format!(
                    "unknown signal {:?} for message {:?}",
                    sv.name, message.name
                ))
            })?;
        indices.push(
            u32::try_from(pos)
                .map_err(|_| Error::Validation(format!("signal index {pos} out of range")))?,
        );
        nums.push(sv.value.numerator());
        dens.push(sv.value.denominator());
    }
    Ok((indices, nums, dens))
}

/// A client over one `StreamState` in the verified core.
///
/// Delegates every raw FFI operation to a [`Backend`] (the production
/// `FfiBackend` by default, or an injected double); keeps the typed concerns —
/// validation, response decoding, violation enrichment, logging — on this side.
/// The default backend owns a thread-pinned GHC `StreamState`, so it is `!Send`,
/// which makes `Client` `!Send + !Sync` too (cross-thread use is a future slice,
/// tracked `planned`; for async use, see [`AsyncClient`]).
pub struct Client {
    /// The FFI-boundary backend every raw operation is routed through.
    backend: Box<dyn Backend>,
    /// Optional structured-log sink (`None` ⇒ logging is a no-op). Held as an
    /// `Arc` so a future async client's worker thread can share it.
    logger: Option<Arc<dyn Logger>>,
    /// Minimum level a record must meet to reach the logger.
    min_level: LogLevel,
    /// Per-property diagnostics derived from the registered formulas (index =
    /// `property_index`); the source for client-side violation enrichment.
    /// `RefCell` because the client methods take `&self`.
    diags: RefCell<Vec<PropertyDiagnostic>>,
    /// The most recent frame seen per CAN id during streaming (when diagnostics
    /// are set) — re-extracted at end-of-stream to enrich the final verdicts.
    last_frames: RefCell<HashMap<CanId, (Dlc, Vec<u8>)>>,
    /// Makes the `!Send + !Sync` contract explicit and future-proof. A
    /// `Box<dyn Backend>` (no `Send` bound) is already `!Send + !Sync`, so this
    /// is not load-bearing today — but it keeps `Client` thread-bound even if a
    /// `Send`/`Sync` field is added later, rather than relying on the current
    /// field set.
    _not_send_sync: PhantomData<*const ()>,
}

/// Builder for a [`Client`] — a [`Logger`] sink and/or the GHC RTS core count.
///
/// The RTS is process-global and initialised once: the first client built
/// latches the core count; a later client requesting a different count gets the
/// first one plus a `rts.cores_mismatch` warning (mirrors Go `WithRTSCores` /
/// C++ `make_ffi_backend`).
#[derive(Default)]
pub struct ClientBuilder {
    rts_cores: Option<u32>,
    logger: Option<Arc<dyn Logger>>,
    min_level: Option<LogLevel>,
}

impl ClientBuilder {
    /// Request the GHC RTS core count (`+RTS -N<cores>`). Must be ≥ 1. Takes
    /// effect only on the first client built in the process.
    #[must_use]
    pub fn rts_cores(mut self, cores: u32) -> Self {
        self.rts_cores = Some(cores);
        self
    }

    /// Set the structured-log sink. A bare `Fn(&LogRecord) + Send + Sync` works
    /// as a [`Logger`] via the blanket impl.
    #[must_use]
    pub fn logger(mut self, logger: impl Logger + 'static) -> Self {
        self.logger = Some(Arc::new(logger));
        self
    }

    /// Set the minimum level a record must meet to reach the logger (default
    /// [`LogLevel::Debug`] — everything passes).
    #[must_use]
    pub fn min_level(mut self, level: LogLevel) -> Self {
        self.min_level = Some(level);
        self
    }

    /// Build the client: load the core, initialise the RTS once per process, and
    /// allocate a fresh `StreamState` (a production `FfiBackend`).
    ///
    /// # Errors
    /// [`Error::Validation`] if `rts_cores` is 0 or exceeds the C `int` range;
    /// otherwise [`Error`] if the library cannot be loaded, a required symbol is
    /// missing, or the core fails to initialise.
    pub fn build(self) -> Result<Client, Error> {
        if let Some(k) = self.rts_cores {
            if k == 0 || k > i32::MAX as u32 {
                return Err(Error::Validation(format!(
                    "rts_cores must be in 1..={}, got {k}",
                    i32::MAX
                )));
            }
        }
        let min_level = self.min_level.unwrap_or(LogLevel::Debug);
        let backend = FfiBackend::new(self.rts_cores, self.logger.as_deref(), min_level)?;
        Ok(Client::from_parts(
            Box::new(backend),
            self.logger,
            min_level,
        ))
    }

    /// Build a [`Client`] over an injected [`Backend`] (e.g. a [`MockBackend`]
    /// or a custom test double), applying this builder's logger / minimum level.
    ///
    /// Skips the FFI entirely: no library is loaded and the GHC RTS is not
    /// initialised, so `rts_cores` (if set) is ignored. Infallible — there is no
    /// `.so` to fail to load.
    #[must_use]
    pub fn build_with_backend(self, backend: Box<dyn Backend>) -> Client {
        let min_level = self.min_level.unwrap_or(LogLevel::Debug);
        Client::from_parts(backend, self.logger, min_level)
    }

    /// Build a runtime-agnostic [`AsyncClient`] from this configuration (feature
    /// `async`) — the async analogue of [`ClientBuilder::build`]. The sync
    /// `Client` is created and owned on a dedicated worker thread.
    ///
    /// # Errors
    /// As [`ClientBuilder::build`], propagated from the worker thread.
    #[cfg(feature = "async")]
    pub async fn build_async(self) -> Result<AsyncClient, Error> {
        async_client::spawn(self).await
    }
}

impl Client {
    /// Load the core, initialise the GHC RTS, and allocate a fresh `StreamState`
    /// — with no logger and no explicit RTS core count.
    ///
    /// The RTS is **process-global and initialised once**: `new()` requests GHC
    /// default flags, but if an earlier client was built with
    /// [`ClientBuilder::rts_cores`], that first `-N<k>` stays in effect — `new()`
    /// does not (and cannot) reset the process-wide RTS. Use [`Client::builder`]
    /// to configure a [`Logger`] or the RTS core count.
    ///
    /// # Errors
    /// Returns [`Error`] if the library cannot be loaded, a required symbol is
    /// missing, or the core fails to initialise.
    pub fn new() -> Result<Self, Error> {
        Client::builder().build()
    }

    /// Begin configuring a client (a [`Logger`] sink and/or the RTS core count).
    #[must_use]
    pub fn builder() -> ClientBuilder {
        ClientBuilder::default()
    }

    /// Construct a [`Client`] over an injected [`Backend`] with no logger — the
    /// terse form of [`ClientBuilder::build_with_backend`] for test substitution
    /// (mirrors Go `NewClient(backend)` / C++ `AletheiaClient(backend)`).
    #[must_use]
    pub fn with_backend(backend: Box<dyn Backend>) -> Self {
        Self::from_parts(backend, None, LogLevel::Debug)
    }

    /// Assemble a client from its parts. The single construction point shared by
    /// the FFI path ([`ClientBuilder::build`]) and the injection path
    /// ([`Client::with_backend`] / [`ClientBuilder::build_with_backend`]).
    fn from_parts(
        backend: Box<dyn Backend>,
        logger: Option<Arc<dyn Logger>>,
        min_level: LogLevel,
    ) -> Self {
        Client {
            backend,
            logger,
            min_level,
            diags: RefCell::new(Vec::new()),
            last_frames: RefCell::new(HashMap::new()),
            _not_send_sync: PhantomData,
        }
    }

    /// Emit a structured log record, if a logger is set and the level passes the
    /// configured minimum. A no-op (one branch) when no logger is configured.
    fn emit(&self, level: LogLevel, event: &str, fields: &[LogField]) {
        if let Some(lg) = &self.logger {
            if level >= self.min_level {
                lg.log(&LogRecord {
                    level,
                    event,
                    fields,
                });
            }
        }
    }

    /// Extract every signal value from one frame, or `None` if the extraction
    /// FFI call failed. Called once per distinct frame — callers filter per
    /// diagnostic — so a frame deciding several violations is extracted once.
    fn extract_all(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Option<Vec<(String, Rational)>> {
        let res = self.extract_signals(id, dlc, data).ok()?;
        Some(
            res.values
                .into_iter()
                .map(|sv| (sv.name, sv.value))
                .collect(),
        )
    }

    /// Collect the `(result-slot, diagnostic)` pairs needing enrichment — the
    /// results whose verdict is in `verdicts` with an in-range `property_index`.
    /// Out-of-range indices emit `enrichment.property_index_oob` and are skipped.
    /// The `diags` borrow is released before the caller extracts (avoids a
    /// re-entrant borrow). Streaming enriches `Fails`; end-of-stream also
    /// enriches `Unresolved` (matching the Go / Python bindings).
    fn enrichment_todo(
        &self,
        results: &[PropertyResult],
        verdicts: &[Verdict],
    ) -> Vec<(usize, PropertyDiagnostic)> {
        let n = self.diags.borrow().len();
        let mut todo = Vec::new();
        for (slot, r) in results.iter().enumerate() {
            if !verdicts.contains(&r.verdict) {
                continue;
            }
            let idx = r.property_index as usize;
            if idx >= n {
                self.emit(
                    LogLevel::Warn,
                    events::ENRICHMENT_PROPERTY_INDEX_OOB,
                    &[
                        LogField::new("property_index", LogValue::U64(u64::from(r.property_index))),
                        LogField::new("count", LogValue::U64(n as u64)),
                    ],
                );
                continue;
            }
            todo.push((slot, self.diags.borrow()[idx].clone()));
        }
        todo
    }

    /// Attach a [`Enrichment`] built from `diag` + extracted `values` to one result.
    fn set_enrichment(
        &self,
        pr: &mut PropertyResult,
        diag: &PropertyDiagnostic,
        values: Vec<(String, Rational)>,
    ) {
        let enriched_reason = enrich::format_enriched_reason(diag, &values, &pr.reason);
        pr.enrichment = Some(Enrichment {
            signals: values,
            formula_desc: diag.formula_desc.clone(),
            enriched_reason,
            core_reason: pr.reason.clone(),
        });
    }

    /// The diagnostic's signal values from an already-extracted frame's values.
    /// A `None` extraction means the FFI call failed: emit
    /// `enrichment.extraction_failed` for `prop_index` and yield no values.
    fn diag_values(
        &self,
        diag: &PropertyDiagnostic,
        extracted: Option<&[(String, Rational)]>,
        prop_index: u32,
    ) -> Vec<(String, Rational)> {
        match extracted {
            Some(all) => all
                .iter()
                .filter(|(n, _)| diag.signals.iter().any(|s| s == n))
                .cloned()
                .collect(),
            None => {
                self.emit(
                    LogLevel::Warn,
                    events::ENRICHMENT_EXTRACTION_FAILED,
                    &[LogField::new(
                        "property_index",
                        LogValue::U64(u64::from(prop_index)),
                    )],
                );
                Vec::new()
            }
        }
    }

    /// Enrich the `Fails` verdicts decided by the current frame. The frame is
    /// extracted once and its values reused across every violation it decided.
    fn enrich_streaming(&self, results: &mut [PropertyResult], id: CanId, dlc: Dlc, data: &[u8]) {
        let todo = self.enrichment_todo(results, &[Verdict::Fails]);
        if todo.is_empty() {
            return;
        }
        let extracted = self.extract_all(id, dlc, data);
        for (slot, diag) in todo {
            let pidx = results[slot].property_index;
            let values = self.diag_values(&diag, extracted.as_deref(), pidx);
            self.set_enrichment(&mut results[slot], &diag, values);
        }
    }

    /// Enrich the final `Fails` verdicts at end-of-stream from the last frame
    /// seen per CAN id. Each distinct frame is extracted once and its values
    /// merged (first-seen order), then reused across every violation.
    fn enrich_eos(&self, results: &mut [PropertyResult]) {
        if self.diags.borrow().is_empty() {
            return;
        }
        let todo = self.enrichment_todo(results, &[Verdict::Fails, Verdict::Unresolved]);
        if todo.is_empty() {
            return;
        }
        // Snapshot the last frames so no borrow is held across extraction. Sort
        // by (id value, extended) so the first-seen merge below is deterministic
        // regardless of `HashMap` iteration order — matching Go's `slices.Sort`
        // and Python's sort-by-(canID, extended) enrichment-ordering contract.
        let mut frames: Vec<(CanId, Dlc, Vec<u8>)> = self
            .last_frames
            .borrow()
            .iter()
            .map(|(id, (dlc, data))| (*id, *dlc, data.clone()))
            .collect();
        frames.sort_by_key(|(id, _, _)| (id.value(), id.is_extended()));
        let mut merged: Vec<(String, Rational)> = Vec::new();
        let mut any_failed = false;
        for (id, dlc, data) in &frames {
            match self.extract_all(*id, *dlc, data) {
                Some(found) => {
                    for (name, value) in found {
                        if !merged.iter().any(|(n, _)| n == &name) {
                            merged.push((name, value));
                        }
                    }
                }
                None => any_failed = true,
            }
        }
        for (slot, diag) in todo {
            let values: Vec<(String, Rational)> = merged
                .iter()
                .filter(|(n, _)| diag.signals.iter().any(|s| s == n))
                .cloned()
                .collect();
            // Wanted signals but got none, and an extraction failed → that
            // failure is why enrichment is missing the values.
            if values.is_empty() && !diag.signals.is_empty() && any_failed {
                self.emit(
                    LogLevel::Warn,
                    events::ENRICHMENT_EXTRACTION_FAILED,
                    &[LogField::new(
                        "property_index",
                        LogValue::U64(u64::from(results[slot].property_index)),
                    )],
                );
            }
            self.set_enrichment(&mut results[slot], &diag, values);
        }
    }

    /// Send one raw JSON command line to the core and return its raw JSON
    /// response. The low-level escape hatch beneath the typed methods.
    ///
    /// # Errors
    /// Returns [`Error`] if the command contains an interior NUL, a required
    /// symbol is missing, or the core returns a null response.
    pub fn process(&self, command: &str) -> Result<String, Error> {
        // The interior-NUL rejection is part of this public contract, not the
        // backend's: the FFI boundary cannot carry a NUL, so enforce it here so
        // it holds for every `Backend` (incl. a mock or custom double), not just
        // `FfiBackend`.
        if command.contains('\0') {
            return Err(Error::NulInString);
        }
        self.backend.process(command)
    }

    /// Parse a DBC database from its `.dbc` text image and load it into this
    /// stream, returning the typed [`Dbc`] document together with any validation
    /// warnings the core reported.
    ///
    /// # Errors
    /// [`Error::Core`] if the text fails to parse, or [`Error::Protocol`] on an
    /// unexpected response.
    pub fn parse_dbc_text(&self, text: &str) -> Result<(Dbc, Vec<ValidationIssue>), Error> {
        let cmd = json!({ "type": "command", "command": "parseDBCText", "text": text });
        let raw = self.process(&cmd.to_string())?;
        let (dbc, warnings) = dbc::decode_parsed_dbc(&raw)?;
        self.emit(
            LogLevel::Info,
            events::DBC_PARSED,
            &[LogField::new(
                "messages",
                LogValue::U64(dbc.messages.len() as u64),
            )],
        );
        Ok((dbc, warnings))
    }

    /// Export the currently-loaded DBC as a typed [`Dbc`] document (the core's
    /// canonical-JSON form). Call after a successful `parse_dbc_text` /
    /// `parse_dbc`.
    ///
    /// # Errors
    /// [`Error::Core`] if no DBC is loaded, or [`Error::Protocol`] on an
    /// unexpected response.
    pub fn format_dbc(&self) -> Result<Dbc, Error> {
        let raw = self.backend.format_dbc_binary()?;
        dbc::decode_format_dbc(&raw)
    }

    /// Load a typed [`Dbc`] document into this stream (the JSON path; the
    /// structural analogue of [`Client::parse_dbc_text`]). Returns the
    /// re-parsed document plus any validation warnings.
    ///
    /// # Errors
    /// [`Error::Core`] if the DBC fails validation, or [`Error::Protocol`] on an
    /// unexpected response.
    pub fn parse_dbc(&self, dbc: &Dbc) -> Result<(Dbc, Vec<ValidationIssue>), Error> {
        // Build the envelope then move the serialized DBC in: `json!({…: expr})`
        // deep-copies a `Value` operand (via `to_value(&expr)`), which would
        // double-allocate a large document.
        let mut cmd = json!({ "type": "command", "command": "parseDBC" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        let (parsed, warnings) = dbc::decode_parsed_dbc(&raw)?;
        self.emit(
            LogLevel::Info,
            events::DBC_PARSED,
            &[LogField::new(
                "messages",
                LogValue::U64(parsed.messages.len() as u64),
            )],
        );
        Ok((parsed, warnings))
    }

    /// Run the structural validator over a typed [`Dbc`] without modifying this
    /// stream's loaded state, returning every issue found.
    ///
    /// # Errors
    /// [`Error::Core`] / [`Error::Protocol`] on a core error or unexpected
    /// response.
    pub fn validate_dbc(&self, dbc: &Dbc) -> Result<ValidationResult, Error> {
        let mut cmd = json!({ "type": "command", "command": "validateDBC" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        response::decode_validation(&raw)
    }

    /// Render a typed [`Dbc`] back to `.dbc` file text via the verified Agda
    /// formatter (the inverse of [`Client::parse_dbc_text`] at the wire level).
    /// Does not modify this stream's loaded state.
    ///
    /// # Errors
    /// [`Error::Core`] if the document fails Agda-side parsing, or
    /// [`Error::Protocol`] on an unexpected response.
    pub fn format_dbc_text(&self, dbc: &Dbc) -> Result<String, Error> {
        let mut cmd = json!({ "type": "command", "command": "formatDBCText" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        response::decode_format_text(&raw)
    }

    /// Bind the LTL properties to monitor. Call after `parse_dbc_text`, before
    /// `start_stream`.
    ///
    /// # Errors
    /// [`Error::Validation`] if any formula is invalid (bad predicate / depth),
    /// or [`Error::Core`] if the core rejects the set (e.g. no DBC loaded).
    pub fn set_properties(&self, properties: &[Formula]) -> Result<(), Error> {
        let mut arr = Vec::with_capacity(properties.len());
        for f in properties {
            arr.push(f.to_value()?);
        }
        let cmd = json!({ "type": "command", "command": "setProperties", "properties": arr });
        let raw = self.process(&cmd.to_string())?;
        response::decode_ack_or_success(&raw)?;
        // Cache one diagnostic per property (index = property_index) for
        // client-side violation enrichment, and reset the per-stream frame cache.
        *self.diags.borrow_mut() = properties.iter().map(enrich::build_diagnostic).collect();
        self.last_frames.borrow_mut().clear();
        self.emit(
            LogLevel::Info,
            events::PROPERTIES_SET,
            &[LogField::new(
                "count",
                LogValue::U64(properties.len() as u64),
            )],
        );
        Ok(())
    }

    /// Bind a set of [`Check`]s built with the [`check`] DSL — the higher-level
    /// equivalent of [`Client::set_properties`] that takes named checks. Only
    /// each check's formula is sent to the core; the metadata (name / severity)
    /// stays on the [`Check`] for the caller's reporting.
    ///
    /// The verdict `property_index` returned during streaming is the position of
    /// the check in `checks` (so the caller can map a violation back to its
    /// [`Check`]). Unlike the stateful bindings, there is no constructor-level
    /// "default checks" set to merge — pass the full list here.
    ///
    /// # Errors
    /// [`Error::Validation`] if a formula is invalid, or [`Error::Core`] if the
    /// core rejects the set (e.g. no DBC loaded).
    pub fn add_checks(&self, checks: &[Check]) -> Result<(), Error> {
        let formulas: Vec<Formula> = checks.iter().map(|c| c.formula().clone()).collect();
        self.set_properties(&formulas)
    }

    /// Begin the monitoring stream (binary FFI).
    ///
    /// # Errors
    /// [`Error::Core`] if the core is not ready (e.g. no DBC), else [`Error`].
    pub fn start_stream(&self) -> Result<(), Error> {
        let raw = self.backend.start_stream_binary()?;
        response::decode_ack_or_success(&raw)?;
        // Scope enrichment's last-frame cache to this stream — otherwise a second
        // stream (without a fresh set_properties) could reuse the prior stream's
        // frames at end-of-stream.
        self.last_frames.borrow_mut().clear();
        self.emit(LogLevel::Info, events::STREAM_STARTED, &[]);
        Ok(())
    }

    /// Send one CAN frame to the active stream (binary FFI). Pass `None` for
    /// `brs`/`esi` on CAN 2.0B frames (the bits do not exist there).
    ///
    /// Returns [`FrameResponse::Ack`] when no property was decided by this frame,
    /// or [`FrameResponse::Verdicts`] (a `property_batch`) carrying the decided
    /// properties — violations include enrichment when diagnostics are loaded.
    ///
    /// # Errors
    /// [`Error::Validation`] if the payload exceeds the CAN-FD maximum, else
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn send_frame(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<FrameResponse, Error> {
        validate_frame_len(dlc, data)?;
        let raw = self
            .backend
            .send_frame_binary(ts, id, dlc, data, brs, esi)?;
        let mut resp = response::decode_frame(&raw)?;
        // When diagnostics are set: remember this frame for end-of-stream
        // enrichment, and enrich any violations it decided (from this frame).
        if !self.diags.borrow().is_empty() {
            self.last_frames
                .borrow_mut()
                .insert(id, (dlc, data.to_vec()));
            if let FrameResponse::Verdicts(results) = &mut resp {
                self.enrich_streaming(results, id, dlc, data);
            }
        }
        let class = match &resp {
            FrameResponse::Ack => "ack",
            FrameResponse::Verdicts(_) => "verdicts",
        };
        self.emit(
            LogLevel::Debug,
            events::FRAME_PROCESSED,
            &[LogField::new("response", LogValue::Str(class))],
        );
        Ok(resp)
    }

    /// Send a CAN error event (no ID, no payload) to the active stream.
    ///
    /// # Errors
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn send_error(&self, ts: Timestamp) -> Result<(), Error> {
        let raw = self.backend.send_error_binary(ts)?;
        response::decode_ack_or_success(&raw)?;
        self.emit(
            LogLevel::Debug,
            events::ERROR_EVENT_SENT,
            &[LogField::new("timestamp", LogValue::U64(ts.micros()))],
        );
        Ok(())
    }

    /// Send a CAN remote frame event (ID, no payload) to the active stream.
    ///
    /// # Errors
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn send_remote(&self, ts: Timestamp, id: CanId) -> Result<(), Error> {
        let raw = self.backend.send_remote_binary(ts, id)?;
        response::decode_ack_or_success(&raw)?;
        self.emit(
            LogLevel::Debug,
            events::REMOTE_EVENT_SENT,
            &[LogField::new("timestamp", LogValue::U64(ts.micros()))],
        );
        Ok(())
    }

    /// End the stream and collect the final per-property verdicts and warnings
    /// (binary FFI).
    ///
    /// # Errors
    /// [`Error::Core`] if no stream is active, else [`Error`].
    pub fn end_stream(&self) -> Result<StreamResult, Error> {
        let raw = self.backend.end_stream_binary()?;
        let mut result = response::decode_stream(&raw)?;
        // Enrich the final violations from the last frame seen on each CAN id.
        self.enrich_eos(&mut result.results);
        self.emit(
            LogLevel::Info,
            events::STREAM_ENDED,
            &[LogField::new(
                "results",
                LogValue::U64(result.results.len() as u64),
            )],
        );
        for w in &result.warnings {
            if w.kind == "uncached_atom" {
                self.emit(
                    LogLevel::Warn,
                    events::ENDSTREAM_UNCACHED_ATOM,
                    &[
                        LogField::new("property_index", LogValue::U64(u64::from(w.property_index))),
                        LogField::new("detail", LogValue::Str(&w.detail)),
                    ],
                );
            }
        }
        Ok(result)
    }

    /// Extract all signals defined for a frame's CAN ID from its payload
    /// (binary FFI), independent of streaming.
    ///
    /// # Errors
    /// [`Error::Validation`] if the payload exceeds the CAN-FD maximum, else
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn extract_signals(
        &self,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
    ) -> Result<ExtractionResult, Error> {
        validate_frame_len(dlc, data)?;
        let raw = self.backend.extract_signals_binary(id, dlc, data)?;
        response::decode_extraction(&raw)
    }

    /// Build a CAN frame payload from named signal values (zero-filled base).
    /// `message` **must come from a [`Dbc`] this client parsed**
    /// ([`Dbc::message_by_id`] on the result of `parse_dbc_text` / `parse_dbc`):
    /// signal injections are resolved to positional indices in `message.signals`,
    /// which the core matches against the DBC currently loaded in its state, so the
    /// two must be the same definition. Each [`SignalValue`] names a signal of that
    /// message and the exact value to encode. Does not need `start_stream`.
    ///
    /// # Errors
    /// [`Error::Validation`] if a signal name is not in `message` or there are more
    /// injections than `u32::MAX`; [`Error::Protocol`] if the core rejects a value
    /// (out of range / not representable at the signal's scale).
    pub fn build_frame(
        &self,
        message: &DbcMessage,
        dlc: Dlc,
        signals: &[SignalValue],
    ) -> Result<Vec<u8>, Error> {
        let (indices, nums, dens) = resolve_signal_indices(message, signals)?;
        self.backend.build_frame_bin(
            message.id,
            message.extended,
            dlc,
            SignalInjection {
                indices: &indices,
                nums: &nums,
                dens: &dens,
            },
        )
    }

    /// Update specific signals inside an existing frame payload, returning a new
    /// payload (the input is not mutated). See [`Client::build_frame`] for the
    /// `message` / `signals` contract.
    ///
    /// # Errors
    /// [`Error::Validation`] for an unknown signal, more than `u32::MAX`
    /// injections, or a `frame` whose length does not match `dlc`;
    /// [`Error::Protocol`] if the core rejects the update.
    pub fn update_frame(
        &self,
        message: &DbcMessage,
        dlc: Dlc,
        frame: &[u8],
        signals: &[SignalValue],
    ) -> Result<Vec<u8>, Error> {
        validate_frame_len(dlc, frame)?;
        let (indices, nums, dens) = resolve_signal_indices(message, signals)?;
        self.backend.update_frame_bin(
            message.id,
            message.extended,
            dlc,
            frame,
            SignalInjection {
                indices: &indices,
                nums: &nums,
                dens: &dens,
            },
        )
    }

    /// Send a batch of frames as a single call (a caller-side convenience over
    /// looping [`Client::send_frame`] — each frame is still one FFI call; there
    /// is no per-call lock to amortize as in the lock-guarded bindings). Returns
    /// the [`FrameResponse`]s for every frame processed, plus the first transport
    /// error if one stopped the batch early (`None` ⇒ all sent). Frames before a
    /// failure were processed and advanced the stream — the partial results carry
    /// their verdicts (the idiomatic-Rust analogue of the other bindings'
    /// `(results, error)` batch send). Each frame is validated like `send_frame`
    /// (payload length must match its DLC).
    #[must_use]
    pub fn send_frames(&self, frames: &[Frame]) -> (Vec<FrameResponse>, Option<Error>) {
        let mut out = Vec::with_capacity(frames.len());
        for (i, f) in frames.iter().enumerate() {
            match self.send_frame(f.timestamp, f.id, f.dlc, &f.data, f.brs, f.esi) {
                Ok(resp) => out.push(resp),
                // Tag the error with the failing frame's index so the caller can
                // locate it (mirrors Go's / C++'s "frame N: …"; see [`Error::Frame`]).
                Err(e) => return (out, Some(Error::at_frame(i, e))),
            }
        }
        (out, None)
    }

    /// Send frames **lazily**, yielding one `Result<FrameResponse, Error>` per
    /// frame as the returned iterator is pulled.
    ///
    /// Unlike [`Client::send_frames`] — which takes a fully materialized
    /// `&[Frame]` and collects every [`FrameResponse`] into a `Vec` before
    /// returning — this consumes any `IntoIterator<Item = Frame>` one frame at a
    /// time and yields each outcome immediately, never holding more than the
    /// current frame and its response. Use it when the source is a live producer
    /// (a channel, a socket, a file reader) and full materialization is wasteful
    /// or impossible. This is the Rust analogue of Python's
    /// `AletheiaClient.send_frames_iter`.
    ///
    /// **Contract** (commit-prefix-and-report; see
    /// `docs/architecture/CANCELLATION.md`): each `Ok` is a frame already
    /// committed to the stream state — durable, not rolled back. On the first
    /// failing frame the iterator yields the `Err` — an [`Error::Frame`] tagged
    /// with that frame's 0-based batch index, so the caller can locate it — and
    /// then ends (it is fused: no frames after a failure are sent). Cancellation
    /// is the standard
    /// iterator protocol — stop pulling (break the `for`, or drop the iterator)
    /// and the remaining frames are never sent; every value already yielded
    /// stays committed.
    ///
    /// Because the iterator borrows `&self`, you may interleave other client
    /// calls between pulls on the same single stream — the eager `&[Frame]` form
    /// structurally could not. That is sound on one sequential stream; it is
    /// simply a capability the lazy form adds.
    pub fn send_frames_iter<'a, I>(
        &'a self,
        frames: I,
    ) -> impl Iterator<Item = Result<FrameResponse, Error>> + 'a
    where
        I: IntoIterator<Item = Frame>,
        I::IntoIter: 'a,
    {
        let mut it = frames.into_iter();
        let mut index = 0usize;
        let mut stopped = false;
        core::iter::from_fn(move || {
            if stopped {
                return None;
            }
            let f = it.next()?;
            let i = index;
            index += 1;
            match self.send_frame(f.timestamp, f.id, f.dlc, &f.data, f.brs, f.esi) {
                Ok(resp) => Some(Ok(resp)),
                Err(e) => {
                    stopped = true;
                    // Tag with the failing frame's index (see [`Error::Frame`]).
                    Some(Err(Error::at_frame(i, e)))
                }
            }
        })
    }
}

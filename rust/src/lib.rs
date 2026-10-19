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
//! hot path. The typed DBC document model and the Check DSL are implemented; a
//! Rust host CLI remains `planned` (Phase 6) in `docs/FEATURE_MATRIX.yaml`.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::sync::Arc;

use crate::enrich::PropertyDiagnostic;
use crate::log::events;

use serde_json::json;

#[cfg(feature = "async")]
mod async_client;
mod backend;
pub mod check;
mod client_stream;
mod dbc;
mod enrich;
mod error;
pub mod log;
mod ltl;
mod mock;
mod response;
#[cfg(feature = "async")]
pub mod testing;
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
    DbcMessage, DbcSignal, EnvironmentVar, Node, ParsedDbc, Presence, SignalGroup,
    ValueDescription, ValueTable,
};
pub use error::{Error, Located};
pub use log::{LogField, LogLevel, LogRecord, LogValue, Logger};
pub use ltl::{Formula, Predicate, MAX_FORMULA_DEPTH};
pub use mock::MockBackend;
pub use response::{
    DbcText, Enrichment, ExtractionResult, FrameResponse, IssueCode, IssueSeverity, PropertyResult,
    SignalError, SignalValue, StreamResult, StreamWarning, ValidationIssue, ValidationResult,
    Verdict,
};
pub use types::{CanId, Dlc, Rational, TimeBound, Timestamp, MAX_EXTENDED_ID, MAX_STANDARD_ID};
#[cfg(feature = "yaml")]
pub use yaml::{load_checks_from_yaml, load_checks_from_yaml_file};

/// Stable signal-name-cache key from a raw CAN id value + its extended flag
/// (mirrors Go's `canIDKey`). Bit 32 carries the extended flag — safe because a
/// CAN id value is at most 29 bits, so a standard and an extended message with
/// the same numeric id map to distinct keys.
fn can_key(value: u32, extended: bool) -> u64 {
    u64::from(value) | (u64::from(extended) << 32)
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

/// The subset of extracted `values` named by `diag.signals`.
fn select_diag_values(
    diag: &PropertyDiagnostic,
    values: &[(String, Rational)],
) -> Vec<(String, Rational)> {
    values
        .iter()
        .filter(|(n, _)| diag.signals.iter().any(|s| s == n))
        .cloned()
        .collect()
}

/// A client over one `StreamState` in the verified core.
///
/// Delegates every raw FFI operation to a [`Backend`] (the production
/// `FfiBackend` by default, or an injected double); keeps the typed concerns —
/// validation, response decoding, violation enrichment, logging — on this side.
/// The default backend owns a thread-pinned GHC `StreamState`, so it is `!Send`,
/// which makes `Client` `!Send + !Sync` too (cross-thread use is a future slice,
/// tracked `planned`; for async use, see `AsyncClient` behind the `async`
/// feature — a doc link would only resolve when that feature is enabled).
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
    /// Per-CAN-id ordered signal names, populated from the parsed DBC. The binary
    /// extraction wire keys values by positional signal index, so this cache maps
    /// each index back to a name (see `response::decode_extraction_bin`). Keyed by
    /// [`can_key`] (value + extended bit, mirroring Go's `canIDKey`) so a standard
    /// and an extended message sharing a numeric id do not collide. No entry for a
    /// CAN id routes `extract_signals` to the JSON fallback. `RefCell` because the
    /// client methods take `&self`.
    signal_names: RefCell<HashMap<u64, Vec<String>>>,
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
                return Err(Error::validation(format!(
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
        async_client::spawn(move || self.build()).await
    }

    /// Build a runtime-agnostic [`AsyncClient`] over an injected [`Backend`]
    /// (feature `async`) — the async analogue of
    /// [`ClientBuilder::build_with_backend`], running without the `.so`.
    /// Applies this builder's logger / minimum level. A test starts no thread,
    /// so it hosts a client on a [`TurnExecutor`](crate::testing::TurnExecutor)
    /// instead.
    ///
    /// The injected backend is **moved to the async worker thread** (where the
    /// `!Send` sync `Client` lives), so — unlike the sync seam, which takes a bare
    /// `Box<dyn Backend>` — it must be `Send`. That `+ Send` bound is the only
    /// difference from [`ClientBuilder::build_with_backend`]; the [`Backend`]
    /// trait itself stays unbounded (the box coerces to `Box<dyn Backend>`,
    /// dropping the marker, when handed to the worker's sync client).
    ///
    /// Building the client is infallible (no `.so` to load), but spawning the
    /// worker thread and awaiting its init handshake can still fail — hence
    /// `Result`, matching [`ClientBuilder::build_async`].
    ///
    /// # Errors
    /// [`Error::InitFailed`] if the worker thread panics before reporting
    /// readiness.
    #[cfg(feature = "async")]
    pub async fn build_async_with_backend(
        self,
        backend: Box<dyn Backend + Send>,
    ) -> Result<AsyncClient, Error> {
        async_client::spawn(move || Ok(self.build_with_backend(backend))).await
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
            signal_names: RefCell::new(HashMap::new()),
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
        // Best-effort on the eval path: a render failure here is in practice only
        // an ABI malfunction (diagnostics exist only after property setup already
        // rendered the thresholds, latching the renderer's process-global RTS +
        // library state this render reuses). Degrade to the no-values reason rather
        // than fail an already-processed frame — no local fallback (we omit the
        // values, never render them locally). See `enrich::reason_without_values`.
        let enriched_reason = enrich::format_enriched_reason(diag, &values, &pr.reason)
            .unwrap_or_else(|_| enrich::reason_without_values(diag, &pr.reason));
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
            Some(all) => select_diag_values(diag, all),
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

    /// Enrich the final `Fails` / `Unresolved` verdicts at end-of-stream from
    /// the last frame seen per CAN id. Each distinct frame is extracted once and
    /// its values merged (first-seen order), then reused across every violation.
    /// Extraction only serves the signals the todo diagnostics reference: the
    /// frame loop stops as soon as all of them are merged, and is skipped
    /// outright when no diagnostic references any signal (enrichment still
    /// attaches below, with the no-values fallback reason).
    fn enrich_eos(&self, results: &mut [PropertyResult]) {
        if self.diags.borrow().is_empty() {
            return;
        }
        let todo = self.enrichment_todo(results, &[Verdict::Fails, Verdict::Unresolved]);
        if todo.is_empty() {
            return;
        }
        // The union of signal names any todo diagnostic wants, consumed as the
        // frame loop merges them ⇒ empty means extraction has nothing left to
        // contribute.
        let mut remaining: HashSet<&str> = todo
            .iter()
            .flat_map(|(_, diag)| diag.signals.iter().map(String::as_str))
            .collect();
        // `merged` stays a Vec to preserve the documented deterministic
        // first-seen order; `seen` is the O(1) membership guard beside it.
        let mut merged: Vec<(String, Rational)> = Vec::new();
        let mut any_failed = false;
        if !remaining.is_empty() {
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
            let mut seen: HashSet<String> = HashSet::new();
            for (id, dlc, data) in &frames {
                match self.extract_all(*id, *dlc, data) {
                    Some(found) => {
                        for (name, value) in found {
                            if !seen.contains(&name) {
                                remaining.remove(name.as_str());
                                seen.insert(name.clone());
                                merged.push((name, value));
                            }
                        }
                    }
                    None => any_failed = true,
                }
                if remaining.is_empty() {
                    break;
                }
            }
        }
        for (slot, diag) in todo {
            let values = select_diag_values(&diag, &merged);
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
    /// Returns [`Error`] if a required symbol is missing or the core returns a
    /// null response. The core reads every byte of `command`, and answers a NUL
    /// among them with an `ffi_validation_error` response.
    pub fn process(&self, command: &str) -> Result<String, Error> {
        self.backend.process(command)
    }

    /// Parse a DBC database from its `.dbc` text image and load it into this
    /// stream, returning the typed [`Dbc`] document together with any validation
    /// warnings the core reported.
    ///
    /// # Errors
    /// [`Error::ValidationFailed`] if the text parses but structural validation
    /// finds errors, [`Error::Core`] if the text fails to parse (or
    /// [`Error::InputBoundExceeded`] if it trips an adversarial-input bound such
    /// as identifier length or message count), or [`Error::Protocol`] on an
    /// unexpected response.
    pub fn parse_dbc_text(&self, text: &str) -> Result<ParsedDbc, Error> {
        let cmd = json!({ "type": "command", "command": "parseDBCText", "text": text });
        let raw = self.process(&cmd.to_string())?;
        let parsed = dbc::decode_parsed_dbc(&raw)?;
        self.populate_signal_names(&parsed.dbc);
        self.emit(
            LogLevel::Info,
            events::DBC_PARSED,
            &[LogField::new(
                "messages",
                LogValue::U64(parsed.dbc.messages.len() as u64),
            )],
        );
        Ok(parsed)
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
    /// [`Error::ValidationFailed`] if the DBC fails validation,
    /// [`Error::InputBoundExceeded`] if it exceeds one of the kernel's size bounds
    /// (a list or a string longer than its limit), [`Error::Core`] on any other
    /// core rejection, or [`Error::Protocol`] on an unexpected response.
    pub fn parse_dbc(&self, dbc: &Dbc) -> Result<ParsedDbc, Error> {
        // Build the envelope then move the serialized DBC in: `json!({…: expr})`
        // deep-copies a `Value` operand (via `to_value(&expr)`), which would
        // double-allocate a large document.
        let mut cmd = json!({ "type": "command", "command": "parseDBC" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        let parsed = dbc::decode_parsed_dbc(&raw)?;
        self.populate_signal_names(&parsed.dbc);
        self.emit(
            LogLevel::Info,
            events::DBC_PARSED,
            &[LogField::new(
                "messages",
                LogValue::U64(parsed.dbc.messages.len() as u64),
            )],
        );
        Ok(parsed)
    }

    /// Rebuild the per-CAN-id signal-name cache from a freshly-parsed DBC (the
    /// canonical, post-validation document the kernel now holds). Replaces the
    /// whole map so a re-parse cannot leave stale names. Each message's signals
    /// are stored in positional order — the order the kernel assigns binary-
    /// extraction indices, so `names[idx]` in `decode_extraction_bin` is correct.
    fn populate_signal_names(&self, dbc: &Dbc) {
        let mut cache = self.signal_names.borrow_mut();
        cache.clear();
        for msg in &dbc.messages {
            cache.insert(
                can_key(msg.id, msg.extended),
                msg.signals.iter().map(|s| s.name.clone()).collect(),
            );
        }
    }

    /// Run the structural validator over a typed [`Dbc`] without modifying this
    /// stream's loaded state, returning every issue found.
    ///
    /// # Errors
    /// [`Error::InputBoundExceeded`] if the DBC exceeds one of the kernel's size
    /// bounds (a list or a string longer than its limit), or [`Error::Core`] /
    /// [`Error::Protocol`] on any other core error or an unexpected response.
    pub fn validate_dbc(&self, dbc: &Dbc) -> Result<ValidationResult, Error> {
        let mut cmd = json!({ "type": "command", "command": "validateDBC" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        response::decode_validation(&raw)
    }

    /// Render a typed [`Dbc`] back to `.dbc` file text via the verified Agda
    /// formatter, returning a [`DbcText`] — the text image plus its `wfTextIssues`
    /// diagnostics (warning-severity, advisory). Always strict: it returns text
    /// only when the emitted text provably re-parses to the input DBC —
    /// `parse_dbc_text(&format_dbc_text(d)?.text)` returns `d` byte-identical (a
    /// stricter condition than validating clean — see the "well-formed DBC" entry
    /// in `docs/GLOSSARY.md`). That guarantee holds at the text-parser level: for
    /// a [`Dbc`] carrying duplicates that are error-class at load (duplicate
    /// message ids / signal names — emitted here with warnings), the text
    /// round-trips in the proof but [`Self::parse_dbc_text`]'s validating load
    /// refuses it. The returned `issues` may be non-empty even on a
    /// proven round-trip. Does not modify this stream's loaded state.
    ///
    /// # Errors
    /// [`Error::TextRoundtripFailed`] if the emitted text does not re-parse to the
    /// input DBC (a divergent DBC, e.g. a multi-value mux) — carrying the
    /// diagnostics led by `text_roundtrip_divergence` — rather than lossy text;
    /// [`Error::InputBoundExceeded`] if the DBC exceeds one of the kernel's size
    /// bounds (a list or a string longer than its limit, including the node list
    /// it derives from the senders when `nodes` is empty), checked before
    /// anything is formatted; [`Error::Core`] if the document fails Agda-side
    /// parsing; or [`Error::Protocol`] on an unexpected response.
    pub fn format_dbc_text(&self, dbc: &Dbc) -> Result<DbcText, Error> {
        let mut cmd = json!({ "type": "command", "command": "formatDBCText" });
        cmd["dbc"] = dbc.to_value();
        let raw = self.process(&cmd.to_string())?;
        response::decode_format_text(&raw)
    }
}

#[cfg(test)]
mod tests;

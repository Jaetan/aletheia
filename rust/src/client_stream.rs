// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The stream and frame methods of `Client`: binding properties, streaming
//! frames, extracting signals, and building and updating frame payloads.

use super::*;

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

impl Client {
    /// Bind the LTL properties to monitor. Call after `parse_dbc_text`, before
    /// `start_stream`.
    ///
    /// # Errors
    /// [`Error::Validation`] if any formula is invalid (bad predicate / depth),
    /// [`Error::Core`] if the core rejects the set (e.g. no DBC loaded) — or
    /// [`Error::InputBoundExceeded`] if a formula trips a bound (nesting depth /
    /// atom count) — or a
    /// library-load error ([`Error::LibraryLoad`] / [`Error::SymbolMissing`]) if the
    /// kernel rational renderer cannot be loaded while building the per-property
    /// enrichment diagnostics (it renders the predicate thresholds via the FFI).
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
        *self.diags.borrow_mut() = properties
            .iter()
            .map(enrich::build_diagnostic)
            .collect::<Result<Vec<_>, _>>()?;
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
    /// [`Error::Validation`] if the payload length does not match the DLC,
    /// else [`Error::Core`] / [`Error::Protocol`].
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
    /// [`Error::Validation`] if the payload length does not match the DLC,
    /// else [`Error::Core`] / [`Error::Protocol`].
    pub fn extract_signals(
        &self,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
    ) -> Result<ExtractionResult, Error> {
        validate_frame_len(dlc, data)?;
        // Binary fast path: when the signal names for this CAN id are cached (a DBC
        // was parsed), decode the packed binary buffer directly — no JSON
        // serialize/parse. Fall back to the JSON path ONLY when there are no cached
        // names or the backend has no binary FFI (a mock → BinaryPathUnsupported);
        // any OTHER binary error is a real failure and is surfaced, not silently
        // retried on the JSON path. Mirrors Go's extractSignalsLocked. Both the
        // public API and the enrichment loop funnel through here, so the two emit
        // sites (process-failed / parse-failed) cover every path.
        // The signal_names borrow is held across the FFI call + decode so the
        // cached names pass by reference — no per-call clone on the hot path.
        // Nothing in this block re-borrows signal_names (the FFI call, the decode,
        // and log_extraction_failure all touch other state), so the RefCell borrow
        // is safe; the block scopes it so the JSON fallback below runs with it
        // already dropped.
        {
            let cache = self.signal_names.borrow();
            if let Some(names) = cache.get(&can_key(id.value(), id.is_extended())) {
                match self.backend.extract_signals_bin(id, dlc, data) {
                    Ok(buf) => {
                        return response::decode_extraction_bin(&buf, names).inspect_err(|e| {
                            self.log_extraction_failure(id, events::EXTRACTION_PARSE_FAILED, e);
                        });
                    }
                    Err(Error::BinaryPathUnsupported) => { /* fall through to JSON path */ }
                    Err(e) => {
                        self.log_extraction_failure(id, events::EXTRACTION_PROCESS_FAILED, &e);
                        return Err(e);
                    }
                }
            }
        }
        // JSON fallback: no cached names, or the backend has no binary path.
        let raw = match self.backend.extract_signals_binary(id, dlc, data) {
            Ok(raw) => raw,
            Err(e) => {
                self.log_extraction_failure(id, events::EXTRACTION_PROCESS_FAILED, &e);
                return Err(e);
            }
        };
        response::decode_extraction(&raw).inspect_err(|e| {
            self.log_extraction_failure(id, events::EXTRACTION_PARSE_FAILED, e);
        })
    }

    /// Log an extraction failure at Warn with the `canId` + `error` fields Go's
    /// `extractSignalsLocked` and the Python/C++ bindings use.
    fn log_extraction_failure(&self, id: CanId, event: &str, err: &Error) {
        let msg = err.to_string();
        self.emit(
            LogLevel::Warn,
            event,
            &[
                LogField::new("canId", LogValue::U64(u64::from(id.value()))),
                LogField::new("error", LogValue::Str(&msg)),
            ],
        );
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
    /// injections than `u32::MAX`; [`Error::Core`] carrying the core's code if it
    /// rejects a value (out of range / not representable at the signal's scale).
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
    /// [`Error::Core`] carrying the core's code if it rejects the update.
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

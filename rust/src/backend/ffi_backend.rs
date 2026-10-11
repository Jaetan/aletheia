// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The production [`Backend`], [`FfiBackend`], with the frames it builds, and
//! the kernel's rational rendering and decimal parsing ([`format_rational`],
//! [`parse_decimal`]).

use std::ffi::c_char;

use libloading::Symbol;
use serde_json::Value;

use super::{
    check_buffer_status, encode_opt_bool, ensure_rts, frame_len, symbols, take_extraction_buffer,
    take_response, Backend, FfiBuffer, FfiDecimal, FfiFrame, FfiRational, FfiSignalValues, FfiText,
    FrameBinFn, SignalInjection, StateHandle, Symbols, RTS_INIT,
};
use crate::error::Error;
use crate::log::{LogLevel, Logger};
use crate::types::{CanId, Dlc, Rational, Timestamp};

impl FfiFrame {
    /// A trace event without payload: a remote frame's timestamp and
    /// identifier, or an error frame's timestamp alone.
    fn event(ts: Timestamp, can_id: u32, extended: bool) -> Self {
        FfiFrame {
            timestamp: ts.micros(),
            data: std::ptr::null(),
            can_id,
            extended: u8::from(extended),
            dlc: 0,
            data_len: 0,
            brs_present: 0,
            brs_value: 0,
            esi_present: 0,
            esi_value: 0,
        }
    }

    /// A frame carrying identifier and DLC, with no payload, no timestamp and
    /// no bus bits: what `aletheia_build_frame_bin` reads, as it writes the
    /// payload itself.
    fn header(can_id: u32, extended: bool, dlc: Dlc) -> Self {
        FfiFrame {
            timestamp: 0,
            data: std::ptr::null(),
            can_id,
            extended: u8::from(extended),
            dlc: dlc.value(),
            data_len: 0,
            brs_present: 0,
            brs_value: 0,
            esi_present: 0,
            esi_value: 0,
        }
    }

    /// The [`header`](Self::header) frame carrying `data`, refused unless it
    /// is exactly the DLC's byte count ([`frame_len`]): what the extraction
    /// and update entries read, and `aletheia_send_frame` once it adds the
    /// timestamp and the bus bits.
    fn new(can_id: u32, extended: bool, dlc: Dlc, data: &[u8]) -> Result<Self, Error> {
        Ok(FfiFrame {
            data: slice_ptr(data),
            data_len: frame_len(dlc, data)?,
            ..FfiFrame::header(can_id, extended, dlc)
        })
    }
}

/// Render a [`Rational`] via the verified Agda kernel's `formatℚ` (the FFI export
/// `aletheia_format_rational`) — the single source of truth for rational display,
/// byte-identical to the Python / Go / C++ bindings by construction (no local
/// fallback). Loads `libaletheia-ffi.so` for its symbols, but is *vocal*: it never
/// initialises the GHC RTS itself. An [`FfiBackend`] (via a [`Client`](crate::Client))
/// is the sole initialiser (it owns the bus-count `-N`), so a render with the RTS
/// down returns an error rather than self-initialising — and the error is returned
/// *before* the FFI call, because invoking the MAlonzo export with the RTS down is
/// undefined behaviour. Mirrors Go (#104), C++ (#105), and Python (#106).
///
/// # Errors
/// [`Error::RtsNotInitialized`] if the GHC runtime is not initialised (no backend
/// created), or [`Error::Protocol`] in the unreachable case of a null return (an
/// ABI/kernel malfunction). A library-load / missing-symbol failure cannot surface
/// here: the RTS gate passing implies the symbol table is already latched
/// ([`FfiBackend::new`] resolves the table before `ensure_rts`, and it is the sole
/// RTS initialiser). The call cannot fail for a well-formed rational once a
/// backend is up: the kernel never emits a zero denominator and the input's
/// denominator is positive by construction.
pub(crate) fn format_rational(r: Rational) -> Result<String, Error> {
    // Check the RTS BEFORE loading the library. The renderer never initialises the
    // RTS — an FfiBackend is the sole initialiser, so RTS_INIT is Some exactly when
    // a real backend has run ensure_rts (which also loaded the .so). Returning
    // first means a caller that renders before any backend exists (e.g. a
    // check-builder validation error) fails fast without attempting a dlopen —
    // and, when the .so is absent, without re-attempting it on every call (the
    // library()/symbols() OnceLocks cache only successes). Invoking the MAlonzo
    // export with the RTS down is undefined behaviour, not a catchable error.
    match RTS_INIT.get() {
        None => return Err(Error::RtsNotInitialized),
        Some(Err(e)) => return Err(e.clone()),
        Some(Ok(())) => {}
    }
    let syms = symbols()?;
    let value = FfiRational {
        numerator: r.numerator(),
        denominator: r.denominator(),
    };
    // SAFETY: `value` outlives the call; the returned pointer is a GHC-allocated
    // CString, which `take_response` copies and releases.
    let ptr = unsafe { (syms.format_rational)(&value) };
    if ptr.is_null() {
        // Unreachable for a well-formed rational (the kernel never returns null and
        // the denominator is positive by construction). Surface a typed error rather
        // than a fabricated value: a null means an ABI/kernel malfunction, and a
        // silent "0" would both violate no-local-fallback and hide the bug.
        return Err(Error::Protocol(
            "aletheia_format_rational returned a null pointer".to_string(),
        ));
    }
    Ok(take_response(syms, ptr))
}

/// Parse a decimal string into an exact [`Rational`] via the verified Agda
/// kernel's `aletheia_parse_decimal` — the cross-binding single source of truth
/// for decimal→rational (the float principle: a decimal is an exact rational,
/// never a float). The accepted grammar is the kernel's: `-?digits` or
/// `-?digits.digits+` — no `+` sign, no leading/trailing `.`, no exponent.
///
/// Like [`format_rational`], this is *vocal*: it never initialises the GHC RTS
/// (an [`FfiBackend`] is the sole initialiser, owning the bus-count `-N`), so it
/// returns [`Error::RtsNotInitialized`] *before* the FFI call if the RTS is down
/// (invoking the MAlonzo export with the RTS down is undefined behaviour).
///
/// # Errors
/// [`Error::RtsNotInitialized`] if no backend is up (as for [`format_rational`],
/// the RTS gate passing implies the symbol table is already latched, so a
/// library-load / missing-symbol failure cannot surface here);
/// [`Error::Validation`] if the string is not a valid decimal literal or its
/// rational overflows `i64` (the kernel's `decimal_parse_failed` /
/// `decimal_overflow` — user input, not a wire fault); [`Error::Protocol`] on a
/// null return or malformed response (an ABI/kernel malfunction).
pub(crate) fn parse_decimal(s: &str) -> Result<Rational, Error> {
    // Vocal, exactly like format_rational (and in the same order: RTS gate first,
    // symbols second): never self-init the RTS; return before the FFI call (the
    // MAlonzo export with the RTS down is UB) — see format_rational's rationale.
    match RTS_INIT.get() {
        None => return Err(Error::RtsNotInitialized),
        Some(Err(e)) => return Err(e.clone()),
        Some(Ok(())) => {}
    }
    let syms = symbols()?;
    let input = FfiText::of(s);
    let mut out = FfiDecimal {
        value: FfiRational {
            numerator: 0,
            denominator: 0,
        },
        err: std::ptr::null_mut(),
    };
    // SAFETY: `input` borrows `s`, which outlives the call, and the kernel reads
    // exactly `input.size` bytes of it; `out` is an out-param the kernel writes.
    let status = unsafe { (syms.parse_decimal)(&input, &mut out) };
    if status != 0 {
        if out.err.is_null() {
            return Err(Error::Protocol(
                "aletheia_parse_decimal failed without an error".to_string(),
            ));
        }
        let envelope = take_response(syms, out.err);
        return Err(decimal_refusal(&envelope));
    }
    // The kernel answers lowest terms over a positive denominator; `new` refuses
    // anything else, which would be the ABI or the kernel malfunctioning.
    Rational::new(out.value.numerator, out.value.denominator).map_err(|e| {
        Error::Protocol(format!(
            "aletheia_parse_decimal answered an invalid rational: {e}"
        ))
    })
}

/// Read the `aletheia_parse_decimal` error envelope, mapping its reason to
/// [`Error::Validation`]: a refused literal (`decimal_parse_failed` /
/// `decimal_overflow`) is user input, not a wire fault.
fn decimal_refusal(json: &str) -> Error {
    match serde_json::from_str::<Value>(json) {
        Ok(value) => Error::Validation(
            value
                .get("message")
                .and_then(Value::as_str)
                .unwrap_or("invalid decimal literal")
                .to_string(),
        ),
        Err(e) => Error::Protocol(format!("aletheia_parse_decimal: malformed response: {e}")),
    }
}

/// Null pointer for an empty slice (the FFI must not deref a zero-length array),
/// else the slice's data pointer.
fn slice_ptr<T>(s: &[T]) -> *const T {
    if s.is_empty() {
        std::ptr::null()
    } else {
        s.as_ptr()
    }
}

/// The production [`Backend`]: loads `libaletheia-ffi.so` and owns one
/// `StreamState` for its lifetime.
///
/// Holds a raw `StreamState` pointer, so it is intentionally `!Send + !Sync`:
/// the GHC RTS is thread-pinned and one handle must not be shared across threads.
pub(crate) struct FfiBackend {
    handle: StateHandle,
}

impl FfiBackend {
    /// Load the core, initialise the GHC RTS once per process, and allocate a
    /// fresh `StreamState`. `logger`/`min_level` are used only to emit the
    /// `rts.cores_mismatch` warning if a later backend requests a different
    /// core count than the first one latched.
    pub(crate) fn new(
        cores: Option<u32>,
        logger: Option<&dyn Logger>,
        min_level: LogLevel,
    ) -> Result<Self, Error> {
        // Resolves the WHOLE export table up front (once per process): any
        // missing symbol fails construction here with its name, instead of on
        // a later call — and, per `symbols()`, a failure is not latched.
        let syms = symbols()?;
        ensure_rts(syms, cores, logger, min_level)?;
        // SAFETY: `aletheia_init` is `StateHandle aletheia_init(void)`.
        let handle = unsafe { (syms.init)() };
        if handle.is_null() {
            return Err(Error::InitFailed);
        }
        Ok(FfiBackend { handle })
    }

    /// Run `call` (handed the cached symbol table) to obtain a GHC-allocated
    /// response pointer, then copy it out and free it (`take_response`, whose
    /// deallocator was pre-resolved with everything else: a `.so` missing
    /// `aletheia_free_str` already failed in [`FfiBackend::new`]).
    fn invoke(&self, call: impl FnOnce(&Symbols) -> *mut c_char) -> Result<String, Error> {
        let syms = symbols()?;
        let ptr = call(syms);
        if ptr.is_null() {
            return Err(Error::NullResponse);
        }
        Ok(take_response(syms, ptr))
    }
}

impl Backend for FfiBackend {
    fn process(&self, input: &str) -> Result<String, Error> {
        let text = FfiText::of(input);
        // SAFETY: `handle` is the live StreamState this backend owns; `text`
        // borrows `input`, which outlives the call, and the kernel reads exactly
        // `text.size` bytes of it.
        self.invoke(|syms| unsafe { (syms.process)(self.handle, &text) })
    }

    fn send_frame_binary(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<String, Error> {
        let mut frame = FfiFrame::new(id.value(), id.is_extended(), dlc, data)?;
        frame.timestamp = ts.micros();
        (frame.brs_present, frame.brs_value) = encode_opt_bool(brs);
        (frame.esi_present, frame.esi_value) = encode_opt_bool(esi);
        // SAFETY: `handle` is the live StreamState this backend owns; `frame`
        // points at `data`, valid for its `data_len` bytes (the DLC's byte
        // count, checked by `frame_len`), and both outlive the call.
        self.invoke(|syms| unsafe { (syms.send_frame)(self.handle, &frame) })
    }

    fn send_error_binary(&self, ts: Timestamp) -> Result<String, Error> {
        let frame = FfiFrame::event(ts, 0, false);
        // SAFETY: `handle` is the live StreamState this backend owns; `frame`
        // outlives the call.
        self.invoke(|syms| unsafe { (syms.send_error)(self.handle, &frame) })
    }

    fn send_remote_binary(&self, ts: Timestamp, id: CanId) -> Result<String, Error> {
        let frame = FfiFrame::event(ts, id.value(), id.is_extended());
        // SAFETY: `handle` is the live StreamState this backend owns; `frame`
        // outlives the call.
        self.invoke(|syms| unsafe { (syms.send_remote)(self.handle, &frame) })
    }

    fn start_stream_binary(&self) -> Result<String, Error> {
        // SAFETY: `handle` is the live StreamState this backend owns.
        self.invoke(|syms| unsafe { (syms.start_stream)(self.handle) })
    }

    fn end_stream_binary(&self) -> Result<String, Error> {
        // SAFETY: `handle` is the live StreamState this backend owns.
        self.invoke(|syms| unsafe { (syms.end_stream)(self.handle) })
    }

    fn format_dbc_binary(&self) -> Result<String, Error> {
        // SAFETY: `handle` is the live StreamState this backend owns.
        self.invoke(|syms| unsafe { (syms.format_dbc)(self.handle) })
    }

    fn extract_signals_binary(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<String, Error> {
        let frame = FfiFrame::new(id.value(), id.is_extended(), dlc, data)?;
        // SAFETY: `handle` is the live StreamState this backend owns; `frame`
        // points at `data`, valid for its `data_len` bytes (the DLC's byte
        // count, checked by `frame_len`), and both outlive the call.
        self.invoke(|syms| unsafe { (syms.extract_signals)(self.handle, &frame) })
    }

    fn extract_signals_bin(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<Vec<u8>, Error> {
        let frame = FfiFrame::new(id.value(), id.is_extended(), dlc, data)?;
        let syms = symbols()?;
        let mut out = FfiBuffer {
            data: std::ptr::null_mut(),
            err: std::ptr::null_mut(),
            size: 0,
        };
        // SAFETY: `handle` is the live StreamState this backend owns; `frame`
        // points at `data`, valid for its `data_len` bytes (the DLC's byte
        // count, checked by `frame_len`); `out` is an out-param the core writes.
        let status = unsafe { (syms.extract_signals_bin)(self.handle, &frame, &mut out) };
        check_buffer_status(status, out.err, syms, "extract_signals_bin")?;
        // SAFETY: on success the core set `out.data` to an `out.size`-byte
        // buffer it allocated, and `free_buf` is its deallocator.
        unsafe { take_extraction_buffer(out.data, out.size, |buf| (syms.free_buf)(buf)) }
    }

    fn build_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        let frame = FfiFrame::header(id, extended, dlc);
        let syms = symbols()?;
        self.frame_bin(&syms.build_frame, &frame, dlc, signals, "build_frame")
    }

    fn update_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        frame: &[u8],
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        let frame = FfiFrame::new(id, extended, dlc, frame)?;
        let syms = symbols()?;
        self.frame_bin(&syms.update_frame, &frame, dlc, signals, "update_frame")
    }
}

impl FfiBackend {
    /// Run build or update, which differ only in the payload `frame` carries,
    /// and answer the payload the core wrote.
    fn frame_bin(
        &self,
        entry: &Symbol<'static, FrameBinFn>,
        frame: &FfiFrame,
        dlc: Dlc,
        signals: SignalInjection<'_>,
        op: &str,
    ) -> Result<Vec<u8>, Error> {
        let count = u32::try_from(signals.indices.len())
            .map_err(|_| Error::Validation("too many signal injections".to_string()))?;
        let values = FfiSignalValues {
            indices: slice_ptr(signals.indices),
            numerators: slice_ptr(signals.nums),
            denominators: slice_ptr(signals.dens),
            count,
        };
        let mut payload = vec![0u8; dlc.to_bytes()];
        let mut out = FfiBuffer {
            data: if payload.is_empty() {
                std::ptr::null_mut()
            } else {
                payload.as_mut_ptr()
            },
            err: std::ptr::null_mut(),
            // A DLC's byte count is at most 64.
            size: payload.len() as u32,
        };
        let syms = symbols()?;
        // SAFETY: `out.data` holds `out.size` bytes, the DLC's count (what the
        // core writes); the parallel arrays all share `indices.len()`;
        // `frame`'s payload is valid for its `data_len` bytes.
        let status = unsafe { entry(self.handle, frame, &values, &mut out) };
        check_buffer_status(status, out.err, syms, op)?;
        payload.truncate(out.size as usize);
        Ok(payload)
    }
}

impl Drop for FfiBackend {
    fn drop(&mut self) {
        // Always the latched fast path: `new()` already resolved the table.
        if let Ok(syms) = symbols() {
            // SAFETY: `handle` is the live StreamState `new()` allocated; it is
            // not used again after `aletheia_close` releases it.
            unsafe { (syms.close)(self.handle) };
        }
    }
}

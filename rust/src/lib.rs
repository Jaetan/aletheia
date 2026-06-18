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
//!
//! Frame streaming uses the binary FFI (`aletheia_send_frame`, …), *not* the
//! JSON command path — that mirrors every other binding and the core's intended
//! hot path. The typed DBC document model, the Check DSL, and CLI affordances
//! are tracked as `planned` in `docs/FEATURE_MATRIX.yaml`.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::marker::PhantomData;
use std::sync::OnceLock;

use libloading::{Library, Symbol};
use serde_json::json;

pub mod check;
mod dbc;
mod error;
mod ltl;
mod response;
mod types;

pub use check::Check;
pub use dbc::{
    AttrScope, AttrTarget, AttrType, AttrValue, Attribute, ByteOrder, Comment, CommentTarget, Dbc,
    DbcMessage, DbcSignal, EnvironmentVar, Node, Presence, SignalGroup, ValueDescription,
    ValueTable,
};
pub use error::Error;
pub use ltl::{Formula, Predicate, MAX_FORMULA_DEPTH};
pub use response::{
    Enrichment, ExtractionResult, FrameResponse, PropertyResult, SignalValue, StreamResult,
    StreamWarning, ValidationIssue, ValidationResult, Verdict,
};
pub use types::{CanId, Dlc, Rational, TimeBound, Timestamp, MAX_EXTENDED_ID, MAX_STANDARD_ID};

/// Opaque pointer to the `StreamState` owned by the core (from `aletheia_init`).
type StateHandle = *mut c_void;

/// CAN-FD's largest payload; frames longer than this are rejected before the FFI.
const MAX_FRAME_BYTES: usize = 64;

// --- FFI signatures (binary fast path) ------------------------------------

type SendFrameFn = unsafe extern "C" fn(
    StateHandle,
    u64, // timestamp µs
    u32, // canId
    u8,  // extended
    u8,  // dlc
    *const u8,
    u8, // data len
    u8, // brs present
    u8, // brs value
    u8, // esi present
    u8, // esi value
) -> *mut c_char;
type SendErrorFn = unsafe extern "C" fn(StateHandle, u64) -> *mut c_char;
type SendRemoteFn = unsafe extern "C" fn(StateHandle, u64, u32, u8) -> *mut c_char;
type StreamLifecycleFn = unsafe extern "C" fn(StateHandle) -> *mut c_char;
type ExtractFn = unsafe extern "C" fn(StateHandle, u32, u8, u8, *const u8, u8) -> *mut c_char;
// Build/update use an output-buffer convention: the caller allocates `out_buf`
// (`dlc` bytes), passes the parallel (indices, nums, dens) signal arrays, and
// reads an `i8` status — nonzero means failure, with the message in `out_err`
// (a GHC-allocated CString the caller frees via `aletheia_free_str`).
type BuildFrameFn = unsafe extern "C" fn(
    StateHandle,
    u32, // canId
    u8,  // extended
    u8,  // dlc
    u32, // numSignals
    *const u32,
    *const i64,
    *const i64,
    *mut u8,          // out_buf (dlc bytes)
    *mut *mut c_char, // out_err
) -> i8;
type UpdateFrameFn = unsafe extern "C" fn(
    StateHandle,
    u32,
    u8,
    u8,
    *const u8, // existing frame
    u8,        // frame len
    u32,
    *const u32,
    *const i64,
    *const i64,
    *mut u8,
    *mut *mut c_char,
) -> i8;

/// Resolve the shared-library path: the `ALETHEIA_LIB` override, else the
/// conventional name (resolved by the dynamic loader's search path).
fn lib_path() -> String {
    std::env::var("ALETHEIA_LIB").unwrap_or_else(|_| "libaletheia-ffi.so".to_string())
}

/// Process-global handle to the loaded library. The GHC RTS owns threads for the
/// process lifetime, so the library is loaded once and never unloaded.
static LIB: OnceLock<Library> = OnceLock::new();
static RTS_INIT: OnceLock<Result<(), Error>> = OnceLock::new();

fn library() -> Result<&'static Library, Error> {
    if let Some(lib) = LIB.get() {
        return Ok(lib);
    }
    let path = lib_path();
    // SAFETY: loading a shared library runs its initialisers; the Aletheia .so is
    // a GHC foreign-library whose only global state is the RTS (started below).
    let lib = unsafe { Library::new(&path) }.map_err(|e| Error::LibraryLoad {
        path: path.clone(),
        source: e.to_string(),
    })?;
    // If another thread won the race, drop ours and use theirs (the OS refcounts
    // the underlying dlopen, so the mapping is shared either way).
    let _ = LIB.set(lib);
    Ok(LIB.get().expect("LIB was just set"))
}

/// Look up a C ABI symbol, mapping absence to a typed error.
///
/// # Safety
/// The caller must instantiate `T` with the symbol's exact ABI signature.
unsafe fn symbol<'lib, T>(lib: &'lib Library, name: &[u8]) -> Result<Symbol<'lib, T>, Error> {
    lib.get(name).map_err(|_| {
        Error::SymbolMissing(
            String::from_utf8_lossy(name)
                .trim_end_matches('\0')
                .to_string(),
        )
    })
}

/// Initialise the GHC RTS exactly once for the process.
///
/// Mirrors the Go binding: the RTS cannot be re-initialised after `hs_exit`, so
/// we start it once and never tear it down. The outcome is latched in a
/// `OnceLock<Result<…>>` so a second `Client::new()` after a failed first one
/// fails identically rather than silently masking a broken `.so`.
fn ensure_rts(lib: &Library) -> Result<(), Error> {
    RTS_INIT
        .get_or_init(|| {
            // SAFETY: `hs_init` has signature `void hs_init(int *argc, char ***argv)`;
            // NULL/NULL is permitted by the GHC runtime and selects default flags.
            let hs_init = unsafe {
                symbol::<unsafe extern "C" fn(*mut c_int, *mut *mut *mut c_char)>(lib, b"hs_init\0")
            }?;
            unsafe { hs_init(std::ptr::null_mut(), std::ptr::null_mut()) };
            Ok(())
        })
        .clone()
}

/// RAII guard for a C string the core returned (allocated by the GHC RTS).
///
/// The bytes must be copied out and then released with `aletheia_free_str` —
/// **never** with `CString::from_raw`, which would hand RTS memory to Rust's
/// allocator and corrupt the heap. Resolving `free_str` up front (in the caller,
/// before allocating) keeps this guard's `Drop` infallible.
type FreeStrFn<'a> = Symbol<'a, unsafe extern "C" fn(*mut c_char)>;

struct Response<'a> {
    ptr: *mut c_char,
    free_str: FreeStrFn<'a>,
}

impl Response<'_> {
    /// Copy the bytes into an owned `String`; the C buffer is freed on drop.
    fn into_string(self) -> String {
        // SAFETY: `ptr` is a non-null, NUL-terminated C string from the core.
        unsafe { CStr::from_ptr(self.ptr) }
            .to_string_lossy()
            .into_owned()
    }
}

impl Drop for Response<'_> {
    fn drop(&mut self) {
        // SAFETY: `ptr` was allocated by the core; `free_str` is its matching
        // deallocator (resolved up front, so it is known to exist).
        unsafe { (self.free_str)(self.ptr) };
    }
}

/// Encode an optional CAN-FD bit as the `(present, value)` byte pair the FFI
/// expects: `None` → `(0,0)` (CAN 2.0B), `Some(false)` → `(1,0)`, `Some(true)` → `(1,1)`.
fn encode_opt_bool(b: Option<bool>) -> (u8, u8) {
    match b {
        None => (0, 0),
        Some(false) => (1, 0),
        Some(true) => (1, 1),
    }
}

/// Validate a payload length against the CAN-FD maximum and narrow it to `u8`.
fn frame_len(data: &[u8]) -> Result<u8, Error> {
    if data.len() > MAX_FRAME_BYTES {
        return Err(Error::Validation(format!(
            "frame payload {} bytes exceeds CAN-FD maximum of {MAX_FRAME_BYTES}",
            data.len()
        )));
    }
    Ok(data.len() as u8) // guarded above: <= 64 fits u8
}

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

/// Null pointer for an empty slice (the FFI must not deref a zero-length array),
/// else the slice's data pointer.
fn slice_ptr<T>(s: &[T]) -> *const T {
    if s.is_empty() {
        std::ptr::null()
    } else {
        s.as_ptr()
    }
}

/// Interpret a build/update FFI status: nonzero ⇒ read and free `out_err`.
fn check_buffer_status(
    status: i8,
    out_err: *mut c_char,
    free_str: &Symbol<unsafe extern "C" fn(*mut c_char)>,
    op: &str,
) -> Result<(), Error> {
    if status == 0 {
        return Ok(());
    }
    if out_err.is_null() {
        return Err(Error::Protocol(format!(
            "{op}: status {status} with null error message"
        )));
    }
    // SAFETY: a nonzero status with non-null `out_err` is a GHC-allocated C
    // string; copy it out, then release it with the core's deallocator.
    let msg = unsafe { CStr::from_ptr(out_err) }
        .to_string_lossy()
        .into_owned();
    unsafe { free_str(out_err) };
    Err(Error::Protocol(format!("{op}: {msg}")))
}

/// A client over one `StreamState` in the verified core.
///
/// Holds a raw `StreamState` pointer, so it is intentionally `!Send + !Sync`:
/// the GHC RTS is thread-pinned and one handle must not be shared across threads.
/// Cross-thread use is a future slice (tracked `planned`).
pub struct Client {
    handle: StateHandle,
    /// Makes the `!Send + !Sync` contract explicit and future-proof. A raw
    /// pointer (`StateHandle = *mut c_void`) is already `!Send + !Sync`, so this
    /// is not load-bearing today — but it keeps `Client` thread-bound even if a
    /// `Send`/`Sync` field is added later, rather than relying on the current
    /// field set.
    _not_send_sync: PhantomData<*const ()>,
}

impl Client {
    /// Load the core (once per process), initialise the GHC RTS (once), and
    /// allocate a fresh `StreamState`.
    ///
    /// # Errors
    /// Returns [`Error`] if the library cannot be loaded, a required symbol is
    /// missing, or the core fails to initialise.
    pub fn new() -> Result<Self, Error> {
        let lib = library()?;
        ensure_rts(lib)?;
        // SAFETY: `aletheia_init` is `StateHandle aletheia_init(void)`.
        let init =
            unsafe { symbol::<unsafe extern "C" fn() -> StateHandle>(lib, b"aletheia_init\0") }?;
        let handle = unsafe { init() };
        if handle.is_null() {
            return Err(Error::InitFailed);
        }
        Ok(Client {
            handle,
            _not_send_sync: PhantomData,
        })
    }

    /// Send one raw JSON command line to the core and return its raw JSON
    /// response. The low-level escape hatch beneath the typed methods.
    ///
    /// # Errors
    /// Returns [`Error`] if the command contains an interior NUL, a required
    /// symbol is missing, or the core returns a null response.
    pub fn process(&self, command: &str) -> Result<String, Error> {
        let c_cmd = CString::new(command).map_err(|_| Error::NulInString)?;
        self.invoke(|lib| {
            let process = unsafe {
                symbol::<unsafe extern "C" fn(StateHandle, *const c_char) -> *mut c_char>(
                    lib,
                    b"aletheia_process\0",
                )
            }?;
            Ok(unsafe { process(self.handle, c_cmd.as_ptr()) })
        })
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
        dbc::decode_parsed_dbc(&raw)
    }

    /// Export the currently-loaded DBC as a typed [`Dbc`] document (the core's
    /// canonical-JSON form). Call after a successful `parse_dbc_text` /
    /// `parse_dbc`.
    ///
    /// # Errors
    /// [`Error::Core`] if no DBC is loaded, or [`Error::Protocol`] on an
    /// unexpected response.
    pub fn format_dbc(&self) -> Result<Dbc, Error> {
        let raw = self.invoke(|lib| {
            let f = unsafe {
                symbol::<unsafe extern "C" fn(StateHandle) -> *mut c_char>(
                    lib,
                    b"aletheia_format_dbc\0",
                )
            }?;
            Ok(unsafe { f(self.handle) })
        })?;
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
        dbc::decode_parsed_dbc(&raw)
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
        response::decode_ack_or_success(&raw)
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
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<StreamLifecycleFn>(lib, b"aletheia_start_stream\0") }?;
            Ok(unsafe { f(self.handle) })
        })?;
        response::decode_ack_or_success(&raw)
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
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        let (brs_p, brs_v) = encode_opt_bool(brs);
        let (esi_p, esi_v) = encode_opt_bool(esi);
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<SendFrameFn>(lib, b"aletheia_send_frame\0") }?;
            Ok(unsafe {
                f(
                    self.handle,
                    ts.micros(),
                    id.value(),
                    ext,
                    dlc.value(),
                    data.as_ptr(),
                    len,
                    brs_p,
                    brs_v,
                    esi_p,
                    esi_v,
                )
            })
        })?;
        response::decode_frame(&raw)
    }

    /// Send a CAN error event (no ID, no payload) to the active stream.
    ///
    /// # Errors
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn send_error(&self, ts: Timestamp) -> Result<(), Error> {
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<SendErrorFn>(lib, b"aletheia_send_error\0") }?;
            Ok(unsafe { f(self.handle, ts.micros()) })
        })?;
        response::decode_ack_or_success(&raw)
    }

    /// Send a CAN remote frame event (ID, no payload) to the active stream.
    ///
    /// # Errors
    /// [`Error::Core`] / [`Error::Protocol`].
    pub fn send_remote(&self, ts: Timestamp, id: CanId) -> Result<(), Error> {
        let ext = u8::from(id.is_extended());
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<SendRemoteFn>(lib, b"aletheia_send_remote\0") }?;
            Ok(unsafe { f(self.handle, ts.micros(), id.value(), ext) })
        })?;
        response::decode_ack_or_success(&raw)
    }

    /// End the stream and collect the final per-property verdicts and warnings
    /// (binary FFI).
    ///
    /// # Errors
    /// [`Error::Core`] if no stream is active, else [`Error`].
    pub fn end_stream(&self) -> Result<StreamResult, Error> {
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<StreamLifecycleFn>(lib, b"aletheia_end_stream\0") }?;
            Ok(unsafe { f(self.handle) })
        })?;
        response::decode_stream(&raw)
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
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        let raw = self.invoke(|lib| {
            let f = unsafe { symbol::<ExtractFn>(lib, b"aletheia_extract_signals\0") }?;
            Ok(unsafe {
                f(
                    self.handle,
                    id.value(),
                    ext,
                    dlc.value(),
                    data.as_ptr(),
                    len,
                )
            })
        })?;
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
        let num_signals = u32::try_from(indices.len())
            .map_err(|_| Error::Validation("too many signal injections".to_string()))?;
        let mut out = vec![0u8; dlc.to_bytes()];
        let lib = library()?;
        let build = unsafe { symbol::<BuildFrameFn>(lib, b"aletheia_build_frame_bin\0") }?;
        let free_str =
            unsafe { symbol::<unsafe extern "C" fn(*mut c_char)>(lib, b"aletheia_free_str\0") }?;
        let mut out_err: *mut c_char = std::ptr::null_mut();
        let out_ptr = if out.is_empty() {
            std::ptr::null_mut()
        } else {
            out.as_mut_ptr()
        };
        // SAFETY: `out` is `dlc.to_bytes()` long (what the core writes); the
        // parallel arrays all share `indices.len()`; `out_err` is an out-param.
        let status = unsafe {
            build(
                self.handle,
                message.id,
                u8::from(message.extended),
                dlc.value(),
                num_signals,
                slice_ptr(&indices),
                slice_ptr(&nums),
                slice_ptr(&dens),
                out_ptr,
                &mut out_err,
            )
        };
        check_buffer_status(status, out_err, &free_str, "build_frame")?;
        Ok(out)
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
        let frame_n = frame_len(frame)?;
        let (indices, nums, dens) = resolve_signal_indices(message, signals)?;
        let num_signals = u32::try_from(indices.len())
            .map_err(|_| Error::Validation("too many signal injections".to_string()))?;
        let mut out = vec![0u8; dlc.to_bytes()];
        let lib = library()?;
        let update = unsafe { symbol::<UpdateFrameFn>(lib, b"aletheia_update_frame_bin\0") }?;
        let free_str =
            unsafe { symbol::<unsafe extern "C" fn(*mut c_char)>(lib, b"aletheia_free_str\0") }?;
        let mut out_err: *mut c_char = std::ptr::null_mut();
        let out_ptr = if out.is_empty() {
            std::ptr::null_mut()
        } else {
            out.as_mut_ptr()
        };
        // SAFETY: as `build_frame`, plus `frame`/`frame_n` describe the input bytes.
        let status = unsafe {
            update(
                self.handle,
                message.id,
                u8::from(message.extended),
                dlc.value(),
                slice_ptr(frame),
                frame_n,
                num_signals,
                slice_ptr(&indices),
                slice_ptr(&nums),
                slice_ptr(&dens),
                out_ptr,
                &mut out_err,
            )
        };
        check_buffer_status(status, out_err, &free_str, "update_frame")?;
        Ok(out)
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
        for f in frames {
            match self.send_frame(f.timestamp, f.id, f.dlc, &f.data, f.brs, f.esi) {
                Ok(resp) => out.push(resp),
                Err(e) => return (out, Some(e)),
            }
        }
        (out, None)
    }

    /// Resolve `aletheia_free_str` up front, run `call` to obtain a GHC-allocated
    /// response pointer, then copy it out and free it via the RAII [`Response`].
    fn invoke(
        &self,
        call: impl FnOnce(&'static Library) -> Result<*mut c_char, Error>,
    ) -> Result<String, Error> {
        let lib = library()?;
        // Resolve the deallocator BEFORE the call so a `.so` missing
        // `aletheia_free_str` fails here instead of leaking in Response::drop.
        let free_str =
            unsafe { symbol::<unsafe extern "C" fn(*mut c_char)>(lib, b"aletheia_free_str\0") }?;
        let ptr = call(lib)?;
        if ptr.is_null() {
            return Err(Error::NullResponse);
        }
        Ok(Response { ptr, free_str }.into_string())
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        if let Ok(lib) = library() {
            // SAFETY: `aletheia_close` is `void aletheia_close(StateHandle)`.
            if let Ok(close) =
                unsafe { symbol::<unsafe extern "C" fn(StateHandle)>(lib, b"aletheia_close\0") }
            {
                unsafe { close(self.handle) };
            }
        }
    }
}

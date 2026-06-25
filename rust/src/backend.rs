// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The backend dependency-injection seam.
//!
//! [`Backend`] is the FFI-boundary abstraction the [`Client`](crate::Client) is
//! built on: every raw operation the client performs against the verified core
//! goes through one of its methods. [`FfiBackend`] is the production
//! implementation (loads `libaletheia-ffi.so`, owns one `StreamState`);
//! [`MockBackend`](crate::MockBackend) is a test double that records the requests
//! it received and replays canned responses — no `.so` required.
//!
//! # Idiomatic divergence from the Go / C++ / Python seams
//!
//! The peer bindings put `init`/`close` in the interface and thread a raw
//! `void* state` through every method (a stateless-strategy shape that mirrors
//! the C ABI). Rust uses **RAII** instead: [`FfiBackend`] owns its session handle
//! and closes it in [`Drop`], so the trait never traffics in a raw pointer and a
//! test double needs no fake handle. Same feature (a substitutable FFI boundary),
//! Rust-idiomatic form — one backend owns one session; multiple independent
//! sessions come from multiple [`Client`](crate::Client)s.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::sync::OnceLock;

use libloading::{Library, Symbol};

use crate::error::Error;
use crate::log::{events, LogField, LogLevel, LogRecord, LogValue, Logger};
use crate::types::{CanId, Dlc, Rational, Timestamp};

/// Opaque pointer to the `StreamState` owned by the core (from `aletheia_init`).
pub(crate) type StateHandle = *mut c_void;

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

/// The FFI-boundary abstraction injected into a [`Client`](crate::Client).
///
/// Each method is one raw operation against the verified core: JSON-command ops
/// return the response as a `String`; the binary fast-path frame ops return the
/// core's JSON response `String`; the build/update ops return the raw payload
/// `Vec<u8>`. The [`Client`](crate::Client) keeps every typed concern —
/// validation, response decoding, violation enrichment, logging — on its side;
/// the backend only marshals arguments and performs the call.
///
/// Unlike the Go / C++ / Python seams there is no `init`/`close`/`state`: a
/// backend owns its own session for its lifetime (RAII). The trait is public and
/// open, so callers can supply their own doubles in addition to
/// [`MockBackend`](crate::MockBackend).
pub trait Backend {
    /// Send one raw JSON command line and return the raw JSON response.
    ///
    /// # Errors
    /// Backend-specific: a transport failure, an interior NUL in `input`, or a
    /// null response from the core.
    fn process(&self, input: &str) -> Result<String, Error>;

    /// Send one CAN frame via the binary fast path; return the core's JSON
    /// response. `brs`/`esi` are `None` for CAN 2.0B frames.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn send_frame_binary(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<String, Error>;

    /// Send a CAN error event (no ID, no payload); return the core's JSON response.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn send_error_binary(&self, ts: Timestamp) -> Result<String, Error>;

    /// Send a CAN remote frame event (ID, no payload); return the JSON response.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn send_remote_binary(&self, ts: Timestamp, id: CanId) -> Result<String, Error>;

    /// Begin the monitoring stream; return the core's JSON response.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn start_stream_binary(&self) -> Result<String, Error>;

    /// End the stream and return the final per-property verdicts as JSON.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn end_stream_binary(&self) -> Result<String, Error>;

    /// Export the loaded DBC as canonical JSON.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn format_dbc_binary(&self) -> Result<String, Error>;

    /// Extract every signal value from one frame; return the JSON response.
    ///
    /// # Errors
    /// Backend-specific transport / protocol failure.
    fn extract_signals_binary(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<String, Error>;

    /// Build a frame payload from named signal injections; return the
    /// `dlc`-byte payload.
    ///
    /// # Errors
    /// Backend-specific: the core rejecting a value, or a marshalling failure.
    fn build_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error>;

    /// Update signals inside an existing `frame` payload; return the new payload.
    ///
    /// # Errors
    /// Backend-specific: the core rejecting a value, or a marshalling failure.
    fn update_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        frame: &[u8],
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error>;
}

/// Borrowed view of the parallel signal-injection arrays the build/update FFI
/// expects: each `indices[i]` signal is set to the rational `nums[i]/dens[i]`.
/// The three slices share a length. Bundling them keeps the seam methods within
/// the argument-count limit and mirrors the C++ `SignalInjection` block.
#[derive(Clone, Copy)]
pub struct SignalInjection<'a> {
    /// Positional index of each target signal in its message's signal list.
    pub indices: &'a [u32],
    /// Numerator of each injected value.
    pub nums: &'a [i64],
    /// Denominator of each injected value.
    pub dens: &'a [i64],
}

/// Resolve the shared-library path: the `ALETHEIA_LIB` override, else the
/// conventional name (resolved by the dynamic loader's search path).
fn lib_path() -> String {
    std::env::var("ALETHEIA_LIB").unwrap_or_else(|_| "libaletheia-ffi.so".to_string())
}

/// Process-global handle to the loaded library. The GHC RTS owns threads for the
/// process lifetime, so the library is loaded once and never unloaded.
static LIB: OnceLock<Library> = OnceLock::new();
static RTS_INIT: OnceLock<Result<(), Error>> = OnceLock::new();
/// The RTS core spec the first init latched (`None` = GHC defaults, `Some(k)` =
/// `-N<k>`). A later init requesting a different spec is a no-op + a warning.
static RTS_SPEC: OnceLock<Option<u32>> = OnceLock::new();

pub(crate) fn library() -> Result<&'static Library, Error> {
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
/// `OnceLock<Result<…>>` so a second backend after a failed first one fails
/// identically rather than silently masking a broken `.so`.
fn ensure_rts(
    lib: &Library,
    cores: Option<u32>,
    logger: Option<&dyn Logger>,
    min_level: LogLevel,
) -> Result<(), Error> {
    // The first init's spec wins; a later mismatching request is a no-op + warn.
    let latched = *RTS_SPEC.get_or_init(|| cores);
    if latched != cores {
        if let Some(lg) = logger {
            if LogLevel::Warn >= min_level {
                let requested = spec_str(cores);
                let active = spec_str(latched);
                lg.log(&LogRecord {
                    level: LogLevel::Warn,
                    event: events::RTS_CORES_MISMATCH,
                    fields: &[
                        LogField::new("requested", LogValue::Str(&requested)),
                        LogField::new("active", LogValue::Str(&active)),
                    ],
                });
            }
        }
    }
    RTS_INIT.get_or_init(|| init_rts(lib, latched)).clone()
}

/// Ensure the GHC RTS is initialised for a library call that may run *before* any
/// [`FfiBackend`] exists — the rational renderer reaches this
/// when a [`Check`](crate::check::Check) built under a
/// [`MockBackend`](crate::MockBackend) renders its `condition_desc()`, or when
/// `set_properties` runs on a mock. The renderer is a MAlonzo foreign export, so
/// calling it with the RTS down is undefined behaviour, not a catchable error.
///
/// Delegates to [`ensure_rts`] — the single one-shot init — with the default spec
/// (no backend `-N`, no logger). GHC's `hs_init` is one-shot and fixes `-N` for the
/// process, so whichever caller runs first latches the spec: a real `FfiBackend`
/// (created before it processes anything) always wins its `-N`; a renderer-first
/// call uses GHC defaults, which is harmless because rendering a single rational is
/// not parallel work. Mirrors the C++ (`rational_renderer.cpp`) and Python
/// (`_enrichment.py`) renderers, which share the backend's RTS init the same way.
fn ensure_rts_for_render(lib: &'static Library) -> Result<(), Error> {
    ensure_rts(lib, None, None, LogLevel::Warn)
}

/// Render a [`Rational`] via the verified Agda kernel's `formatℚ` (the FFI export
/// `aletheia_format_rational`) — the single source of truth for rational display,
/// byte-identical to the Python / Go / C++ bindings by construction (no local
/// fallback). Lazily loads `libaletheia-ffi.so` and ensures the RTS on first use.
///
/// # Errors
/// [`Error::LibraryLoad`] / [`Error::SymbolMissing`] if the `.so` is not loadable
/// or the export is absent. Once the library is usable the call cannot fail for a
/// well-formed rational: the kernel never emits a zero denominator and the input's
/// denominator is positive by construction, so "render fails" ⟺ "library unusable".
pub(crate) fn format_rational(r: Rational) -> Result<String, Error> {
    type FormatRationalFn = unsafe extern "C" fn(i64, i64) -> *mut c_char;
    let lib = library()?;
    ensure_rts_for_render(lib)?;
    let f = unsafe { symbol::<FormatRationalFn>(lib, b"aletheia_format_rational\0") }?;
    let free_str =
        unsafe { symbol::<unsafe extern "C" fn(*mut c_char)>(lib, b"aletheia_free_str\0") }?;
    // SAFETY: numerator/denominator are plain `i64` the kernel renders; the returned
    // pointer is a GHC-allocated CString released by the `Response` guard.
    let ptr = unsafe { f(r.numerator(), r.denominator()) };
    if ptr.is_null() {
        // Unreachable for a well-formed rational (the kernel never returns null);
        // mirror Python's defensive "0" so the sole real failure stays lib-load.
        return Ok("0".to_string());
    }
    Ok(Response { ptr, free_str }.into_string())
}

/// Human spec for the RTS core count (`default` or `-N<k>`).
fn spec_str(cores: Option<u32>) -> String {
    cores.map_or_else(|| "default".to_string(), |k| format!("-N{k}"))
}

/// Run `hs_init`, either with GHC defaults (`cores = None`) or a leaked
/// `+RTS -N<k> -RTS` argv (`cores = Some(k)`). GHC retains the argv pointers for
/// the process lifetime, so the strings and the array are intentionally leaked.
fn init_rts(lib: &Library, cores: Option<u32>) -> Result<(), Error> {
    // SAFETY: `hs_init` is `void hs_init(int *argc, char ***argv)`.
    let hs_init = unsafe {
        symbol::<unsafe extern "C" fn(*mut c_int, *mut *mut *mut c_char)>(lib, b"hs_init\0")
    }?;
    match cores {
        // NULL/NULL selects GHC default flags.
        None => unsafe { hs_init(std::ptr::null_mut(), std::ptr::null_mut()) },
        Some(k) => {
            // `into_raw` / `Box::leak` deliberately leak: GHC retains argv.
            let argv: Vec<*mut c_char> = vec![
                CString::new("aletheia").expect("no NUL").into_raw(),
                CString::new("+RTS").expect("no NUL").into_raw(),
                CString::new(format!("-N{k}")).expect("no NUL").into_raw(),
                CString::new("-RTS").expect("no NUL").into_raw(),
                std::ptr::null_mut(),
            ];
            let mut argc: c_int = 4;
            let mut argv_ptr = Box::leak(argv.into_boxed_slice()).as_mut_ptr();
            unsafe { hs_init(&mut argc, &mut argv_ptr) };
        }
    }
    Ok(())
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
        let lib = library()?;
        ensure_rts(lib, cores, logger, min_level)?;
        // SAFETY: `aletheia_init` is `StateHandle aletheia_init(void)`.
        let init =
            unsafe { symbol::<unsafe extern "C" fn() -> StateHandle>(lib, b"aletheia_init\0") }?;
        let handle = unsafe { init() };
        if handle.is_null() {
            return Err(Error::InitFailed);
        }
        Ok(FfiBackend { handle })
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

impl Backend for FfiBackend {
    fn process(&self, input: &str) -> Result<String, Error> {
        let c_cmd = CString::new(input).map_err(|_| Error::NulInString)?;
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

    fn send_frame_binary(
        &self,
        ts: Timestamp,
        id: CanId,
        dlc: Dlc,
        data: &[u8],
        brs: Option<bool>,
        esi: Option<bool>,
    ) -> Result<String, Error> {
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        let (brs_p, brs_v) = encode_opt_bool(brs);
        let (esi_p, esi_v) = encode_opt_bool(esi);
        self.invoke(|lib| {
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
        })
    }

    fn send_error_binary(&self, ts: Timestamp) -> Result<String, Error> {
        self.invoke(|lib| {
            let f = unsafe { symbol::<SendErrorFn>(lib, b"aletheia_send_error\0") }?;
            Ok(unsafe { f(self.handle, ts.micros()) })
        })
    }

    fn send_remote_binary(&self, ts: Timestamp, id: CanId) -> Result<String, Error> {
        let ext = u8::from(id.is_extended());
        self.invoke(|lib| {
            let f = unsafe { symbol::<SendRemoteFn>(lib, b"aletheia_send_remote\0") }?;
            Ok(unsafe { f(self.handle, ts.micros(), id.value(), ext) })
        })
    }

    fn start_stream_binary(&self) -> Result<String, Error> {
        self.invoke(|lib| {
            let f = unsafe { symbol::<StreamLifecycleFn>(lib, b"aletheia_start_stream\0") }?;
            Ok(unsafe { f(self.handle) })
        })
    }

    fn end_stream_binary(&self) -> Result<String, Error> {
        self.invoke(|lib| {
            let f = unsafe { symbol::<StreamLifecycleFn>(lib, b"aletheia_end_stream\0") }?;
            Ok(unsafe { f(self.handle) })
        })
    }

    fn format_dbc_binary(&self) -> Result<String, Error> {
        self.invoke(|lib| {
            let f = unsafe {
                symbol::<unsafe extern "C" fn(StateHandle) -> *mut c_char>(
                    lib,
                    b"aletheia_format_dbc\0",
                )
            }?;
            Ok(unsafe { f(self.handle) })
        })
    }

    fn extract_signals_binary(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<String, Error> {
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        self.invoke(|lib| {
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
        })
    }

    fn build_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        let num_signals = u32::try_from(signals.indices.len())
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
                id,
                u8::from(extended),
                dlc.value(),
                num_signals,
                slice_ptr(signals.indices),
                slice_ptr(signals.nums),
                slice_ptr(signals.dens),
                out_ptr,
                &mut out_err,
            )
        };
        check_buffer_status(status, out_err, &free_str, "build_frame")?;
        Ok(out)
    }

    fn update_frame_bin(
        &self,
        id: u32,
        extended: bool,
        dlc: Dlc,
        frame: &[u8],
        signals: SignalInjection<'_>,
    ) -> Result<Vec<u8>, Error> {
        let frame_n = frame_len(frame)?;
        let num_signals = u32::try_from(signals.indices.len())
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
        // SAFETY: as `build_frame_bin`, plus `frame`/`frame_n` describe the input bytes.
        let status = unsafe {
            update(
                self.handle,
                id,
                u8::from(extended),
                dlc.value(),
                slice_ptr(frame),
                frame_n,
                num_signals,
                slice_ptr(signals.indices),
                slice_ptr(signals.nums),
                slice_ptr(signals.dens),
                out_ptr,
                &mut out_err,
            )
        };
        check_buffer_status(status, out_err, &free_str, "update_frame")?;
        Ok(out)
    }
}

impl Drop for FfiBackend {
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

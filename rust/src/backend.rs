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
use serde_json::Value;

use crate::error::Error;
use crate::log::{events, LogField, LogLevel, LogRecord, LogValue, Logger};
use crate::response::rational_from_value;
use crate::types::{CanId, Dlc, Rational, Timestamp};

/// Opaque pointer to the `StreamState` owned by the core (from `aletheia_init`).
pub(crate) type StateHandle = *mut c_void;

/// CAN-FD's largest payload; frames longer than this are rejected before the FFI.
const MAX_FRAME_BYTES: usize = 64;

// Runtime GHC RTS parameters — SSOT: docs/RESOURCE_BUDGETS.yaml (runtime
// block); mirrored here verbatim.  Parity with the SSOT is enforced by
// tools/check_rts_runtime.py (a run_ci gate) and the `rts_params` test module
// at the bottom of this file.
//
// CONTAINMENT-BY-ABORT contract: the heap cap does NOT yield a recoverable
// error.  The loaded kernel's GHC RTS has no heap limit by default, so a
// runaway allocation exhausts host memory and the OOM killer takes the whole
// machine down.  With the cap in place the same runaway trips GHC's
// heap-overflow check and the foreign-export wrapper aborts the PROCESS
// (`aletheia: aletheia_process: Return code (4) not ok`).  There is no
// catchable error and no partial result — the host survives, the process does
// not.  A containment bound with measured headroom (heaviest kernel working
// set observed ~1.5 GiB), never a tuned working-set budget.

/// Default -M heap cap emitted into the RTS argv (see [`build_rts_argv`]).
const RTS_HEAP_CAP_FLAG: &str = "-M3G";
/// GHC capability count for single-bus monitoring; a `-N` flag is emitted only
/// when a caller requests more.
const RTS_DEFAULT_CORES: u32 = 1;
/// The GHC entry point that starts the RTS.  Plain `hs_init` cannot carry the
/// `-M` cap under the `.so`'s link-time RtsOptsSafeOnly (it aborts at init with
/// "Most RTS options are disabled"); `hs_init_with_rtsopts` honours the full
/// flag set.  Same C signature (`void(int*, char***)`), so the switch is a pure
/// string change.
const RTS_INIT_SYMBOL: &str = "hs_init_with_rtsopts";
/// Environment variable whose whitespace-split flags are appended after the cap
/// (and after an optional `-N`), so a caller `-M` wins (the RTS honours the
/// last occurrence).
const RTS_OVERRIDE_ENV: &str = "ALETHEIA_RTS_OPTS";

/// Assemble the argv passed to `hs_init_with_rtsopts`, per the SSOT argv_order:
/// `{progname, +RTS, heap_cap, -N<k> iff k>1, override flags, -RTS}`.  The cap
/// is ALWAYS present, so the host is contained regardless of the requested core
/// count.  Pure (no FFI, no env read — `override_opts` is passed in), so it is
/// unit-testable and the parity test can drive it directly.
fn build_rts_argv(cores: Option<u32>, override_opts: &str) -> Vec<String> {
    let mut argv = vec![
        "aletheia".to_owned(),
        "+RTS".to_owned(),
        RTS_HEAP_CAP_FLAG.to_owned(),
    ];
    if let Some(k) = cores {
        if k > RTS_DEFAULT_CORES {
            argv.push(format!("-N{k}"));
        }
    }
    argv.extend(override_opts.split_whitespace().map(str::to_owned));
    argv.push("-RTS".to_owned());
    argv
}

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
// Binary extraction (the hot path): the core allocates the response buffer and
// returns it via `out_buf` / `out_size`; the caller copies it out and frees it
// with `aletheia_free_buf`. Status/`out_err` follow the build_frame convention.
type ExtractBinFn = unsafe extern "C" fn(
    StateHandle,
    u32,              // canId
    u8,               // extended
    u8,               // dlc
    *const u8,        // data
    u8,               // dataLen
    *mut *mut u8,     // out_buf (callee-allocated)
    *mut u32,         // out_size
    *mut *mut c_char, // out_err
) -> i8;
type FreeBufFn = unsafe extern "C" fn(*mut u8);
type ProcessFn = unsafe extern "C" fn(StateHandle, *const c_char) -> *mut c_char;
type FormatDbcFn = unsafe extern "C" fn(StateHandle) -> *mut c_char;
type FormatRationalFn = unsafe extern "C" fn(i64, i64) -> *mut c_char;
type ParseDecimalFn = unsafe extern "C" fn(*const c_char) -> *mut c_char;
type InitFn = unsafe extern "C" fn() -> StateHandle;
type CloseFn = unsafe extern "C" fn(StateHandle);
type FreeStrFn = unsafe extern "C" fn(*mut c_char);
type HsInitFn = unsafe extern "C" fn(*mut c_int, *mut *mut *mut c_char);
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

    /// Extract every signal value from one frame, returning the packed BINARY
    /// buffer (the hot path — no JSON serialize/parse). The default returns
    /// [`Error::BinaryPathUnsupported`], signalling the caller to fall back to
    /// [`Backend::extract_signals_binary`] (the JSON path); a backend without
    /// real FFI (e.g. a mock) therefore needs no impl. `FfiBackend` overrides
    /// it. The buffer layout is decoded by `response::decode_extraction_bin`.
    ///
    /// # Errors
    /// [`Error::BinaryPathUnsupported`] by default; a real FFI backend returns
    /// [`Error::Validation`] / [`Error::Protocol`] on a bad payload or wire fault.
    fn extract_signals_bin(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<Vec<u8>, Error> {
        let _ = (id, dlc, data);
        Err(Error::BinaryPathUnsupported)
    }

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

/// Every C ABI export the binding calls, resolved once per process.
///
/// Re-running `dlsym` on every call put two lookups on the per-frame hot path
/// (the op symbol + `aletheia_free_str`); this table pays them exactly once.
/// Each field is a `Symbol<'static, _>` borrowing the process-global [`LIB`]:
/// the `Library` lives in a `static OnceLock` and is never unloaded, so the
/// `'static` borrow is honest and each fn pointer stays type-tied to the
/// mapping that backs it — no `Symbol::into_raw` / raw-pointer step needed.
pub(crate) struct Symbols {
    process: Symbol<'static, ProcessFn>,
    send_frame: Symbol<'static, SendFrameFn>,
    send_error: Symbol<'static, SendErrorFn>,
    send_remote: Symbol<'static, SendRemoteFn>,
    start_stream: Symbol<'static, StreamLifecycleFn>,
    end_stream: Symbol<'static, StreamLifecycleFn>,
    format_dbc: Symbol<'static, FormatDbcFn>,
    extract_signals: Symbol<'static, ExtractFn>,
    extract_signals_bin: Symbol<'static, ExtractBinFn>,
    free_buf: Symbol<'static, FreeBufFn>,
    build_frame: Symbol<'static, BuildFrameFn>,
    update_frame: Symbol<'static, UpdateFrameFn>,
    format_rational: Symbol<'static, FormatRationalFn>,
    parse_decimal: Symbol<'static, ParseDecimalFn>,
    init: Symbol<'static, InitFn>,
    close: Symbol<'static, CloseFn>,
    free_str: Symbol<'static, FreeStrFn>,
    hs_init: Symbol<'static, HsInitFn>,
}

impl Symbols {
    /// Resolve every export, failing with the missing symbol's name if the
    /// `.so` lacks one — at construction, not on the Nth call against a stale
    /// library (the exports move together; `check-ffi-exports` pins the set).
    fn resolve(lib: &'static Library) -> Result<Self, Error> {
        // SAFETY: each type argument is that export's exact C ABI signature,
        // matching haskell-shim/src/AletheiaFFI.hs (see the aliases above).
        unsafe {
            Ok(Symbols {
                process: symbol::<ProcessFn>(lib, b"aletheia_process\0")?,
                send_frame: symbol::<SendFrameFn>(lib, b"aletheia_send_frame\0")?,
                send_error: symbol::<SendErrorFn>(lib, b"aletheia_send_error\0")?,
                send_remote: symbol::<SendRemoteFn>(lib, b"aletheia_send_remote\0")?,
                start_stream: symbol::<StreamLifecycleFn>(lib, b"aletheia_start_stream\0")?,
                end_stream: symbol::<StreamLifecycleFn>(lib, b"aletheia_end_stream\0")?,
                format_dbc: symbol::<FormatDbcFn>(lib, b"aletheia_format_dbc\0")?,
                extract_signals: symbol::<ExtractFn>(lib, b"aletheia_extract_signals\0")?,
                extract_signals_bin: symbol::<ExtractBinFn>(
                    lib,
                    b"aletheia_extract_signals_bin\0",
                )?,
                free_buf: symbol::<FreeBufFn>(lib, b"aletheia_free_buf\0")?,
                build_frame: symbol::<BuildFrameFn>(lib, b"aletheia_build_frame_bin\0")?,
                update_frame: symbol::<UpdateFrameFn>(lib, b"aletheia_update_frame_bin\0")?,
                format_rational: symbol::<FormatRationalFn>(lib, b"aletheia_format_rational\0")?,
                parse_decimal: symbol::<ParseDecimalFn>(lib, b"aletheia_parse_decimal\0")?,
                init: symbol::<InitFn>(lib, b"aletheia_init\0")?,
                close: symbol::<CloseFn>(lib, b"aletheia_close\0")?,
                free_str: symbol::<FreeStrFn>(lib, b"aletheia_free_str\0")?,
                // NUL-terminate the mirrored RTS_INIT_SYMBOL for dlsym.  Plain
                // hs_init cannot carry the -M cap under RtsOptsSafeOnly.
                hs_init: symbol::<HsInitFn>(lib, format!("{RTS_INIT_SYMBOL}\0").as_bytes())?,
            })
        }
    }
}

/// Process-global symbol table (see [`Symbols`]). Latched separately from
/// [`LIB`] so both caches share the only-success-latches rule.
static SYMBOLS: OnceLock<Symbols> = OnceLock::new();

/// The cached symbol table, resolving it on first use.
///
/// Mirrors [`library`]'s non-latching shape: resolution runs *outside* a
/// `get_or_init`, so a failure is returned to the caller and nothing is cached
/// — only a fully successful resolution is latched. A library-*load* failure
/// (unloadable `.so`) is therefore retried on the next call, so correcting
/// `ALETHEIA_LIB` before any successful load can still succeed. A library that
/// *loads* but lacks an export fail-fasts with the missing symbol's name — but
/// that library itself stays loaded for the process lifetime (the loaded-once
/// contract on [`LIB`]), so recovering from a wrong-but-loadable path requires
/// a new process.
pub(crate) fn symbols() -> Result<&'static Symbols, Error> {
    if let Some(syms) = SYMBOLS.get() {
        return Ok(syms);
    }
    let syms = Symbols::resolve(library()?)?;
    // If another thread won the race, drop ours and use theirs (both were
    // resolved from the same process-global library, so they are identical).
    let _ = SYMBOLS.set(syms);
    Ok(SYMBOLS.get().expect("SYMBOLS was just set"))
}

/// Initialise the GHC RTS exactly once for the process.
///
/// Mirrors the Go binding: the RTS cannot be re-initialised after `hs_exit`, so
/// we start it once and never tear it down. The outcome is latched in a
/// `OnceLock<Result<…>>` so a second backend after a failed first one fails
/// identically rather than silently masking a broken `.so`.
fn ensure_rts(
    syms: &Symbols,
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
    RTS_INIT.get_or_init(|| init_rts(syms, latched)).clone()
}

/// Test-only: bring the GHC RTS up for unit tests that render. The production
/// renderer no longer self-initialises (an [`FfiBackend`] is the sole initialiser —
/// see [`format_rational`]), so unit tests that exercise the renderer
/// (`check.rs`'s `condition_desc`, `enrich.rs`'s diagnostics) bring it up
/// explicitly. Idempotent via the one-shot [`RTS_INIT`] latch, so a per-test call
/// is cheap after the first. Mirrors the C++ `rts_setup_listener` / Python `rts_up`
/// fixture, which bring the RTS up for their render-dependent mock-backend tests.
#[cfg(test)]
pub(crate) fn ensure_rts_for_test() {
    let syms = symbols().expect("load libaletheia-ffi.so for test (is ALETHEIA_LIB set?)");
    ensure_rts(syms, None, None, LogLevel::Warn).expect("init GHC RTS for test");
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
    // SAFETY: numerator/denominator are plain `i64` the kernel renders; the returned
    // pointer is a GHC-allocated CString released by the `Response` guard.
    let ptr = unsafe { (syms.format_rational)(r.numerator(), r.denominator()) };
    if ptr.is_null() {
        // Unreachable for a well-formed rational (the kernel never returns null and
        // the denominator is positive by construction). Surface a typed error rather
        // than a fabricated value: a null means an ABI/kernel malfunction, and a
        // silent "0" would both violate no-local-fallback and hide the bug.
        return Err(Error::Protocol(
            "aletheia_format_rational returned a null pointer".to_string(),
        ));
    }
    Ok(Response {
        ptr,
        free_str: syms.free_str.clone(),
    }
    .into_string())
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
    let input = CString::new(s)
        .map_err(|_| Error::Validation("decimal literal contains an interior NUL".to_string()))?;
    // SAFETY: `input` is a valid NUL-terminated C string held alive across the
    // call; the returned pointer is a GHC-allocated CString freed by `Response`.
    let ptr = unsafe { (syms.parse_decimal)(input.as_ptr()) };
    if ptr.is_null() {
        return Err(Error::Protocol(
            "aletheia_parse_decimal returned a null pointer".to_string(),
        ));
    }
    decode_decimal_response(
        &Response {
            ptr,
            free_str: syms.free_str.clone(),
        }
        .into_string(),
    )
}

/// Decode the `aletheia_parse_decimal` wire envelope: a bare
/// `{"numerator","denominator"}` on success, or a `{"status":"error",...}`
/// envelope on failure. Branch on `status` BEFORE handing the value to the wire
/// decoder — otherwise the decoder reports an opaque "missing numerator" and
/// masks the precise `decimal_parse_failed` / `decimal_overflow` reason. Maps the
/// error to [`Error::Validation`] (user input), reusing the shared wire decoder
/// [`rational_from_value`] on success (no reimplemented denominator check).
fn decode_decimal_response(json: &str) -> Result<Rational, Error> {
    let value: Value = serde_json::from_str(json)
        .map_err(|e| Error::Protocol(format!("aletheia_parse_decimal: malformed response: {e}")))?;
    if value.get("status").and_then(Value::as_str) == Some("error") {
        let msg = value
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or("invalid decimal literal");
        return Err(Error::Validation(msg.to_string()));
    }
    rational_from_value(&value)
}

/// Human spec for the RTS core count (`default` or `-N<k>`).
fn spec_str(cores: Option<u32>) -> String {
    cores.map_or_else(|| "default".to_string(), |k| format!("-N{k}"))
}

/// Run `hs_init_with_rtsopts` with an argv that ALWAYS carries the containment
/// heap cap ([`build_rts_argv`]), plus `-N<k>` when `cores` exceeds the default
/// and any `ALETHEIA_RTS_OPTS` flags.  Unlike before, the `cores = None` /
/// default arm no longer passes NULL argv (and thus no cap) — the host must be
/// contained no matter the requested core count.  GHC retains the argv pointers
/// for the process lifetime, so the strings and the array are intentionally
/// leaked.
///
/// Infallible today (the init symbol is pre-resolved in [`Symbols`]), but kept
/// `Result`-shaped: [`RTS_INIT`] latches a `Result` so a failed first init
/// would fail every later one identically, and this is its only writer.
fn init_rts(syms: &Symbols, cores: Option<u32>) -> Result<(), Error> {
    let hs_init = &syms.hs_init;
    let override_opts = std::env::var(RTS_OVERRIDE_ENV).unwrap_or_default();
    // `into_raw` / `Box::leak` deliberately leak: GHC retains argv for the
    // process lifetime (no hs_release hook), and the RTS is never torn down.
    let mut argv: Vec<*mut c_char> = build_rts_argv(cores, &override_opts)
        .into_iter()
        .map(|s| {
            CString::new(s)
                .expect("no interior NUL in RTS flag")
                .into_raw()
        })
        .collect();
    let mut argc: c_int = c_int::try_from(argv.len()).expect("RTS argv length fits c_int");
    argv.push(std::ptr::null_mut());
    let mut argv_ptr = Box::leak(argv.into_boxed_slice()).as_mut_ptr();
    // SAFETY: `hs_init` is `void hs_init(int *argc, char ***argv)`; argv is a
    // leaked, NUL-terminated array of leaked C strings, valid for the process.
    unsafe { hs_init(&mut argc, &mut argv_ptr) };
    Ok(())
}

/// RAII guard for a C string the core returned (allocated by the GHC RTS).
///
/// The bytes must be copied out and then released with `aletheia_free_str` —
/// **never** with `CString::from_raw`, which would hand RTS memory to Rust's
/// allocator and corrupt the heap. `free_str` is the pre-resolved deallocator
/// from [`Symbols`] (a cheap `Symbol` clone), keeping this guard's `Drop`
/// infallible.
struct Response {
    ptr: *mut c_char,
    free_str: Symbol<'static, FreeStrFn>,
}

impl Response {
    /// Copy the bytes into an owned `String`; the C buffer is freed on drop.
    fn into_string(self) -> String {
        // SAFETY: `ptr` is a non-null, NUL-terminated C string from the core.
        unsafe { CStr::from_ptr(self.ptr) }
            .to_string_lossy()
            .into_owned()
    }
}

impl Drop for Response {
    fn drop(&mut self) {
        // SAFETY: `ptr` was allocated by the core; `free_str` is its matching
        // deallocator (pre-resolved in `Symbols`, so it is known to exist).
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
    free_str: &Symbol<'static, FreeStrFn>,
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
    /// response pointer, then copy it out and free it via the RAII [`Response`]
    /// (whose deallocator was pre-resolved with everything else — a `.so`
    /// missing `aletheia_free_str` already failed in [`FfiBackend::new`]).
    fn invoke(&self, call: impl FnOnce(&Symbols) -> *mut c_char) -> Result<String, Error> {
        let syms = symbols()?;
        let ptr = call(syms);
        if ptr.is_null() {
            return Err(Error::NullResponse);
        }
        Ok(Response {
            ptr,
            free_str: syms.free_str.clone(),
        }
        .into_string())
    }
}

impl Backend for FfiBackend {
    fn process(&self, input: &str) -> Result<String, Error> {
        let c_cmd = CString::new(input).map_err(|_| Error::NulInString)?;
        // SAFETY: `handle` is the live StreamState this backend owns; `c_cmd`
        // is a valid NUL-terminated C string held alive across the call.
        self.invoke(|syms| unsafe { (syms.process)(self.handle, c_cmd.as_ptr()) })
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
        // SAFETY: `handle` is the live StreamState this backend owns; `data`
        // is valid for `len` bytes (validated ≤ 64 by `frame_len`).
        self.invoke(|syms| unsafe {
            (syms.send_frame)(
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
    }

    fn send_error_binary(&self, ts: Timestamp) -> Result<String, Error> {
        // SAFETY: `handle` is the live StreamState this backend owns.
        self.invoke(|syms| unsafe { (syms.send_error)(self.handle, ts.micros()) })
    }

    fn send_remote_binary(&self, ts: Timestamp, id: CanId) -> Result<String, Error> {
        let ext = u8::from(id.is_extended());
        // SAFETY: `handle` is the live StreamState this backend owns.
        self.invoke(|syms| unsafe { (syms.send_remote)(self.handle, ts.micros(), id.value(), ext) })
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
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        // SAFETY: `handle` is the live StreamState this backend owns; `data`
        // is valid for `len` bytes (validated ≤ 64 by `frame_len`).
        self.invoke(|syms| unsafe {
            (syms.extract_signals)(
                self.handle,
                id.value(),
                ext,
                dlc.value(),
                data.as_ptr(),
                len,
            )
        })
    }

    fn extract_signals_bin(&self, id: CanId, dlc: Dlc, data: &[u8]) -> Result<Vec<u8>, Error> {
        let len = frame_len(data)?;
        let ext = u8::from(id.is_extended());
        let syms = symbols()?;
        let mut out_buf: *mut u8 = std::ptr::null_mut();
        let mut out_size: u32 = 0;
        let mut out_err: *mut c_char = std::ptr::null_mut();
        // SAFETY: `handle` is the live StreamState this backend owns; `data` is
        // valid for `len` bytes (validated ≤ 64 by `frame_len`); out_buf/out_size/
        // out_err are out-params the core writes.
        let status = unsafe {
            (syms.extract_signals_bin)(
                self.handle,
                id.value(),
                ext,
                dlc.value(),
                data.as_ptr(),
                len,
                &mut out_buf,
                &mut out_size,
                &mut out_err,
            )
        };
        check_buffer_status(status, out_err, &syms.free_str, "extract_signals_bin")?;
        // On success the core returns a buffer of exactly `out_size` bytes. The
        // wire always carries at least the 10-byte header, so a null buffer paired
        // with a non-zero size is a protocol violation, NOT an empty result —
        // surface it rather than silently dropping data. (A null buffer with size
        // 0 yields an empty Vec, which decode_extraction_bin then rejects as too
        // short — a truthful error, not a silent success.)
        if out_buf.is_null() {
            if out_size != 0 {
                return Err(Error::Protocol(format!(
                    "extract_signals_bin: null buffer with non-zero size {out_size}"
                )));
            }
            return Ok(Vec::new());
        }
        // Sanity-cap the core-reported size before copying — a PLAUSIBILITY
        // bound, not the wire's theoretical maximum (whose u32-length reason
        // blob would admit a multi-GiB copy from a corrupt size report): the
        // 10-byte header, the maximum u16 count of each fixed-stride section
        // (values 18 B, errors 3 B, absent 2 B), the (nErrors + 1) x u32
        // reason-offsets table, and a generous per-entry reason budget.
        // Kernel-minted reasons are short (bounded signal names + bounded
        // decimal renderings + fixed text — well under 512 B each), so any
        // honest buffer sits far below this cap; a larger reported size is
        // corruption — reject (after freeing) instead of copying an
        // implausible span. Layout: `response::decode_extraction_bin`
        // (canonical source: `Aletheia.Main.Binary`, processExtractBin).
        const MAX_REASON_BYTES_PER_ENTRY: usize = 512;
        const MAX_EXTRACT_BUF: usize = 10
            + (18 + 3 + 2) * (u16::MAX as usize)
            + 4 * (u16::MAX as usize + 1)
            + MAX_REASON_BYTES_PER_ENTRY * (u16::MAX as usize);
        if out_size as usize > MAX_EXTRACT_BUF {
            // SAFETY: `out_buf` was allocated by the core; free it before erroring.
            unsafe { (syms.free_buf)(out_buf) };
            return Err(Error::Protocol(format!(
                "extract_signals_bin: buffer size {out_size} exceeds wire maximum {MAX_EXTRACT_BUF}"
            )));
        }
        // SAFETY: the core set `out_buf` to an `out_size`-byte buffer it allocated
        // (bounded above); copy it out, then return it to the core's allocator.
        let bytes = unsafe { std::slice::from_raw_parts(out_buf, out_size as usize) }.to_vec();
        // SAFETY: `out_buf` was allocated by the core; free it with its allocator.
        unsafe { (syms.free_buf)(out_buf) };
        Ok(bytes)
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
        let syms = symbols()?;
        let mut out_err: *mut c_char = std::ptr::null_mut();
        let out_ptr = if out.is_empty() {
            std::ptr::null_mut()
        } else {
            out.as_mut_ptr()
        };
        // SAFETY: `out` is `dlc.to_bytes()` long (what the core writes); the
        // parallel arrays all share `indices.len()`; `out_err` is an out-param.
        let status = unsafe {
            (syms.build_frame)(
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
        check_buffer_status(status, out_err, &syms.free_str, "build_frame")?;
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
        let syms = symbols()?;
        let mut out_err: *mut c_char = std::ptr::null_mut();
        let out_ptr = if out.is_empty() {
            std::ptr::null_mut()
        } else {
            out.as_mut_ptr()
        };
        // SAFETY: as `build_frame_bin`, plus `frame`/`frame_n` describe the input bytes.
        let status = unsafe {
            (syms.update_frame)(
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
        check_buffer_status(status, out_err, &syms.free_str, "update_frame")?;
        Ok(out)
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

#[cfg(test)]
mod rts_params {
    //! Rust leg of the runtime-RTS parity chain: assert this binding's mirrored
    //! constants equal `docs/RESOURCE_BUDGETS.yaml` (the cross-binding SSOT,
    //! itself enforced against every binding by `tools/check_rts_runtime.py`).
    //! An internal `#[cfg(test)]` module (not a `tests/` integration test) so it
    //! reads the private mirror constants directly — matching how the Python /
    //! Go / C++ mirrors are private to their binding.

    use std::path::Path;

    use yaml_rust2::YamlLoader;

    use super::{
        build_rts_argv, RTS_DEFAULT_CORES, RTS_HEAP_CAP_FLAG, RTS_INIT_SYMBOL, RTS_OVERRIDE_ENV,
    };

    fn ssot() -> yaml_rust2::Yaml {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/RESOURCE_BUDGETS.yaml");
        let text = std::fs::read_to_string(&path).expect("read docs/RESOURCE_BUDGETS.yaml");
        let docs = YamlLoader::load_from_str(&text).expect("parse RESOURCE_BUDGETS.yaml");
        docs[0]["runtime"].clone()
    }

    #[test]
    fn mirror_matches_ssot() {
        let runtime = ssot();
        assert_eq!(
            runtime["heap_cap"]["flag"].as_str(),
            Some(RTS_HEAP_CAP_FLAG),
            "RTS_HEAP_CAP_FLAG drifted from docs/RESOURCE_BUDGETS.yaml runtime.heap_cap.flag"
        );
        assert_eq!(
            runtime["default_cores"]["value"].as_i64(),
            Some(i64::from(RTS_DEFAULT_CORES)),
            "RTS_DEFAULT_CORES drifted from runtime.default_cores.value"
        );
        assert_eq!(
            runtime["init_symbol"].as_str(),
            Some(RTS_INIT_SYMBOL),
            "RTS_INIT_SYMBOL drifted from runtime.init_symbol"
        );
        assert_eq!(
            runtime["heap_cap"]["override_env"].as_str(),
            Some(RTS_OVERRIDE_ENV),
            "RTS_OVERRIDE_ENV drifted from runtime.heap_cap.override_env"
        );
    }

    #[test]
    fn argv_always_carries_the_cap() {
        // Default cores: cap present, no -N.
        assert_eq!(
            build_rts_argv(None, ""),
            vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-RTS"]
        );
        assert_eq!(
            build_rts_argv(Some(1), ""),
            vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-RTS"]
        );
        // Multi-core: -N appended after the cap.
        assert_eq!(
            build_rts_argv(Some(4), ""),
            vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-N4", "-RTS"]
        );
        // Override flags land after the cap (so a caller -M occurs last, wins).
        assert_eq!(
            build_rts_argv(Some(1), "  -M12M   -hT "),
            vec![
                "aletheia",
                "+RTS",
                RTS_HEAP_CAP_FLAG,
                "-M12M",
                "-hT",
                "-RTS"
            ]
        );
    }
}

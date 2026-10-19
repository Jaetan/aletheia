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
use crate::response;
use crate::types::{CanId, Dlc, Timestamp};

mod ffi_backend;

pub(crate) use ffi_backend::{format_rational, parse_decimal, FfiBackend};

/// Opaque pointer to the `StreamState` owned by the core (from `aletheia_init`).
pub(crate) type StateHandle = *mut c_void;

// Runtime GHC RTS parameters — SSOT: docs/RESOURCE_BUDGETS.yaml (runtime
// block); mirrored here verbatim.  Parity with the SSOT is enforced by
// tools/check_rts_runtime.py (a run_ci gate).
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

/// `struct aletheia_frame` (`haskell-shim/include/aletheia.h`): one CAN frame, passed by
/// pointer. The `abi_layout` tests hold its layout to the header's.
#[repr(C)]
struct FfiFrame {
    timestamp: u64,
    data: *const u8,
    can_id: u32,
    extended: u8,
    dlc: u8,
    data_len: u8,
    brs_present: u8,
    brs_value: u8,
    esi_present: u8,
    esi_value: u8,
}

/// `struct aletheia_signal_values`: parallel signal indices and rationals.
#[repr(C)]
struct FfiSignalValues {
    indices: *const u32,
    numerators: *const i64,
    denominators: *const i64,
    count: u32,
}

/// `struct aletheia_buffer`: a binary result and the error the core set.
/// Build and update write into the caller's `data` (`size` bytes, set to the
/// count written); extraction allocates `data` for the caller to free with
/// `aletheia_free_buf`. On failure `err` is a GHC-allocated JSON error
/// envelope the caller frees with `aletheia_free_str`.
#[repr(C)]
struct FfiBuffer {
    data: *mut u8,
    err: *mut c_char,
    size: u32,
}

/// `struct aletheia_rational`: an exact rational.
#[repr(C)]
struct FfiRational {
    numerator: i64,
    denominator: i64,
}

/// `struct aletheia_text`: `size` bytes of UTF-8 from `data`, with no
/// terminating NUL.
#[repr(C)]
struct FfiText {
    data: *const c_char,
    size: usize,
}

impl FfiText {
    /// The text `s` spans, which the kernel reads whole: a NUL among its bytes
    /// is the kernel's to refuse, not the end of the text.
    fn of(s: &str) -> Self {
        Self {
            data: s.as_ptr().cast(),
            size: s.len(),
        }
    }
}

/// `struct aletheia_decimal`: a parsed decimal, or on failure a GHC-allocated
/// JSON error envelope the caller frees with `aletheia_free_str`.
#[repr(C)]
struct FfiDecimal {
    value: FfiRational,
    err: *mut c_char,
}

type SendFrameFn = unsafe extern "C" fn(StateHandle, *const FfiFrame) -> *mut c_char;
type SendErrorFn = unsafe extern "C" fn(StateHandle, *const FfiFrame) -> *mut c_char;
type SendRemoteFn = unsafe extern "C" fn(StateHandle, *const FfiFrame) -> *mut c_char;
type StreamLifecycleFn = unsafe extern "C" fn(StateHandle) -> *mut c_char;
type ExtractFn = unsafe extern "C" fn(StateHandle, *const FfiFrame) -> *mut c_char;
// Binary extraction (the hot path): the core allocates the response buffer
// into the `FfiBuffer`; the caller copies it out and frees it with
// `aletheia_free_buf`. The `i8` status follows the build/update convention.
type ExtractBinFn = unsafe extern "C" fn(StateHandle, *const FfiFrame, *mut FfiBuffer) -> i8;
type FreeBufFn = unsafe extern "C" fn(*mut u8);
type ProcessFn = unsafe extern "C" fn(StateHandle, *const FfiText) -> *mut c_char;
type FormatDbcFn = unsafe extern "C" fn(StateHandle) -> *mut c_char;
type FormatRationalFn = unsafe extern "C" fn(*const FfiRational) -> *mut c_char;
type ParseDecimalFn = unsafe extern "C" fn(*const FfiText, *mut FfiDecimal) -> i8;
type InitFn = unsafe extern "C" fn() -> StateHandle;
type CloseFn = unsafe extern "C" fn(StateHandle);
type FreeStrFn = unsafe extern "C" fn(*mut c_char);
type HsInitFn = unsafe extern "C" fn(*mut c_int, *mut *mut *mut c_char);
type AbiVersionFn = unsafe extern "C" fn() -> u32;

/// `ALETHEIA_ABI_VERSION`: the version of the structures and signatures this
/// crate lays out, which the `abi_layout` tests hold to the header's.
const ABI_VERSION: u32 = 2;
// Build and update share one shape: the caller allocates the output (`dlc`
// bytes) in the `FfiBuffer` and reads an `i8` status, nonzero meaning failure
// with the JSON error envelope in the buffer's `err`.
type FrameBinFn = unsafe extern "C" fn(
    StateHandle,
    *const FfiFrame,
    *const FfiSignalValues,
    *mut FfiBuffer,
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
    /// Backend-specific: a transport failure or a null response from the core.
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
    /// [`Error::Validation`] on a payload whose length is not the DLC's byte
    /// count, [`Error::Core`] on the core's refusal, and [`Error::Protocol`] on
    /// a wire fault.
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
    build_frame: Symbol<'static, FrameBinFn>,
    update_frame: Symbol<'static, FrameBinFn>,
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
        // The version first: a library laid out for another ABI is refused
        // before any other entry is resolved or its runtime is started.
        // SAFETY: `aletheia_abi_version` is `uint32_t aletheia_abi_version(void)`,
        // plain C that needs no runtime.
        let library = unsafe { symbol::<AbiVersionFn>(lib, b"aletheia_abi_version\0")?() };
        if library != ABI_VERSION {
            return Err(Error::AbiMismatch {
                library,
                binding: ABI_VERSION,
            });
        }
        // SAFETY: each type argument is that export's exact C ABI signature,
        // matching haskell-shim/include/aletheia.h (see the aliases above).
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
                build_frame: symbol::<FrameBinFn>(lib, b"aletheia_build_frame_bin\0")?,
                update_frame: symbol::<FrameBinFn>(lib, b"aletheia_update_frame_bin\0")?,
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

/// Copy a C string the core returned, allocated by the GHC RTS, into an owned
/// `String`, then release it with `aletheia_free_str`: **never** with
/// `CString::from_raw`, which would hand RTS memory to Rust's allocator and
/// corrupt the heap. The copy cannot unwind, so the release always follows it.
fn take_response(syms: &Symbols, ptr: *mut c_char) -> String {
    // SAFETY: `ptr` is a non-null, NUL-terminated C string from the core.
    let text = unsafe { CStr::from_ptr(ptr) }
        .to_string_lossy()
        .into_owned();
    // SAFETY: `ptr` was allocated by the core and is not read again;
    // `free_str` is its matching deallocator, pre-resolved in `Symbols`.
    unsafe { (syms.free_str)(ptr) };
    text
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

/// Require a payload of exactly the DLC's byte count, the one length the core
/// accepts, and narrow that length to the frame's `u8`. A length past `u8`
/// equals no DLC's byte count, so it takes the same refusal.
fn frame_len(dlc: Dlc, data: &[u8]) -> Result<u8, Error> {
    let expected = dlc.to_bytes();
    u8::try_from(data.len())
        .ok()
        .filter(|&len| usize::from(len) == expected)
        .ok_or_else(|| {
            Error::validation(format!(
                "payload length {} does not match DLC ({expected} bytes expected)",
                data.len()
            ))
        })
}

/// A plausibility cap on the size the core reports for an extraction buffer,
/// not the wire's theoretical maximum (whose u32-length reason blob would admit
/// a multi-GiB copy from a corrupt size report): the 10-byte header, the
/// maximum u16 count of each fixed-stride section (values 18 B, errors 3 B,
/// absent 2 B), the (nErrors + 1) x u32 reason-offsets table, and a generous
/// per-entry reason budget. Kernel-minted reasons are short (bounded signal
/// names + bounded decimal renderings + fixed text, well under 512 B each), so
/// any honest buffer sits far below this cap. Layout:
/// `response::decode_extraction_bin` (canonical source: `Aletheia.Main.Binary`,
/// processExtractBin).
const MAX_REASON_BYTES_PER_ENTRY: usize = 512;
const MAX_EXTRACT_BUF: usize = 10
    + (18 + 3 + 2) * (u16::MAX as usize)
    + 4 * (u16::MAX as usize + 1)
    + MAX_REASON_BYTES_PER_ENTRY * (u16::MAX as usize);

/// Copy the extraction buffer the core returned and hand it back to the core.
///
/// The wire always carries at least the 10-byte header, so a null buffer paired
/// with a non-zero size is a protocol violation, NOT an empty result: it is
/// surfaced rather than silently dropping data. (A null buffer with size 0
/// yields an empty Vec, which `decode_extraction_bin` then rejects as too
/// short, a truthful error rather than a silent success.) A reported size past
/// [`MAX_EXTRACT_BUF`] is corruption and is rejected, after freeing, instead of
/// copying an implausible span. `free` is called exactly once on every non-null
/// buffer, whichever way the call ends.
///
/// # Safety
/// A non-null `out_buf` must point to `out_size` readable bytes that `free`
/// releases; a null `out_buf` is never dereferenced and never freed.
unsafe fn take_extraction_buffer(
    out_buf: *mut u8,
    out_size: u32,
    free: impl FnOnce(*mut u8),
) -> Result<Vec<u8>, Error> {
    if out_buf.is_null() {
        if out_size != 0 {
            return Err(Error::Protocol(format!(
                "extract_signals_bin: null buffer with non-zero size {out_size}"
            )));
        }
        return Ok(Vec::new());
    }
    if out_size as usize > MAX_EXTRACT_BUF {
        free(out_buf);
        return Err(Error::Protocol(format!(
            "extract_signals_bin: buffer size {out_size} exceeds wire maximum {MAX_EXTRACT_BUF}"
        )));
    }
    // SAFETY: the caller guarantees `out_size` readable bytes at `out_buf`,
    // bounded above; copy them out before the buffer goes back to its owner.
    let bytes = unsafe { std::slice::from_raw_parts(out_buf, out_size as usize) }.to_vec();
    free(out_buf);
    Ok(bytes)
}

/// Interpret a binary-output entry's status: nonzero ⇒ read and free
/// `out_err`, and answer the refusal it carries ([`buffer_refusal`]).
fn check_buffer_status(
    status: i8,
    out_err: *mut c_char,
    syms: &Symbols,
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
    // A nonzero status with non-null `out_err` is a GHC-allocated C string,
    // which `take_response` copies out and releases.
    Err(buffer_refusal(op, &take_response(syms, out_err)))
}

/// Read the JSON error envelope a binary-output entry sets on refusal, the
/// one the JSON path answers with (the core's typed error, or the shim's own
/// `ffi_validation_error`), as the JSON path reads it: [`Error::Core`] with
/// its `code` and `message`, or a typed lift. Anything else in `err` is a
/// wire fault.
fn buffer_refusal(op: &str, json: &str) -> Error {
    match response::parse_object(json) {
        Err(Error::Protocol(e)) => Error::Protocol(format!("{op}: malformed error envelope: {e}")),
        Err(refusal) => refusal,
        Ok(_) => Error::Protocol(format!("{op}: error is not an error envelope: {json}")),
    }
}

#[cfg(test)]
mod rts_argv;

#[cfg(test)]
mod abi_layout;

#[cfg(test)]
mod codec_tests;

#[cfg(test)]
mod frame_entries;

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Rust binding for Aletheia — formally verified CAN frame analysis.
//!
//! Like the Go and C++ bindings, this crate loads the GHC-compiled Agda core
//! `libaletheia-ffi.so` at runtime via `dlopen` (the `libloading` crate) rather
//! than statically linking the GHC RTS + MAlonzo into a non-Haskell binary. The
//! verified logic lives entirely in the shared library; this crate is a thin,
//! memory-safe wrapper over its stable C ABI.
//!
//! This is the tracer-bullet slice. It proves the FFI *lifecycle* — load → RTS
//! init → one `aletheia_process` JSON round-trip → free → close — and the two
//! ownership rules that cgo hides from the Go binding (GHC-allocated return
//! strings; init-the-RTS-once). The typed client surface (validated CAN ID /
//! DLC newtypes, sealed predicate / formula enums, richer `Result` errors) and
//! the binary endpoints land in subsequent slices.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::fmt;
use std::sync::OnceLock;

use libloading::{Library, Symbol};

/// Opaque pointer to the `StreamState` owned by the core (from `aletheia_init`).
type StateHandle = *mut c_void;

/// Errors surfaced by the binding.
///
/// `Clone` lets the process-global RTS-init latch (`RTS_INIT`) replay the first
/// init outcome on every `ensure_rts` call.
#[derive(Debug, Clone)]
pub enum Error {
    /// `libaletheia-ffi.so` could not be loaded (resolved path + underlying message).
    LibraryLoad { path: String, source: String },
    /// A required C ABI symbol was absent from the library.
    SymbolMissing(String),
    /// `aletheia_init` returned a null handle (the RTS did not initialise correctly).
    InitFailed,
    /// The command contained an interior NUL byte and cannot cross the C boundary.
    NulInCommand,
    /// The core returned a null response pointer.
    NullResponse,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::LibraryLoad { path, source } => write!(f, "failed to load {path}: {source}"),
            Error::SymbolMissing(name) => write!(f, "missing FFI symbol: {name}"),
            Error::InitFailed => write!(f, "aletheia_init returned null"),
            Error::NulInCommand => write!(f, "command contained an interior NUL byte"),
            Error::NullResponse => write!(f, "core returned a null response"),
        }
    }
}

impl std::error::Error for Error {}

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
/// we start it once and never tear it down. `hs_init(NULL, NULL)` selects RTS
/// defaults; `+RTS -N<cores> -RTS` tuning lands in a later slice.
fn ensure_rts(lib: &Library) -> Result<(), Error> {
    // Latch the first init outcome process-globally and replay it on every call.
    // A plain `Once` would run the body at most once but could not surface a
    // first-call failure to later callers (it cannot re-run) — masking a broken
    // `.so`. `OnceLock<Result<…>>` stores the outcome (Ok, or the same Err) so a
    // second `Client::new()` after a failed first one fails identically.
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
/// allocator and corrupt the heap. This guard makes the copy-then-free sequence
/// impossible to skip per call site.
/// The signature of `aletheia_free_str`, resolved once in `process()` so the
/// guard's `Drop` is infallible and can never leak by silently skipping a free.
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
        // SAFETY: `ptr` was allocated by the core; `free_str` (resolved up front
        // in process(), so it is known to exist) is its matching deallocator.
        unsafe { (self.free_str)(self.ptr) };
    }
}

/// A client over one `StreamState` in the verified core.
pub struct Client {
    handle: StateHandle,
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
        Ok(Client { handle })
    }

    /// Send one JSON command line to the core and return its JSON response.
    ///
    /// # Errors
    /// Returns [`Error`] if the command contains an interior NUL, a required
    /// symbol is missing, or the core returns a null response.
    pub fn process(&self, command: &str) -> Result<String, Error> {
        let lib = library()?;
        let c_cmd = CString::new(command).map_err(|_| Error::NulInCommand)?;
        // SAFETY: `aletheia_process` is `CString aletheia_process(StateHandle, CString)`.
        let process = unsafe {
            symbol::<unsafe extern "C" fn(StateHandle, *const c_char) -> *mut c_char>(
                lib,
                b"aletheia_process\0",
            )
        }?;
        // Resolve the deallocator BEFORE allocating, so a `.so` missing
        // `aletheia_free_str` fails here instead of leaking in Response::drop.
        let free_str =
            unsafe { symbol::<unsafe extern "C" fn(*mut c_char)>(lib, b"aletheia_free_str\0") }?;
        let ptr = unsafe { process(self.handle, c_cmd.as_ptr()) };
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

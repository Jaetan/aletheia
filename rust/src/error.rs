// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Error type for the Aletheia binding.

use std::fmt;

/// Errors surfaced by the binding.
///
/// `Clone` lets the process-global RTS-init latch (`RTS_INIT`) replay the first
/// init outcome on every `ensure_rts` call, so the source variants must stay
/// clonable — wrapped library / JSON errors are flattened to owned `String`s.
#[derive(Debug, Clone)]
pub enum Error {
    /// `libaletheia-ffi.so` could not be loaded (resolved path + underlying message).
    LibraryLoad { path: String, source: String },
    /// A required C ABI symbol was absent from the library.
    SymbolMissing(String),
    /// `aletheia_init` returned a null handle (the RTS did not initialise correctly).
    InitFailed,
    /// The GHC RTS has not been initialised: a render (a check description, a
    /// formula, or an observed value) was attempted before any `FfiBackend` /
    /// `Client` brought the runtime up. The renderer is *vocal* — it never
    /// self-initialises (that would latch a default `-N` and squander the backend's
    /// bus-count). Distinct from [`Error::Protocol`] (a wire/ABI malfunction) so
    /// callers can tell a local precondition failure from an actual core problem.
    RtsNotInitialized,
    /// A string crossing the C boundary contained an interior NUL byte.
    NulInString,
    /// The core returned a null response pointer.
    NullResponse,
    /// Caller-supplied input was structurally invalid before it reached the core
    /// (e.g. a CAN ID out of range, a non-positive rational denominator, a
    /// `between` predicate with `min > max`, or a formula nested past the limit).
    Validation(String),
    /// The core's JSON response could not be parsed or had an unexpected shape.
    Protocol(String),
    /// The core returned a structured error response. `code` is the machine-
    /// readable wire code from the Agda kernel (e.g. `handler_no_dbc`).
    Core { code: String, message: String },
    /// A per-frame error from a batch send (`send_frames` / `send_frames_iter` /
    /// `send_frames_stream`), tagged with the **0-based index** of the offending
    /// frame so the caller can locate which frame in the batch failed. `source`
    /// is the underlying error for that frame. (The structured analogue of Go's
    /// / C++'s `"frame N: …"` message prefix and Python's `BatchError.frame_index`.)
    Frame { index: usize, source: Box<Error> },
}

impl Error {
    /// Tag a per-frame error with its 0-based batch index. Internal constructor
    /// for the batch-send paths; callers match on [`Error::Frame`].
    pub(crate) fn at_frame(index: usize, source: Error) -> Error {
        Error::Frame {
            index,
            source: Box::new(source),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::LibraryLoad { path, source } => write!(f, "failed to load {path}: {source}"),
            Error::SymbolMissing(name) => write!(f, "missing FFI symbol: {name}"),
            Error::InitFailed => write!(f, "aletheia_init returned null"),
            Error::RtsNotInitialized => write!(
                f,
                "GHC runtime not initialized: create a Client (FfiBackend) before rendering"
            ),
            Error::NulInString => write!(f, "string contained an interior NUL byte"),
            Error::NullResponse => write!(f, "core returned a null response"),
            Error::Validation(msg) => write!(f, "validation error: {msg}"),
            Error::Protocol(msg) => write!(f, "protocol error: {msg}"),
            Error::Core { code, message } => write!(f, "core error [{code}]: {message}"),
            Error::Frame { index, source } => write!(f, "frame {index}: {source}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Frame { source, .. } => Some(source),
            _ => None,
        }
    }
}

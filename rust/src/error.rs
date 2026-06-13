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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::LibraryLoad { path, source } => write!(f, "failed to load {path}: {source}"),
            Error::SymbolMissing(name) => write!(f, "missing FFI symbol: {name}"),
            Error::InitFailed => write!(f, "aletheia_init returned null"),
            Error::NulInString => write!(f, "string contained an interior NUL byte"),
            Error::NullResponse => write!(f, "core returned a null response"),
            Error::Validation(msg) => write!(f, "validation error: {msg}"),
            Error::Protocol(msg) => write!(f, "protocol error: {msg}"),
            Error::Core { code, message } => write!(f, "core error [{code}]: {message}"),
        }
    }
}

impl std::error::Error for Error {}

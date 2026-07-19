// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Error type for the Aletheia binding.

use std::fmt;

use crate::response::ValidationIssue;

/// Errors surfaced by the binding.
///
/// `Clone` lets the process-global RTS-init latch (`RTS_INIT`) replay the first
/// init outcome on every `ensure_rts` call, so the source variants must stay
/// clonable — wrapped library / JSON errors are flattened to owned `String`s.
///
/// Kernel feature work grows this enum (typed refusals lift new kernel error
/// codes into variants), so it is `#[non_exhaustive]`: matches outside this
/// crate carry a `_` arm, and a new variant is not a breaking change. Errors
/// the crate does not lift stay reachable as [`Error::Core`] with the raw
/// wire `code` string.
#[derive(Debug, Clone)]
#[non_exhaustive]
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
    /// readable wire code from the Agda kernel (e.g. `handler_no_dbc`). A
    /// `code == "input_bound_exceeded"` response carrying a well-typed
    /// `bound_kind` / `observed` / `limit` triple is lifted to
    /// [`Error::InputBoundExceeded`] instead of this generic variant, so any
    /// method documented as returning `Error::Core` on a core error may also
    /// return `Error::InputBoundExceeded` when the rejection is a bound violation.
    /// Likewise, a `code == "handler_validation_failed"` response carrying a
    /// well-typed `has_errors` / `issues` payload is lifted to
    /// [`Error::ValidationFailed`].
    Core { code: String, message: String },
    /// The core rejected an input for exceeding a structural bound (nesting
    /// depth, atom count, identifier length, …). This is the typed lift of a
    /// `code == "input_bound_exceeded"` error response that carries the
    /// structured `bound_kind` / `observed` / `limit` triple — the Rust analogue
    /// of Go's `*InputBoundExceededError`, C++'s `InputBoundExceededError`, and
    /// Python's `InputBoundExceededError`. A malformed or partial triple degrades
    /// to [`Error::Core`] rather than surfacing here (matching the peer bindings).
    /// The human-readable message is reconstructed from the triple by [`Display`],
    /// not stored — like Go / C++ / Python, none of which carry the wire message.
    ///
    /// [`Display`]: std::fmt::Display
    InputBoundExceeded {
        /// Machine-readable wire code (always `input_bound_exceeded`).
        code: String,
        /// Which bound was crossed (a `BoundKind` name, e.g. `nesting_depth`).
        bound_kind: String,
        /// The observed value that exceeded the limit.
        observed: u64,
        /// The canonical limit that was exceeded.
        limit: u64,
    },
    /// The core rejected a DBC because structural validation found errors. This
    /// is the typed lift of a `code == "handler_validation_failed"` error
    /// response that carries the structured `has_errors` / `issues` payload
    /// (each issue has the exact element shape of a `validate_dbc` result).
    /// A missing or malformed payload — including any single ill-typed issue
    /// element — degrades to [`Error::Core`] rather than surfacing here
    /// (the same degrade rule as [`Error::InputBoundExceeded`]). Unlike that
    /// variant, the legacy wire `message` is carried unchanged: it is free text
    /// the core composes, not reconstructible from the issues.
    ValidationFailed {
        /// Machine-readable wire code (always `handler_validation_failed`).
        code: String,
        /// The unchanged legacy human-readable message from the core.
        message: String,
        /// `true` if at least one issue is error-severity (decoded from the
        /// wire, never assumed).
        has_errors: bool,
        /// Every issue the validator reported (errors and warnings), in
        /// report order.
        issues: Vec<ValidationIssue>,
    },
    /// `format_dbc_text` refused: the emitted `.dbc` text does not re-parse to
    /// the input DBC. `format_dbc_text` is always strict — it returns text only
    /// when it provably round-trips — so a divergent DBC (e.g. a multi-value
    /// mux) surfaces this typed lift of a `code == "handler_text_roundtrip_failed"`
    /// error response carrying the structured `has_errors` / `issues` payload
    /// (led by the error-severity `text_roundtrip_divergence` issue). Distinct
    /// from [`Error::ValidationFailed`] (a validation failure, not a round-trip
    /// failure) though the wire shape matches. A missing or malformed payload
    /// degrades to [`Error::Core`], the same rule as the peer bindings.
    TextRoundtripFailed {
        /// Machine-readable wire code (always `handler_text_roundtrip_failed`).
        code: String,
        /// The unchanged legacy human-readable message from the core.
        message: String,
        /// `true` if at least one issue is error-severity (decoded from the wire).
        has_errors: bool,
        /// The round-trip diagnostics, led by `text_roundtrip_divergence`.
        issues: Vec<ValidationIssue>,
    },
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
            Error::InputBoundExceeded {
                bound_kind,
                observed,
                limit,
                ..
            } => write!(
                f,
                "input bound exceeded: {bound_kind} {observed} exceeds limit {limit}"
            ),
            Error::ValidationFailed {
                code,
                message,
                issues,
                ..
            } => write!(
                f,
                "core error [{code}]: {message} ({} validation issues)",
                issues.len()
            ),
            Error::TextRoundtripFailed {
                code,
                message,
                issues,
                ..
            } => write!(
                f,
                "core error [{code}]: {message} ({} round-trip issues)",
                issues.len()
            ),
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

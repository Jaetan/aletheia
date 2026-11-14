// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Error type for the Aletheia binding.

use std::fmt;

use crate::response::{ErrorCode, ValidationIssue};

/// Errors surfaced by the binding.
///
/// The error is `Clone`, so the source variants stay clonable: wrapped library /
/// JSON errors are flattened to owned `String`s.
///
/// Kernel feature work grows this enum (typed refusals lift new kernel error
/// codes into variants), so it is `#[non_exhaustive]`: matches outside this
/// crate carry a `_` arm, and a new variant is not a breaking change. Errors
/// the crate does not lift stay reachable as [`Error::Core`] with their
/// [`ErrorCode`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Error {
    /// `libaletheia-ffi.so` could not be loaded (resolved path + underlying message).
    LibraryLoad { path: String, source: String },
    /// A required C ABI symbol was absent from the library.
    SymbolMissing(String),
    /// `aletheia_init` returned a null handle (the RTS did not initialise correctly).
    InitFailed,
    /// The library implements an ABI version other than the one this crate lays
    /// its structures out for, so it is refused before any other entry is
    /// resolved or its runtime is started.
    AbiMismatch { library: u32, binding: u32 },
    /// The GHC runtime has not started: a call into the kernel outside a
    /// session was attempted before [`start_runtime`](crate::start_runtime) or
    /// a `Client` started it. None of them starts it itself, since a start
    /// fixes the core count for the process. `operation` names the call, as
    /// the Go and C++ bindings name it: `rendering` (a check description, a
    /// formula or an observed value, through `aletheia_format_rational`),
    /// `parsing decimals` (`aletheia_parse_decimal`), `building a check` (the
    /// kernel's check of a predicate, formula or check a builder finished,
    /// through `aletheia_check_property`) and `reading a time bound`
    /// (`aletheia_parse_time_bound`).
    /// Distinct from [`Error::Protocol`] (a wire/ABI malfunction) so callers can
    /// tell a local precondition failure from an actual core problem.
    RtsNotInitialized {
        /// The call refused, which the message names after `before`.
        operation: &'static str,
    },
    /// A C entry answered null where it answers a string, read as `{entry}
    /// returned null`, such as `aletheia_process returned null`.
    NullResponse {
        /// The C entry that answered null, as the library exports it.
        entry: &'static str,
    },
    /// A caller-supplied input the binding or the kernel refused as the
    /// caller's own mistake. The binding refuses a CAN ID out of range, a
    /// non-positive denominator given to [`Rational::new`](crate::Rational::new)
    /// and a formula nested past [`MAX_FORMULA_DEPTH`](crate::MAX_FORMULA_DEPTH)
    /// before any call; the kernel refuses a decimal literal its grammar does
    /// not read and, at a builder's end, a check whose `between` minimum is
    /// above its maximum or whose signal name is no identifier. Its
    /// [`Display`](std::fmt::Display) text is `message`, the kernel's when the
    /// kernel refused, after the place [`Error::located`] or
    /// [`Error::located_at`] set; the `code` is a field, not text.
    Validation {
        /// What was refused and why.
        message: String,
        /// The kernel's code when the kernel refused the input
        /// ([`ErrorCode::TextParseFailure`] or [`ErrorCode::TextTrailingInput`]
        /// for a decimal the grammar refuses, [`ErrorCode::HandlerPropertyRefused`]
        /// for a property or a time bound the kernel refuses,
        /// [`ErrorCode::FfiValidationError`] when the shim refused the bytes);
        /// `None` when the binding refused it itself before any call.
        code: Option<ErrorCode>,
        /// Where a loader read the refused number and the key it sat under;
        /// `None` outside a loader.
        located: Option<Box<Located>>,
    },
    /// The core's JSON response could not be parsed or had an unexpected shape.
    Protocol(String),
    /// The core returned a structured error response. `code` is the machine-
    /// readable code the kernel or the shared library wrote (e.g.
    /// [`ErrorCode::HandlerNoDbc`]). A
    /// response carrying a bound refusal's `bound_kind` / `observed` / `limit`
    /// triple is lifted to [`Error::InputBoundExceeded`] instead of this
    /// generic variant, so any method documented as returning `Error::Core` on
    /// a core error may also return `Error::InputBoundExceeded` when the
    /// rejection is a bound violation. Likewise, a `handler_validation_failed`
    /// response is lifted to [`Error::ValidationFailed`] and a
    /// `handler_text_roundtrip_failed` one to [`Error::TextRoundtripFailed`].
    Core { code: ErrorCode, message: String },
    /// The core rejected an input for exceeding a structural bound (nesting
    /// depth, atom count, identifier length, the length of a DBC's lists and
    /// strings, a number's magnitude, …). This is the typed lift of an error
    /// response carrying the `bound_kind` / `observed` / `limit` triple, the
    /// kernel's `message` and, for a bound on a named part of the input, the
    /// `field` it names, each a field of the boxed [`BoundRefusal`]: the Rust
    /// analogue of Go's `*InputBoundExceededError`, C++'s
    /// `InputBoundExceededError`, and Python's `InputBoundExceededError`.
    /// The triple is read whole: a response holding part of it, or a `field`
    /// that is not a string, is an [`Error::Protocol`] naming the place, in
    /// the one form every reply refusal takes. The crate builds this variant
    /// only by that lift, so its text, rendered by [`Display`], is the
    /// kernel's message exactly, after the place [`Error::located`] or
    /// [`Error::located_at`] set.
    ///
    /// [`Display`]: std::fmt::Display
    InputBoundExceeded(Box<BoundRefusal>),
    /// The core rejected a DBC because structural validation found errors. This
    /// is the typed lift of a `code == "handler_validation_failed"` error
    /// response that carries the structured `has_errors` / `issues` payload
    /// (each issue has the exact element shape of a `validate_dbc` result).
    /// A missing or malformed payload, including any single ill-typed issue
    /// element, is an [`Error::Protocol`] naming the place, in the one form
    /// every reply refusal takes. The wire `message` is carried unchanged: it
    /// is free text the core composes, not reconstructible from the issues.
    ValidationFailed {
        /// Machine-readable code (always [`ErrorCode::HandlerValidationFailed`]).
        code: ErrorCode,
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
    /// is an [`Error::Protocol`] naming the place, as for
    /// [`Error::ValidationFailed`] and in the peer bindings.
    TextRoundtripFailed {
        /// Machine-readable code (always [`ErrorCode::HandlerTextRoundtripFailed`]).
        code: ErrorCode,
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
    /// Internal signal: this backend has no binary FFI (e.g. a mock), so the
    /// caller should fall back to the JSON extraction path. The [`Client`] never
    /// surfaces this to callers — it is consumed by the `extract_signals`
    /// fallback and is only observable through a custom [`Backend`] impl. Mirrors
    /// Go's `ErrBinaryPathUnsupported` sentinel.
    ///
    /// [`Client`]: crate::Client
    /// [`Backend`]: crate::Backend
    BinaryPathUnsupported,
}

/// A bound refusal's fields, carried boxed by [`Error::InputBoundExceeded`] so
/// that every `Result<_, Error>` stays small.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRefusal {
    /// Machine-readable code (always [`ErrorCode::InputBoundExceeded`]).
    pub code: ErrorCode,
    /// The kernel's message, which [`Display`](std::fmt::Display) renders
    /// unchanged (e.g. `ParseDBC: senders array: array cardinality 10001
    /// exceeds limit 10000`).
    pub message: String,
    /// Which bound was crossed, one of the [`limits`](crate::limits)
    /// `BOUND_KIND_*` codes (e.g. `nesting_depth`).
    pub bound_kind: String,
    /// The measured value that exceeded the limit, or `u128::MAX` when the
    /// kernel measured more, its message then naming no number.
    pub observed: u128,
    /// The canonical limit that was exceeded.
    pub limit: u128,
    /// The part of the input that crossed the bound, as the kernel names it:
    /// a DBC's `senders array` or `signal factor` on a refusal from
    /// `parse_dbc`, `parse_dbc_text`, `validate_dbc` or `format_dbc_text`,
    /// a decimal's `decimal` from `Rational::from_decimal`, a time bound's
    /// `time bound` from `TimeBound::parse`; `None` for a bound that names
    /// no field, such as the input's length, its nesting depth or an
    /// identifier's length.
    pub field: Option<String>,
    /// Where a loader read the refused number and the key it sat under;
    /// `None` outside a loader.
    pub located: Option<Box<Located>>,
}

/// The place a loader read a refused number, carried boxed by
/// [`Error::Validation`], so that every `Result<_, Error>` stays small, and by
/// a [`BoundRefusal`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Located {
    /// Where the loader read the number: `Check 'C'` for a YAML check named
    /// `C`, `Row 2` for a spreadsheet row.
    pub location: String,
    /// The key or column header the number sat under (`value`, `Factor`);
    /// `None` for a refusal of the place as a whole.
    pub key: Option<String>,
}

impl Error {
    /// A refusal the binding makes itself, before any call reaches the kernel:
    /// [`Error::Validation`] with `message`, no `code` and no location.
    #[must_use]
    pub fn validation(message: impl Into<String>) -> Self {
        Error::Validation {
            message: message.into(),
            code: None,
            located: None,
        }
    }

    /// The same refusal with the place a loader read the refused number:
    /// `location` (`Check 'C'`, `Row 2`) and `key`, the key or column header
    /// it sat under. On [`Error::Validation`] and [`Error::InputBoundExceeded`]
    /// it sets `located` and keeps the kernel's message, code and fields;
    /// every other variant is returned unchanged.
    #[must_use]
    pub fn located(self, location: impl Into<String>, key: impl Into<String>) -> Self {
        self.placed(Located {
            location: location.into(),
            key: Some(key.into()),
        })
    }

    /// The same refusal with the place a loader read it, `location`
    /// (`Check 'C'`, `Row 2`), and no key: a refusal of the place as a whole,
    /// such as a check the kernel refuses where it is built. It sets
    /// `located` as [`Error::located`] does, on the same variants.
    #[must_use]
    pub fn located_at(self, location: impl Into<String>) -> Self {
        self.placed(Located {
            location: location.into(),
            key: None,
        })
    }

    /// The refusal carrying `place`, on the variants that carry one.
    fn placed(mut self, place: Located) -> Self {
        let located = match &mut self {
            Error::Validation { located, .. } => located,
            Error::InputBoundExceeded(refusal) => &mut refusal.located,
            _ => return self,
        };
        *located = Some(Box::new(place));
        self
    }

    /// Where a loader read the refused number (`Check 'C'`, `Row 2`); `None`
    /// for every variant but a located [`Error::Validation`] or
    /// [`Error::InputBoundExceeded`].
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.place().map(|place| place.location.as_str())
    }

    /// The key or column header the refused number sat under (`value`,
    /// `Factor`); `None` wherever [`Error::location`] is `None`, and for a
    /// place [`Error::located_at`] set.
    #[must_use]
    pub fn key(&self) -> Option<&str> {
        self.place().and_then(|place| place.key.as_deref())
    }

    /// The place [`Error::located`] or [`Error::located_at`] set, if any.
    fn place(&self) -> Option<&Located> {
        match self {
            Error::Validation { located, .. } => located.as_deref(),
            Error::InputBoundExceeded(refusal) => refusal.located.as_deref(),
            _ => None,
        }
    }

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
            Error::AbiMismatch { library, binding } => write!(
                f,
                "the library implements ABI version {library}, and this binding needs {binding}"
            ),
            Error::RtsNotInitialized { operation } => write!(
                f,
                "GHC runtime not initialized: call aletheia::start_runtime or build a Client \
                 before {operation}"
            ),
            Error::NullResponse { entry } => write!(f, "{entry} returned null"),
            Error::Validation {
                message, located, ..
            } => write_placed(f, located.as_deref(), message),
            Error::InputBoundExceeded(refusal) => {
                write_placed(f, refusal.located.as_deref(), &refusal.message)
            }
            Error::Protocol(msg) => f.write_str(msg),
            Error::BinaryPathUnsupported => {
                write!(f, "binary extraction path not supported by this backend")
            }
            Error::Core { message, .. } => f.write_str(message),
            Error::ValidationFailed { message, .. }
            | Error::TextRoundtripFailed { message, .. } => f.write_str(message),
            Error::Frame { index, source } => write!(f, "frame {index}: {source}"),
        }
    }
}

/// `message` after the place a loader read the refusal, when one is set.
fn write_placed(f: &mut fmt::Formatter<'_>, place: Option<&Located>, message: &str) -> fmt::Result {
    match place {
        Some(Located {
            location,
            key: Some(key),
        }) => write!(f, "{location}: invalid '{key}': {message}"),
        Some(Located {
            location,
            key: None,
        }) => write!(f, "{location}: {message}"),
        None => f.write_str(message),
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

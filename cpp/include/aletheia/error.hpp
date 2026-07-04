// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/limits.hpp>
#include <aletheia/validation_issue.hpp> // IWYU pragma: export

#include <expected>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia {

enum class ErrorKind {
    Protocol,          // JSON protocol error from Agda core
    Validation,        // DBC structural issues
    State,             // Wrong state (e.g., send_frame when not streaming)
    Ffi,               // Library load / RTS initialization failure
    BinaryUnsupported, // Backend cannot service the binary-path call (use JSON
                       // fallback); mirrors Go's ErrBinaryPathUnsupported sentinel.
    Cancellation,      // std::stop_token requested cancellation; cooperative-at-
                       // FFI-boundaries per docs/architecture/CANCELLATION.md §1.1
                       // — the next FFI call honors the request, an in-flight call
                       // runs to completion. Mirrors Go's wrapped context.Canceled.
    InputBoundExceeded // Adversarial-input bound crossed at a parser surface;
                       // mirrors Python's `InputBoundExceededError` and Go's
                       // `*InputBoundExceededError` (R19 cluster 8 — CPP-D-21.3
                       // cross-binding parity).  Post R19 cluster 14 /
                       // AGDA-C-6.2 consolidation, the wire code is the single
                       // `ErrorCode::InputBoundExceeded`; `bound_kind` from
                       // the structured payload discriminates which bound.
};

/// Machine-readable error codes mirroring the Agda `Error` ADT.
///
/// Each named constant other than `Unknown` maps 1:1 to a string emitted by
/// `errorCode` in `Aletheia.Error` — the Parse / DBC-text / Frame / Route /
/// Handler / Dispatch / Extraction families plus the consolidated top-level
/// `input_bound_exceeded` code (`WithContext` delegates to its inner error).
///
/// `Unknown` is a forward-compatibility sentinel used by
/// `error_code_from_string` when the Agda core returns a code the C++
/// binding does not recognise. In lock-step builds it should never be
/// produced; its presence here is a deliberate escape hatch, not a mirror
/// of any Agda constructor.
enum class ErrorCode {
    Unknown,
    // Parse errors
    ParseMissingField,
    ParseInvalidByteOrder,
    ParseInvalidPresence,
    ParseMissingSigned,
    ParseInvalidSigned,
    ParseNotAnObject,
    ParseExtCanIdOutOfRange,
    ParseStdCanIdOutOfRange,
    ParseDefaultCanIdOutOfRange,
    ParseInvalidDlcBytes,
    ParseRootNotObject,
    ParseMissingSignalName,
    ParseSignalBitLengthZero,
    ParseSignalOverflowsFrame,
    ParseSignalMsbBelowBitLength,
    ParseInvalidKind,
    ParseNonTerminatingRational,
    ParseInvalidIdentifier,
    ParseNonIntegerMultiplexValue,
    // DBC text parse errors
    DBCTextParseFailure,
    DBCTextTrailingInput,
    DBCTextAttributeRefinementFailed,
    // Frame errors
    FrameSignalNotFound,
    FrameSignalIndexOob,
    FrameInjectionFailed,
    FrameSignalsOverlap,
    FrameCanIdNotFound,
    FrameCanIdMismatch,
    FrameSignalValueOutOfBounds,
    // Top-level adversarial-input bound (consolidated 2026-05-11 per
    // R19 cluster 14 / AGDA-C-6.2 — replaces ParseInputBoundExceeded /
    // FrameInputBoundExceeded / DBCTextInputBoundExceeded; discriminate
    // by `bound_kind` from the structured payload).
    InputBoundExceeded,
    // Route errors
    RouteMissingField,
    RouteMissingArray,
    RouteUnknownCommand,
    RouteMissingCommandField,
    RouteDlcExceedsMax,
    RouteByteArrayParseFailed,
    RouteByteCountMismatch,
    RouteMissingDbcField,
    RouteMissingPropsField,
    // Handler errors
    HandlerNoDbc,
    HandlerAlreadyStreaming,
    HandlerNotStreaming,
    HandlerStreamNotStarted,
    HandlerStreamActive,
    HandlerPropertyParseFailed,
    HandlerInvalidDlcCode,
    HandlerValidationFailed,
    HandlerNonMonotonicTimestamp,
    // Dispatch errors
    DispatchMissingTypeField,
    DispatchUnknownMessageType,
    DispatchInvalidJson,
    DispatchRequestNotObject,
    // Extraction errors
    ExtractionMuxValueMismatch,
    ExtractionMuxSignalNotFound,
    ExtractionMuxChainCycle,
    ExtractionMuxExtractionFailed,
    ExtractionBitExtractionFailed,
};

/// Parse an error code string from Agda JSON into the enum.
[[nodiscard]] auto error_code_from_string(std::string_view s) -> ErrorCode;

class AletheiaError {
    ErrorKind kind_;
    ErrorCode code_;
    std::string message_;
    // Populated only when `kind_ == ErrorKind::InputBoundExceeded`; carries
    // the structured `bound_kind/observed/limit` that the Python and Go
    // bindings already expose via their typed `InputBoundExceededError`
    // (R19 cluster 8 — CPP-D-21.5 cross-binding parity).  Errors of any
    // other kind have `std::nullopt`.
    std::optional<InputBoundExceededError> bound_info_;
    // Populated only when `code_ == ErrorCode::HandlerValidationFailed` and
    // the error envelope carried well-typed `has_errors` + `issues` fields
    // (parseDBC / parseDBCText rejects); the elements use the same
    // {severity, code, detail} shape as a validation response.  Any other
    // error — including a validation-failed envelope without the structured
    // fields — has `std::nullopt`.
    std::optional<std::vector<ValidationIssue>> issues_;

public:
    AletheiaError(ErrorKind kind, std::string message, ErrorCode code = ErrorCode::Unknown,
                  std::optional<InputBoundExceededError> bound_info = std::nullopt,
                  std::optional<std::vector<ValidationIssue>> issues = std::nullopt)
        : kind_(kind)
        , code_(code)
        , message_(std::move(message))
        , bound_info_(std::move(bound_info))
        , issues_(std::move(issues)) {}

    [[nodiscard]] auto kind() const -> ErrorKind { return kind_; }
    [[nodiscard]] auto code() const -> ErrorCode { return code_; }
    [[nodiscard]] auto message() const -> std::string_view { return message_; }
    [[nodiscard]] auto bound_info() const -> const std::optional<InputBoundExceededError>& {
        return bound_info_;
    }
    [[nodiscard]] auto issues() const -> const std::optional<std::vector<ValidationIssue>>& {
        return issues_;
    }
};

template<typename T>
using Result = std::expected<T, AletheiaError>;

/// Throwing wrapper around `AletheiaError`.
///
/// The C++ binding's primary error-reporting channel is `Result<T> =
/// std::expected<T, AletheiaError>`.  Constructors (which cannot return
/// `Result`) and a small number of binary-FFI methods returning raw
/// `std::string` use exceptions instead; `AletheiaException` carries the
/// same `AletheiaError` value so callers can branch on `kind()` /
/// `code()` after a `catch`.  Derives from `std::runtime_error` so
/// pre-R20 `catch (const std::exception&)` blocks keep catching it via
/// the base; new code can `catch (const AletheiaException&)` to recover
/// the kind-tagged error.
class AletheiaException : public std::runtime_error {
    AletheiaError error_;

public:
    explicit AletheiaException(AletheiaError error)
        : std::runtime_error(std::string{error.message()})
        , error_(std::move(error)) {}

    [[nodiscard]] auto error() const -> const AletheiaError& { return error_; }
    [[nodiscard]] auto kind() const -> ErrorKind { return error_.kind(); }
    [[nodiscard]] auto code() const -> ErrorCode { return error_.code(); }
};

} // namespace aletheia

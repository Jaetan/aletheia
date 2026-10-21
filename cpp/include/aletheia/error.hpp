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
    Protocol,           // JSON protocol error from Agda core
    Validation,         // DBC structural issues
    State,              // Wrong state (e.g., send_frame when not streaming)
    Ffi,                // Library load / RTS initialization failure
    BinaryUnsupported,  // Backend cannot service the binary-path call (use JSON
                        // fallback); mirrors Go's ErrBinaryPathUnsupported sentinel.
    Cancellation,       // std::stop_token requested cancellation; cooperative at
                        // FFI boundaries (Rule 1 of docs/architecture/CANCELLATION.md):
                        // the next FFI call honors the request, an in-flight call
                        // runs to completion. Mirrors Go's wrapped context.Canceled.
    InputBoundExceeded, // Adversarial-input bound crossed at a parser surface;
                        // mirrors Python's `InputBoundExceededError` and Go's
                        // `*InputBoundExceededError` for cross-binding parity.
                        // The wire code is the single
                        // `ErrorCode::InputBoundExceeded`; `bound_kind` from
                        // the structured payload discriminates which bound.
    TextRoundtrip       // FormatDBCText refused: the emitted .dbc text does not
                        // re-parse to the input DBC.  A distinct kind (not
                        // Validation) so a caller discriminates a round-trip
                        // refusal from a structural validation failure — mirrors
                        // the distinct typed errors in the Python / Go / Rust
                        // bindings.
};

/// Machine-readable error codes mirroring the Agda `Error` ADT and the shim's
/// own refusal.
///
/// Each named constant other than `Unknown` maps 1:1 to a string emitted by
/// `errorCode` in `Aletheia.Error` — the Parse / DBC-text / Frame / Route /
/// Handler / Dispatch / Extraction families plus the consolidated top-level
/// `input_bound_exceeded` code (`WithContext` delegates to its inner error),
/// or, for `FfiValidationError`, by the shared library refusing an argument
/// it cannot read or a buffer it cannot write to.
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
    ParseSignalStartBitExceedsFrame,
    ParseSignalBitLengthExceedsFrame,
    ParseSignalBigEndianOverflow,
    ParseInvalidKind,
    ParseNonTerminatingRational,
    ParseInvalidIdentifier,
    ParseNonIntegerMultiplexValue,
    ParseNonNaturalField,
    ParseDlcCodeOutOfRange,
    ParsePayloadLengthMismatch,
    ParsePayloadByteOutOfRange,
    ParseNonPositiveDenominator,
    ParseSignalArrayLengthMismatch,
    ParseTimestampPastWire,
    // Text parse errors: a DBC text the grammar refuses carries one of these,
    // a decimal literal it refuses TextParseFailure or TextTrailingInput.
    TextParseFailure,
    TextTrailingInput,
    DBCTextAttributeRefinementFailed,
    // Frame errors
    FrameSignalNotFound,
    FrameSignalIndexOob,
    FrameValueOutOfRange,
    FrameValueNotRepresentable,
    FrameSignalsOverlap,
    FrameSignalPastFrameEnd,
    FrameCanIdNotFound,
    FrameCanIdMismatch,
    FrameSignalValueOutOfBounds,
    // Top-level adversarial-input bound, one code for every parser surface;
    // discriminate by `bound_kind` from the structured payload.
    InputBoundExceeded,
    // The DBC character set and keywords: a character outside the set
    // (`code_point`, located by `field` + `index` or `line` + `column`), a
    // keyword used as a name (`keyword`).
    DBCInvalidCharacter,
    DBCKeywordName,
    // Route errors
    RouteMissingField,
    RouteUnknownCommand,
    RouteMissingCommandField,
    RouteMissingDbcField,
    RouteMissingPropsField,
    // Handler errors
    HandlerNoDbc,
    HandlerAlreadyStreaming,
    HandlerNotStreaming,
    HandlerStreamNotStarted,
    HandlerStreamActive,
    HandlerPropertyParseFailed,
    // A property names a signal no signal of the loaded DBC carries.
    HandlerUnknownSignal,
    HandlerValidationFailed,
    HandlerTextRoundtripFailed,
    HandlerNonMonotonicTimestamp,
    // Dispatch errors
    DispatchMissingTypeField,
    DispatchUnknownMessageType,
    DispatchInvalidJson,
    DispatchRequestNotObject,
    // Extraction errors
    ExtractionMuxValueMismatch,
    ExtractionSignalPastFrameEnd,
    ExtractionMuxSignalNotFound,
    ExtractionMuxChainCycle,
    ExtractionMuxExtractionFailed,
    ExtractionValueExceedsWireRange,
    // The shared library's own refusal of an entry's arguments
    FfiValidationError,
};

/// Parse an error code string from Agda JSON into the enum.
[[nodiscard]] auto error_code_from_string(std::string_view s) -> ErrorCode;

class AletheiaError {
    ErrorKind kind_;
    ErrorCode code_;
    std::string message_;
    // Populated only when `kind_ == ErrorKind::InputBoundExceeded`; carries
    // the structured `bound_kind/observed/limit` and, for a DBC size bound,
    // the `field` that crossed it, as the Python and Go bindings' typed
    // `InputBoundExceededError` do.  Errors of any other kind have
    // `std::nullopt`.
    std::optional<InputBoundExceededError> bound_info_;
    // Populated when `code_` is `HandlerValidationFailed` (parseDBC /
    // parseDBCText rejects) or `HandlerTextRoundtripFailed` (formatDBCText
    // round-trip refusal) and the envelope carried well-typed `has_errors` +
    // `issues` fields; the elements use the same {severity, code, detail} shape
    // as a validation response.  Any other error — including one of those
    // envelopes without the structured fields — has `std::nullopt`.
    std::optional<std::vector<ValidationIssue>> issues_;
    /// Where a loader read a refused number and the key it sat under, one
    /// fact set by `located`; any other error has `std::nullopt`.
    struct Place {
        std::string location;
        std::string key;
    };
    std::optional<Place> place_;

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
    /// Where a loader read the refused number: a check of a YAML document or a
    /// row of a workbook.
    [[nodiscard]] auto location() const -> std::optional<std::string> {
        return place_.transform([](const Place& place) { return place.location; });
    }
    /// The key or column header the refused number sat under.
    [[nodiscard]] auto key() const -> std::optional<std::string> {
        return place_.transform([](const Place& place) { return place.key; });
    }

    /// This error, kind, code and fields kept, with the location and the key a
    /// loader read the refused number at.
    [[nodiscard]] auto located(std::string location, std::string key) const -> AletheiaError {
        auto copy = *this;
        copy.place_ = Place{.location = std::move(location), .key = std::move(key)};
        return copy;
    }

    /// The error as every binding prints it: `<location>: invalid '<key>':
    /// <message>` for a located error, the message alone for any other.
    [[nodiscard]] auto text() const -> std::string {
        if (place_)
            return place_.value().location + ": invalid '" + place_.value().key + "': " + message_;
        return message_;
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
/// existing `catch (const std::exception&)` blocks keep catching it via
/// the base; new code can `catch (const AletheiaException&)` to recover
/// the kind-tagged error.  `what()` is the error's `text()`.
class AletheiaException : public std::runtime_error {
    AletheiaError error_;

public:
    explicit AletheiaException(AletheiaError error)
        : std::runtime_error(error.text())
        , error_(std::move(error)) {}

    [[nodiscard]] auto error() const -> const AletheiaError& { return error_; }
    [[nodiscard]] auto kind() const -> ErrorKind { return error_.kind(); }
    [[nodiscard]] auto code() const -> ErrorCode { return error_.code(); }
};

} // namespace aletheia

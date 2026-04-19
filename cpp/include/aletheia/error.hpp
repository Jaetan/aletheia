// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <expected>
#include <string>
#include <string_view>
#include <utility>

namespace aletheia {

enum class ErrorKind {
    Protocol,         // JSON protocol error from Agda core
    Validation,       // DBC structural issues
    State,            // Wrong state (e.g., send_frame when not streaming)
    Ffi,              // Library load / RTS initialization failure
    BinaryUnsupported // Backend cannot service the binary-path call (use JSON
                      // fallback); mirrors Go's ErrBinaryPathUnsupported sentinel.
};

/// Machine-readable error codes mirroring the Agda `Error` ADT.
///
/// Each named constant other than `Unknown` maps 1:1 to a string emitted by
/// `errorCode` in `Aletheia.Error` — the ADT defines 49 codes across 6
/// families (Parse / Frame / Route / Handler / Dispatch / Extraction).
///
/// `Unknown` is a forward-compatibility sentinel used by
/// `error_code_from_string` when the Agda core returns a code the C++
/// binding does not recognise. In lock-step builds it should never be
/// produced; its presence here is a deliberate escape hatch rather than a
/// 50th ADT constructor.
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
    // Frame errors
    FrameSignalNotFound,
    FrameSignalIndexOob,
    FrameInjectionFailed,
    FrameSignalsOverlap,
    FrameCanIdNotFound,
    FrameCanIdMismatch,
    FrameSignalValueOutOfBounds,
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

public:
    AletheiaError(ErrorKind kind, std::string message, ErrorCode code = ErrorCode::Unknown)
        : kind_(kind)
        , code_(code)
        , message_(std::move(message)) {}

    [[nodiscard]] auto kind() const -> ErrorKind { return kind_; }
    [[nodiscard]] auto code() const -> ErrorCode { return code_; }
    [[nodiscard]] auto message() const -> std::string_view { return message_; }
};

template<typename T>
using Result = std::expected<T, AletheiaError>;

} // namespace aletheia

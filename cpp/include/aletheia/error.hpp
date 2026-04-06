// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <expected>
#include <string>
#include <string_view>
#include <utility>

namespace aletheia {

enum class ErrorKind {
    Protocol,   // JSON protocol error from Agda core
    Validation, // DBC structural issues
    State,      // Wrong state (e.g., send_frame when not streaming)
    Ffi         // Library load / RTS initialization failure
};

/// Machine-readable error codes matching Agda Error ADT (37 codes).
/// Each maps 1:1 to an Agda error constructor via errorCode.
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
    // Frame errors
    FrameSignalNotFound,
    FrameSignalIndexOob,
    FrameInjectionFailed,
    FrameSignalsOverlap,
    FrameCanIdNotFound,
    FrameCanIdMismatch,
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
    HandlerSignalListParseFailed,
    HandlerPropertyParseFailed,
    HandlerInvalidDlcCode,
    HandlerValidationFailed,
    // Dispatch errors
    DispatchMissingTypeField,
    DispatchUnknownMessageType,
    DispatchInvalidJson,
    DispatchRequestNotObject,
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

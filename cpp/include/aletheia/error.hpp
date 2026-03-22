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

class AletheiaError {
    ErrorKind kind_;
    std::string message_;

public:
    AletheiaError(ErrorKind kind, std::string message)
        : kind_(kind)
        , message_(std::move(message)) {}

    [[nodiscard]] auto kind() const -> ErrorKind { return kind_; }
    [[nodiscard]] auto message() const -> std::string_view { return message_; }
};

template<typename T>
using Result = std::expected<T, AletheiaError>;

} // namespace aletheia

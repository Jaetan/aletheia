// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Definitions for the FfiBackend pure decision helpers — see ffi_logic.hpp
// for the testability rationale.

#include "ffi_logic.hpp"

namespace aletheia::detail {

auto rts_init_args(int rts_cores) -> std::optional<std::array<std::string, 4>> {
    if (rts_cores > 1)
        return std::array<std::string, 4>{"aletheia", "+RTS", "-N" + std::to_string(rts_cores),
                                          "-RTS"};
    return std::nullopt;
}

auto rts_cores_mismatch(int requested, int active) -> std::optional<std::pair<int, int>> {
    if (requested != active)
        return std::make_pair(active, requested);
    return std::nullopt;
}

auto ffi_error_from_status(std::int8_t status, char* err_str, void (*free_str)(char*))
    -> std::optional<AletheiaError> {
    if (status != 0) {
        const std::string msg = err_str != nullptr ? err_str : "Unknown error";
        if (err_str != nullptr)
            free_str(err_str);
        return AletheiaError{ErrorKind::Protocol, msg};
    }
    return std::nullopt;
}

} // namespace aletheia::detail

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Definitions for the FfiBackend pure decision helpers — see ffi_logic.hpp
// for the testability rationale.

#include "ffi_logic.hpp"

#include "rts_params.hpp"

#include <aletheia/error.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::detail {

// ASCII whitespace that separates ALETHEIA_RTS_OPTS tokens.
static constexpr std::string_view k_rts_ws{" \t\n\r\v\f"};

auto rts_init_args(int rts_cores, std::string_view override_opts) -> std::vector<std::string> {
    // The heap cap is ALWAYS present and goes FIRST, so a caller -M in
    // override_opts lands later and wins (the RTS honours the last occurrence).
    std::vector<std::string> args{"aletheia", "+RTS", std::string{rts_heap_cap_flag}};
    if (rts_cores > rts_default_cores)
        args.push_back("-N" + std::to_string(rts_cores));
    // Whitespace-split override_opts and append each token.  The find-based form
    // carries no manual index-boundary comparison: the `< size()` guard such a
    // loop needs is a genuine equivalent under string_view's defined `[size()]`
    // read (it returns a non-space), so a mutation flipping it to `<=` cannot be
    // killed by any input.  find_first_*_of avoids the construct entirely.
    for (std::size_t start = override_opts.find_first_not_of(k_rts_ws);
         start != std::string_view::npos;) {
        const std::size_t end = override_opts.find_first_of(k_rts_ws, start);
        args.emplace_back(override_opts.substr(start, end - start));
        start = override_opts.find_first_not_of(k_rts_ws, end);
    }
    args.emplace_back("-RTS");
    return args;
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

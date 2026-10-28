// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared GHC RTS init state — see header for the cross-singleton
// rationale.

#include "rts_init.hpp"

#include <aletheia/error.hpp>

#include <expected>
#include <mutex>
#include <string>
#include <string_view>

namespace aletheia::detail {

auto rts_init_state() -> RTSInitState& {
    static RTSInitState s;
    return s;
}

auto rts_initialized() -> bool {
    auto& s = rts_init_state();
    std::scoped_lock const lk{s.mu};
    return s.initialized;
}

auto started_entries(std::string_view reading) -> Result<RuntimeEntries> {
    auto& s = rts_init_state();
    std::scoped_lock const lk{s.mu};
    if (!s.initialized)
        return std::unexpected(AletheiaError{
            ErrorKind::Ffi,
            "GHC runtime not initialized: call aletheia::start_runtime or open a client before " +
                std::string{reading}});
    return s.entries;
}

} // namespace aletheia::detail

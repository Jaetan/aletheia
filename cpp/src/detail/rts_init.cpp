// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared GHC RTS init state — see header for the cross-singleton
// rationale (R23 — CPP-D-17.1).

#include "rts_init.hpp"

namespace aletheia::detail {

auto rts_init_state() -> RTSInitState& {
    static RTSInitState s;
    return s;
}

} // namespace aletheia::detail

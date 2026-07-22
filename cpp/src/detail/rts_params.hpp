// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Runtime GHC RTS parameters — SSOT: docs/RESOURCE_BUDGETS.yaml (runtime
// block); mirrored here verbatim.  Parity with the SSOT is enforced by
// tools/check_rts_runtime.py (a run_ci gate) and cpp/tests/test_rts_params_parity.cpp.
//
// CONTAINMENT-BY-ABORT contract: the heap cap does NOT yield a recoverable
// error.  The loaded kernel's GHC RTS has no heap limit by default, so a
// runaway allocation exhausts host memory and the OOM killer takes the whole
// machine down.  With the cap in place the same runaway trips GHC's
// heap-overflow check and the foreign-export wrapper aborts the PROCESS
// (`aletheia: aletheia_process: Return code (4) not ok`).  There is no
// catchable error and no partial result — the host survives, the process does
// not.  This is a containment bound with measured headroom (heaviest kernel
// working set observed ~1.5 GiB), never a tuned working-set budget.

#pragma once

#include <string_view>

namespace aletheia::detail {

// Default -M heap cap emitted into the RTS argv (see rts_init_args).
inline constexpr std::string_view rts_heap_cap_flag = "-M3G";

// GHC capability count for single-bus monitoring; a -N flag is emitted only
// when a caller requests more.
inline constexpr int rts_default_cores = 1;

// The GHC entry point that starts the RTS.  Plain hs_init cannot carry the -M
// cap under the .so's link-time RtsOptsSafeOnly (it aborts at init with "Most
// RTS options are disabled"); hs_init_with_rtsopts honours the full flag set.
// Same C signature (void(int*, char***)), so the switch is a pure string change.
inline constexpr std::string_view rts_init_symbol = "hs_init_with_rtsopts";

// Environment variable whose whitespace-split flags are appended after the cap
// (and after an optional -N), so a caller -M wins (the RTS honours the last
// occurrence).
inline constexpr std::string_view rts_override_env = "ALETHEIA_RTS_OPTS";

} // namespace aletheia::detail

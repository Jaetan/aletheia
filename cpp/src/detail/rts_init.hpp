// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared GHC RTS init state — used by both `rational_renderer.cpp` and
// `ffi_backend.cpp` so the two independent `dlopen`+`hs_init` sites
// coordinate on a single source of truth.
//
// Why this exists (R23 — CPP-D-17.1).  Before this TU, each of the two
// .cpp files held its own function-static `rts_state` (initialized flag
// + cores), so the GHC RTS could be initialized twice without either
// side knowing.  GHC's `hs_init` is idempotent — the second call is
// silently a no-op even when the new argv would have set `+RTS -N<n>`.
// That made the renderer-first-then-FfiBackend ordering drop the user's
// `rts_cores` arg without triggering the `rts.cores_mismatch` warning,
// because FfiBackend's local `rts_state.initialized` flag stayed
// `false` and FfiBackend thought it was the first init.
//
// Sharing the state across both TUs closes the gap: whichever singleton
// initializes the RTS first records the cores it requested in
// `rts_init_state()`, and the other singleton sees `initialized == true`
// when it tries to init.  FfiBackend then surfaces the renderer's
// `cores == 1` vs. user's `rts_cores > 1` as the existing
// `rts_mismatch_info()` warning — the warning that would have silently
// vanished under the per-TU state.
//
// Lifecycle invariant: the GHC RTS is process-global, so `hs_init` is
// called at most once per process.  The state set here lives for the
// process lifetime; there is no teardown path — `hs_exit` is never
// called (GHC RTS does not support reinitialization), so the state
// is never reset.

#pragma once

#include <mutex>

namespace aletheia::detail {

struct RTSInitState {
    std::mutex mu;
    bool initialized = false;
    // Cores actually passed to `hs_init` at first-init.  Recorded as 1
    // for renderer-first (no `+RTS -N<n>` argv) and as the user's
    // `rts_cores` for FfiBackend-first.  Used by FfiBackend to detect
    // and surface the renderer-first downgrade case.
    int cores = 0;
};

// Function-static accessor — guarantees a single instance shared across
// every TU that links against aletheia-cpp.  Lock `RTSInitState::mu`
// before reading or writing `initialized` / `cores`.
auto rts_init_state() -> RTSInitState&;

} // namespace aletheia::detail

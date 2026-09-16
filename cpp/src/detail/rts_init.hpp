// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared GHC RTS init state — `ffi_backend.cpp` initialises the RTS and
// `rational_renderer.cpp` reads this state to decide whether it may call the
// kernel, so the two TUs coordinate on a single source of truth.
//
// FfiBackend (`make_ffi_backend`) is the sole RTS initialiser: its constructor
// runs `hs_init` once and records the requested cores here. The rational
// renderer is a *consumer* — it dlopens the .so for the format/free symbols but
// does NOT init the RTS; before calling the kernel it checks `rts_initialized()`
// and throws if the runtime is down rather than self-initialising, which would
// latch a default `-N` and squander the FfiBackend's bus-count `-N` (GHC's
// `hs_init` is one-shot per process).
//
// The `cores` field backs FfiBackend's `rts.cores_mismatch` warning when more
// than one FfiBackend is created with differing `rts_cores` (first init wins).
//
// Lifecycle invariant: the GHC RTS is process-global, so `hs_init` is called at
// most once per process; there is no teardown (`hs_exit` is never called, as the
// GHC RTS does not support reinitialization), so the state is never reset.

#pragma once

#include <mutex>

namespace aletheia::detail {

struct RTSInitState {
    std::mutex mu;
    bool initialized = false;
    // The `rts_cores` the first FfiBackend passed to `hs_init`.  A later
    // FfiBackend constructed with a different count cannot change it and
    // surfaces the difference as the `rts.cores_mismatch` warning.
    int cores = 0;
};

// Function-static accessor — guarantees a single instance shared across
// every TU that links against aletheia-cpp.  Lock `RTSInitState::mu`
// before reading or writing `initialized` / `cores`.
[[nodiscard]] auto rts_init_state() -> RTSInitState&;

// Whether the GHC RTS has been initialised (by an FfiBackend). The rational
// renderer checks this before calling the kernel and throws if it is false,
// rather than self-initialising. Acquires `RTSInitState::mu` internally.
[[nodiscard]] auto rts_initialized() -> bool;

} // namespace aletheia::detail

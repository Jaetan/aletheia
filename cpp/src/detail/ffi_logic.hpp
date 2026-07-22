// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Pure decision logic extracted out of `FfiBackend` (ffi_backend.cpp) so the
// RTS-init and FFI-error branches are unit-testable without a live `dlopen`ed
// `libaletheia-ffi.so`.
//
// FfiBackend owns process-global, once-only side effects (`hs_init`, dlopen)
// and its error paths only fire when the Haskell kernel returns a non-zero
// status — both awkward to drive from a test.  Lifting the branch *decisions*
// into these three pure functions makes each branch observable directly, and
// collapses the error block that was triplicated across `build_frame_bin` /
// `update_frame_bin` / `extract_signals_bin` into one site.

#pragma once

#include <aletheia/error.hpp>

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::detail {

// GHC RTS argv for hs_init_with_rtsopts.  ALWAYS includes the containment heap
// cap (rts_params.hpp `rts_heap_cap_flag`), so the host is protected regardless
// of the requested core count — unlike the old optional form, which returned
// nullopt (and thus NO cap) for the single-core default.  Layout per the SSOT
// argv_order: `{"aletheia", "+RTS", "-M<cap>", "-N<n>" iff rts_cores >
// rts_default_cores, <override flags>, "-RTS"}`.  `override_opts` is the raw
// ALETHEIA_RTS_OPTS string, whitespace-split and appended after the cap — taken
// as a PARAMETER (the caller does the getenv) so this stays a pure, unit-
// testable decision.  The std::string storage is owned by the returned vector;
// the caller copies its `.data()` pointers into process-lifetime storage for
// hs_init (GHC retains argv).
auto rts_init_args(int rts_cores, std::string_view override_opts) -> std::vector<std::string>;

// Detect a requested-vs-active RTS core mismatch (the renderer-first downgrade
// case).  Returns `{active, requested}` — the order `rts_mismatch_info()`
// reports — when the two differ, else nullopt.
auto rts_cores_mismatch(int requested, int active) -> std::optional<std::pair<int, int>>;

// Convert a binary-FFI `(status, err_str)` outcome into an error.  `status == 0`
// → nullopt (success).  Otherwise returns `AletheiaError{Protocol, msg}` where
// `msg` is `err_str` when non-null, or "Unknown error" when the backend
// signalled failure without a message; a non-null `err_str` (Haskell-owned) is
// released via `free_str`.  `free_str` is a plain C function pointer
// (`void(*)(char*)`) to match the dlsym'd `aletheia_free_str`.
auto ffi_error_from_status(std::int8_t status, char* err_str, void (*free_str)(char*))
    -> std::optional<AletheiaError>;

} // namespace aletheia::detail

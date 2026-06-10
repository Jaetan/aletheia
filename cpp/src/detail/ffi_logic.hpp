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

#include <array>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>

namespace aletheia::detail {

// GHC RTS argv for a requested core count, or nullopt for the single-core
// default (the caller then does `hs_init(nullptr, nullptr)`).  `rts_cores > 1`
// yields the `{"aletheia", "+RTS", "-N<n>", "-RTS"}` argv; `<= 1` yields
// nullopt.  The std::string storage is owned by the returned array — the
// caller takes `.data()` for hs_init's `char**` without const_cast.
auto rts_init_args(int rts_cores) -> std::optional<std::array<std::string, 4>>;

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

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
// gives `build_frame_bin`, `update_frame_bin` and `extract_signals_bin` one
// error path to share.

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
// of the requested core count.  Layout per the SSOT
// argv_order: `{"aletheia", "+RTS", "-M<cap>", "-N<n>" iff rts_cores >
// rts_default_cores, <override flags>, "-RTS"}`.  `override_opts` is the raw
// ALETHEIA_RTS_OPTS string, whitespace-split and appended after the cap — taken
// as a PARAMETER (the caller does the getenv) so this stays a pure, unit-
// testable decision.  The std::string storage is owned by the returned vector;
// the caller copies its `.data()` pointers into process-lifetime storage for
// hs_init (GHC retains argv).
[[nodiscard]] auto rts_init_args(int rts_cores, std::string_view override_opts)
    -> std::vector<std::string>;

// Detect a requested-vs-active RTS core mismatch (a later FfiBackend asking
// for a count the first one did not pass).  Returns `{active, requested}` in
// the order `rts_mismatch_info()` reports when the two differ, else nullopt.
[[nodiscard]] auto rts_cores_mismatch(int requested, int active)
    -> std::optional<std::pair<int, int>>;

// Convert a binary-FFI `(status, err_str)` outcome into an error.  `status == 0`
// → nullopt (success).  Otherwise returns `AletheiaError{Protocol, msg}` where
// `msg` is `err_str` when non-null, or "Unknown error" when the backend
// signalled failure without a message; a non-null `err_str` (Haskell-owned) is
// released via `free_str`.  `free_str` is a plain C function pointer
// (`void(*)(char*)`) to match the dlsym'd `aletheia_free_str`.
[[nodiscard]] auto ffi_error_from_status(std::int8_t status, char* err_str, void (*free_str)(char*))
    -> std::optional<AletheiaError>;

// The wire-form refusal of a JSON command longer than `max_json_bytes`, or
// nullopt for one within it.  The kernel enforces the same bound; answering
// here spares the copy of an input that would only be refused on the other
// side.  The shape carries the structured bound_kind, observed and limit
// fields beside the code and message, which the `parse_*` paths lift into
// the error's bound_info, as the Python and Go bindings' typed errors do.
[[nodiscard]] auto json_input_bound_error(std::size_t input_bytes) -> std::optional<std::string>;

} // namespace aletheia::detail

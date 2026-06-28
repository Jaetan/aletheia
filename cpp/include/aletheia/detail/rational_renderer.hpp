// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Internal interface for the cross-binding-identical Rational
// pretty-printer (R20 cluster Y stage 2).
//
// `format_value(const Rational&)` (in `enrich.cpp`) calls
// `format_rational_ffi` on every render.  The implementation
// dlopens `libaletheia-ffi.so` lazily on first use via `std::call_once`
// — no local C++ fallback exists, so output is byte-identical to
// Python's and Go's by construction rather than via a test corpus.
//
// Throws `AletheiaException` (kind `Ffi`) when the library cannot be
// located or symbols cannot be resolved.  Callers may rely on
// `format_value(const Rational&)` propagating that exception; setting
// the `ALETHEIA_LIB` environment variable is the standard remedy when
// the search heuristic does not find the .so (e.g. out-of-tree builds).

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

namespace aletheia::detail {

// Render `(num, denom)` via the Agda kernel.  Lazy-initialises the FFI
// on first call.  Throws `AletheiaException(Ffi)` if the library is
// not loadable.
auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::string;

// Parse a decimal literal into an exact rational via the Agda kernel's
// `aletheia_parse_decimal`, returning the RAW JSON wire envelope (a bare
// `{"numerator","denominator"}` on success, or `{"status":"error",...}` on a
// parse failure / int64 overflow).  Symmetric with `format_rational_ffi`: it
// shares the renderer's lazy-load + vocal-RTS contract — it does NOT initialise
// the GHC RTS (an FfiBackend is the sole initialiser), so it throws
// `AletheiaException(Ffi)` when the runtime is down rather than self-initialising.
// The caller decodes the envelope via `detail::decode_decimal_response`
// (in json.hpp) — this TU stays JSON-free.  Throws `AletheiaException(Ffi)` if
// the library is not loadable or the runtime is uninitialised.
auto parse_decimal_ffi(std::string_view input) -> std::string;

// Register a preferred `libaletheia-ffi.so` path for the lazy-load.
// Called by `make_ffi_backend(lib_path, ...)` so the renderer (which
// loads independently of the backend) consults the same .so the user
// asked for, instead of falling back to its relative-path heuristic.
// First-write-wins under `std::call_once`: subsequent registrations
// after the renderer has loaded are no-ops (the renderer's state is
// already pinned).  Pre-load registrations win over the heuristic;
// `ALETHEIA_LIB` env var still wins over both.
// Closes R21 CPP-SYS-17.1 / GO-S-17.2 / Python parallel.
void register_default_lib_path(const std::filesystem::path& lib_path);

} // namespace aletheia::detail

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Internal interface for the cross-binding-identical Rational
// pretty-printer.
//
// Every render in the binding goes through `format_rational` below, which
// dlopens `libaletheia-ffi.so` lazily on first use via `std::call_once`
// — no local C++ fallback exists, so output is byte-identical to
// Python's and Go's by construction rather than via a test corpus.
//
// Throws `AletheiaException` (kind `Ffi`) when the library cannot be
// located or symbols cannot be resolved.  Callers may rely on that
// exception propagating; setting the `ALETHEIA_LIB` environment variable
// is the standard remedy when the search heuristic does not find the .so
// (e.g. out-of-tree builds).

#include <aletheia/types.hpp>

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

namespace aletheia::detail {

// Render `(num, denom)` via the Agda kernel.  Lazy-initialises the FFI
// on first call.  Throws `AletheiaException(Ffi)` if the library is
// not loadable.
[[nodiscard]] auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::string;

// The one place the binding turns a Rational into text, so the check
// builder's thresholds and the enrichment renderer's values cannot drift.
[[nodiscard]] inline auto format_rational(const Rational& r) -> std::string {
    return format_rational_ffi(r.numerator(), r.denominator());
}

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
[[nodiscard]] auto parse_decimal_ffi(std::string_view input) -> std::string;

// Register a preferred `libaletheia-ffi.so` path for the lazy-load.
// Called by `make_ffi_backend(lib_path, ...)` so the renderer (which
// loads independently of the backend) consults the same .so the user
// asked for, instead of falling back to its relative-path heuristic.
// The first registration wins and every later one is ignored; the
// renderer reads it once, inside its `std::call_once`.  The load takes
// the first candidate that exists, in the order `ALETHEIA_LIB`, the
// registered path, the relative heuristic: a variable naming a missing
// file is skipped, not an error (a probe under probes/ pins both halves).
void register_default_lib_path(const std::filesystem::path& lib_path);

// The search behind `aletheia::find_ffi_library`, over the inputs it reads:
// the `ALETHEIA_LIB` value or null, the registered path or empty, and the
// directory the build-tree candidates are relative to. The first route that
// names a file that exists answers; none answering is the empty path.
[[nodiscard]] auto search_ffi_library(const char* env_path, std::string_view registered_path,
                                      const std::filesystem::path& cwd) -> std::filesystem::path;

// The refusal the renderer records for a library at `lib_path`, or empty
// when that library loads and carries the renderer's three entries. A refused
// library is closed again; one that serves stays mapped, as the renderer's
// own would.
[[nodiscard]] auto renderer_load_error(const std::filesystem::path& lib_path) -> std::string;

} // namespace aletheia::detail

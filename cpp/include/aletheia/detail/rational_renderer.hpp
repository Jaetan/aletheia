// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Internal interface for the cross-binding-identical Rational
// pretty-printer.
//
// Every render in the binding goes through `format_rational` below, which
// calls the kernel in the library the GHC runtime started on: no local C++
// fallback exists, so output is byte-identical to Python's and Go's by
// construction rather than via a test corpus.
//
// Each entry answers an error of kind `Ffi` while the runtime is down, naming
// `aletheia::start_runtime` and a client as the remedy; neither starts the
// runtime itself.

#include <aletheia/error.hpp>
#include <aletheia/types.hpp>

#include <cstdint>
#include <expected>
#include <filesystem>
#include <string>
#include <string_view>

namespace aletheia::detail {

// Render `(num, denom)` via the Agda kernel: the text, or kind `Ffi` while the
// runtime is down or when the kernel returns a null string.
[[nodiscard]] auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> Result<std::string>;

// The one place the binding turns a Rational into text, so the check
// builder's thresholds and the enrichment renderer's values cannot drift.
[[nodiscard]] inline auto format_rational(Rational const& r) -> Result<std::string> {
    return format_rational_ffi(r.numerator(), r.denominator());
}

// Parse a decimal literal into an exact rational via the Agda kernel's
// `aletheia_parse_decimal`.  The inner answer is the kernel's: the rational,
// or its raw JSON error envelope (`{"status":"error",...}` on a parse failure
// or a component past the kernel's magnitude bound), which the caller reads
// via `detail::binary_refusal` (in json.hpp), this TU staying JSON-free.  The
// outer error is the binding's: kind `Ffi` while the runtime is down, kind
// `Protocol` for a failure without an envelope or a non-positive denominator.
[[nodiscard]] auto parse_decimal_ffi(std::string_view input)
    -> Result<std::expected<Rational, std::string>>;

// Register a preferred `libaletheia-ffi.so` path for `aletheia::find_ffi_library`.
// `start_runtime` and `make_ffi_backend` call it with the path they opened.
// The first registration wins and every later one is ignored.  The search takes
// the first candidate that exists, in the order `ALETHEIA_LIB`, the registered
// path, the relative heuristic: a variable naming a missing file is skipped,
// not an error; the search tests in cpp/tests/unit_tests_validation.cpp hold
// both halves.
void register_default_lib_path(std::filesystem::path const& lib_path);

// The search behind `aletheia::find_ffi_library`, over the inputs it reads:
// the `ALETHEIA_LIB` value or null, the registered path or empty, and the
// directory the build-tree candidates are relative to.
[[nodiscard]] auto search_ffi_library(char const* env_path, std::string_view registered_path,
                                      std::filesystem::path const& cwd)
    -> Result<std::filesystem::path>;

} // namespace aletheia::detail

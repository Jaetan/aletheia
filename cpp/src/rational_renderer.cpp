// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// FFI dispatch for the kernel's Rational entries: the cross-binding-identical
// pretty-printer and the decimal parser, and the library search the command
// line and the benchmarks share.
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so, and every decimal through
// `aletheia_parse_decimal`, called in the library the runtime started on
// through the entries the start recorded (`runtime_start.cpp`).  Neither
// starts the GHC runtime, which would fix its core count before the program
// chose one: while it is down they answer an error.
// No local C++ fallback exists; `format_value(const Rational&)` (in
// `enrich.cpp`) is byte-identical to Python's and Go's output by
// construction, not by a test corpus.

#include <aletheia/backend.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include "detail/ffi_abi.hpp"
#include "detail/ffi_logic.hpp"
#include "detail/rts_init.hpp"

#include <cstdint>
#include <cstdlib>
#include <expected>
#include <filesystem>
#include <memory>
#include <mutex>
#include <string>
#include <string_view>
#include <system_error>

namespace aletheia::detail {

// Package-static preferred library path, registered by `start_runtime` and
// `make_ffi_backend` with the path they opened.  Function-static, and every
// write by `register_default_lib_path()` and read by `find_library_path()`
// holds its mutex.
namespace {
struct DefaultPathState {
    std::mutex mu;
    std::string path;
};
} // namespace

static auto default_path_state() -> DefaultPathState& {
    static DefaultPathState s;
    return s;
}

// The one search, published as aletheia::find_ffi_library at the end of this
// file and shared by every caller: AletheiaClient::open, the command-line tool
// and both benchmarks. It consults the path a start or a backend registered,
// the state in this file. It takes what it reads as arguments, so a test
// reaches each route whatever the process already holds.
auto search_ffi_library(char const* env_path, std::string_view registered_path,
                        std::filesystem::path const& cwd) -> Result<std::filesystem::path> {
    namespace fs = std::filesystem;
    // A path that cannot be looked at is taken not to exist.
    std::error_code ec;
    // A set value is the library asked for: one naming no file is refused, as
    // Python refuses it, rather than answered by another route.
    if (env_path != nullptr && !std::string_view{env_path}.empty()) {
        fs::path p{env_path};
        if (fs::exists(p, ec))
            return p;
        return std::unexpected(AletheiaError{
            ErrorKind::Ffi, "ALETHEIA_LIB=" + std::string{env_path} + " does not exist"});
    }
    // No registration yet is the empty path, which names no file.
    {
        fs::path p{registered_path};
        if (fs::exists(p, ec))
            return p;
    }
    // Heuristic: ctest runs from `cpp/build`; integration / parity
    // tests already navigate to `<repo>/build/libaletheia-ffi.so`.
    for (auto const* candidate : {
             "../../build/libaletheia-ffi.so",
             "../build/libaletheia-ffi.so",
             "build/libaletheia-ffi.so",
         }) {
        auto p = fs::canonical(cwd / candidate, ec);
        if (!ec)
            return p;
    }
    return std::unexpected(AletheiaError{
        ErrorKind::Ffi,
        "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'"});
}

static auto find_library_path() -> Result<std::filesystem::path> {
    auto& d = default_path_state();
    std::scoped_lock const lk{d.mu};
    // A working directory that cannot be read leaves the build candidates
    // relative, where they name nothing that resolves.
    std::error_code ec;
    auto const cwd = std::filesystem::current_path(ec);
    return search_ffi_library(std::getenv("ALETHEIA_LIB"), d.path, cwd);
}

// Call one kernel function of the library the runtime started on and own the
// string it returns, `reading` naming the operation in the refusal while the
// runtime is down and `returned_null` the function.  A null return is
// unreachable for a well-formed call, so it is an error rather than a
// fabricated value, as Go and Rust answer it.
template<typename Call>
static auto kernel_string(Call call, std::string_view reading, std::string_view returned_null)
    -> Result<std::string> {
    auto const started = started_entries(reading);
    if (!started)
        return std::unexpected(detail::error_of(started));
    auto const& entries = started.value();
    auto* raw = call(entries);
    if (raw == nullptr)
        return std::unexpected(
            AletheiaError{ErrorKind::Ffi, std::string{returned_null} + " returned a null pointer"});
    auto const deleter = [&entries](char* p) { entries.free_str(p); };
    std::unique_ptr<char, decltype(deleter)> const guard{raw, deleter};
    return std::string{raw};
}

auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> Result<std::string> {
    return kernel_string(
        [&](RuntimeEntries const& entries) {
            FfiRational const value{.numerator = num, .denominator = denom};
            return entries.format_rational(&value);
        },
        "rendering", "aletheia_format_rational");
}

auto parse_decimal_ffi(std::string_view input) -> Result<std::expected<Rational, std::string>> {
    auto const started = started_entries("parsing decimals");
    if (!started)
        return std::unexpected(detail::error_of(started));
    auto const& entries = started.value();
    auto const text = ffi_text(input);
    FfiDecimal out{.value = {.numerator = 0, .denominator = 0}, .err = nullptr};
    if (entries.parse_decimal(&text, &out) != 0) {
        if (out.err == nullptr)
            return std::unexpected(AletheiaError{ErrorKind::Protocol,
                                                 "aletheia_parse_decimal failed without an error"});
        auto const deleter = [&entries](char* p) { entries.free_str(p); };
        std::unique_ptr<char, decltype(deleter)> const guard{out.err, deleter};
        return std::expected<Rational, std::string>{std::unexpect, out.err};
    }
    return decimal_value(out.value.numerator, out.value.denominator)
        .transform([](Rational value) -> std::expected<Rational, std::string> { return value; });
}

void register_default_lib_path(std::filesystem::path const& lib_path) {
    auto& d = default_path_state();
    std::scoped_lock const lk{d.mu};
    if (d.path.empty()) // first-write-wins
        d.path = lib_path.string();
}

} // namespace aletheia::detail

namespace aletheia {

// Published so the client, the command-line tool and the benchmarks search one
// way. Defined here because the search consults state this file owns.
auto find_ffi_library() -> Result<std::filesystem::path> {
    return detail::find_library_path();
}

} // namespace aletheia

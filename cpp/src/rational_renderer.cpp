// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Self-contained lazy-load + FFI dispatch for the cross-binding-
// identical Rational pretty-printer.
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so.  The renderer dlopens
// the library on first use via `std::call_once` for the format/free symbols,
// but does NOT initialise the GHC RTS — that is an FfiBackend's job.  If the
// runtime is not up it throws rather than self-initialising, which would
// squander the FfiBackend's bus-count -N (the RTS is one-shot per process).
// No local C++ fallback exists; `format_value(const Rational&)` (in
// `enrich.cpp`) is byte-identical to Python's and Go's output by
// construction, not by a test corpus.

#include <aletheia/backend.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include "detail/rts_init.hpp"

#include <dlfcn.h>

#include <cstdint>
#include <cstdlib>
#include <expected>
#include <filesystem>
#include <memory>
#include <mutex>
#include <string>
#include <string_view>
#include <tuple>

namespace aletheia::detail {

namespace {

using FormatRationalFn = char* (*)(std::int64_t, std::int64_t);
using FreeStrFn = void (*)(char*);
using ParseDecimalFn = char* (*)(const char*);

struct RendererState {
    std::once_flag init;
    bool loaded = false;
    std::string load_error;
    FormatRationalFn format_fn = nullptr;
    FreeStrFn free_fn = nullptr;
    ParseDecimalFn parse_decimal_fn = nullptr;
};
} // namespace

// Function-local static for the singleton state.  Wrapped in an
// accessor so it isn't flagged as a non-const global
// (cppcoreguidelines-avoid-non-const-global-variables); function-static
// initialisation is thread-safe per [stmt.dcl]/4 ("magic statics").
static auto state() -> RendererState& {
    static RendererState s;
    return s;
}

// Package-static preferred library path, registered by
// `make_ffi_backend(lib_path, ...)` before any Check builder triggers
// `format_rational_ffi`.  Function-static + mutex so writes from
// `register_default_lib_path()` are serialized; the read in
// `find_library_path()` happens inside `std::call_once(init)` so
// reader sees a stable value.  Stored as `std::string` (not `path`)
// to avoid the path's variant-of-string allocation on the read path.
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
// file and shared by every caller: the renderer below, the command-line tool
// and both benchmarks. It lives here because the registered path it consults
// is the state in this file, written by a make_ffi_backend call, and that
// consultation is what keeps the renderer and the backend on the same library.
// Runs once per process, on the first render, and the first FfiBackend of a
// process has registered its path by then; so the order below is held by a
// probe in a process of its own, not by the suite.
auto search_ffi_library(const char* env_path, std::string_view registered_path,
                        const std::filesystem::path& cwd) -> std::filesystem::path {
    namespace fs = std::filesystem;
    // An empty value, from the environment or from no registration yet, is a
    // path that does not exist, so each route is one existence check.
    if (env_path != nullptr) {
        const fs::path p{env_path};
        if (fs::exists(p))
            return p;
    }
    {
        const fs::path p{registered_path};
        if (fs::exists(p))
            return p;
    }
    // Heuristic: ctest runs from `cpp/build`; integration / parity
    // tests already navigate to `<repo>/build/libaletheia-ffi.so`.
    for (auto const* candidate : {
             "../../build/libaletheia-ffi.so",
             "../build/libaletheia-ffi.so",
             "build/libaletheia-ffi.so",
         }) {
        const fs::path p = cwd / candidate;
        if (fs::exists(p))
            return fs::canonical(p);
    }
    return {};
}

static auto find_library_path() -> std::filesystem::path {
    auto& d = default_path_state();
    const std::scoped_lock lk{d.mu};
    return search_ffi_library(std::getenv("ALETHEIA_LIB"), d.path, std::filesystem::current_path());
}

namespace {
// The three kernel entries the renderer calls, resolved from one library.
struct RendererSymbols {
    FormatRationalFn format_fn = nullptr;
    FreeStrFn free_fn = nullptr;
    ParseDecimalFn parse_decimal_fn = nullptr;
};
} // namespace

// dlopen + dlsym the library at `lib_path`, or the reason it could not be.
// The handle a successful load opened stays open for the process, which is
// the renderer's own lifetime. Does NOT initialise the GHC RTS (that is an
// FfiBackend's job).
static auto load_renderer(const std::filesystem::path& lib_path)
    -> std::expected<RendererSymbols, std::string> {
    if (lib_path.empty())
        return std::unexpected(
            "libaletheia-ffi.so not found; build with: cabal run shake -- build");
    // A library that lacks an entry is closed again on the way out, so a
    // refused load leaves no mapping behind; the one that serves is released
    // to the process for the renderer's lifetime.
    struct Closer {
        void operator()(void* handle) const noexcept { dlclose(handle); }
    };
    std::unique_ptr<void, Closer> opened{dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL)};
    if (opened == nullptr)
        return std::unexpected(std::string{"renderer dlopen failed: "} + dlerror());
    auto const load_sym = [&](const char* name) -> std::expected<void*, std::string> {
        dlerror(); // clear previous errors
        void* sym = dlsym(opened.get(), name);
        if (const char* err = dlerror(); err != nullptr)
            return std::unexpected(std::string{"renderer dlsym "} + name + ": " + err);
        return sym;
    };
    auto const fmt_sym = load_sym("aletheia_format_rational");
    if (!fmt_sym)
        return std::unexpected(fmt_sym.error());
    auto const free_sym = load_sym("aletheia_free_str");
    if (!free_sym)
        return std::unexpected(free_sym.error());
    auto const parse_decimal_sym = load_sym("aletheia_parse_decimal");
    if (!parse_decimal_sym)
        return std::unexpected(parse_decimal_sym.error());
    std::ignore = opened.release();
    return RendererSymbols{
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
        .format_fn = reinterpret_cast<FormatRationalFn>(*fmt_sym),
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
        .free_fn = reinterpret_cast<FreeStrFn>(*free_sym),
        // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
        .parse_decimal_fn = reinterpret_cast<ParseDecimalFn>(*parse_decimal_sym),
    };
}

auto renderer_load_error(const std::filesystem::path& lib_path) -> std::string {
    auto const loaded = load_renderer(lib_path);
    return loaded ? std::string{} : loaded.error();
}

// Records the resolved function pointers, or the load's refusal, in the
// singleton state. Called exactly once per process via `std::call_once`.
static void init_renderer() {
    auto& s = state();
    auto const loaded = load_renderer(find_library_path());
    if (!loaded) {
        s.load_error = loaded.error();
        return;
    }
    s.format_fn = loaded->format_fn;
    s.free_fn = loaded->free_fn;
    s.parse_decimal_fn = loaded->parse_decimal_fn;
    s.loaded = true;
}

static void ensure_loaded() {
    auto& s = state();
    std::call_once(s.init, init_renderer);
    if (!s.loaded)
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi,
                          "Rational pretty-printer requires libaletheia-ffi.so: " + s.load_error});
}

// The shape both entry points share: load lazily, refuse while the RTS is
// down (calling the kernel then is undefined behaviour), call one kernel
// function, own the string it returns.  `whats_down` and `returned_null`
// name the operation in those two refusals.  A null return is unreachable
// for a well-formed call, so it throws rather than fabricating a value,
// as Go and Rust do.
static auto loaded_state(std::string_view whats_down) -> RendererState& {
    ensure_loaded();
    if (!rts_initialized())
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi, "GHC runtime not initialized: create a backend before " +
                                              std::string{whats_down}});
    return state();
}

template<typename Call>
static auto kernel_string(Call call, std::string_view whats_down, std::string_view returned_null)
    -> std::string {
    auto& s = loaded_state(whats_down);
    char* raw = call(s);
    if (raw == nullptr)
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi, std::string{returned_null} + " returned a null pointer"});
    auto const deleter = [&s](char* p) { s.free_fn(p); };
    const std::unique_ptr<char, decltype(deleter)> guard{raw, deleter};
    return std::string{raw};
}

auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::string {
    return kernel_string([&](RendererState& s) { return s.format_fn(num, denom); }, "rendering",
                         "aletheia_format_rational");
}

auto parse_decimal_ffi(std::string_view input) -> std::string {
    return kernel_string(
        [&](RendererState& s) {
            // Reject an interior NUL before marshaling: the kernel takes a
            // NUL-terminated C string, so a NUL inside the input would silently
            // truncate the literal ("1\0xyz" -> "1") and accept a value the
            // caller did not intend. A NUL is not in the decimal grammar, so
            // this is a user-input fault (Validation), mirroring Rust's
            // CString::new rejection. It sits inside the call, after the
            // runtime gate, because Rust refuses a runtime-down call before it
            // looks at the literal and the two bindings answer alike.
            if (input.contains('\0'))
                throw AletheiaException(AletheiaError{
                    ErrorKind::Validation, "decimal literal contains an interior NUL byte"});
            const std::string buf{input};
            return s.parse_decimal_fn(buf.c_str());
        },
        "parsing decimals", "aletheia_parse_decimal");
}

void register_default_lib_path(const std::filesystem::path& lib_path) {
    auto& d = default_path_state();
    const std::scoped_lock lk{d.mu};
    if (d.path.empty()) // first-write-wins
        d.path = lib_path.string();
}

} // namespace aletheia::detail

namespace aletheia {

// Published so the command-line tool and the benchmarks search the same way the
// renderer does. Defined here because the search consults state this file owns.
auto find_ffi_library() -> std::filesystem::path {
    return detail::find_library_path();
}

} // namespace aletheia

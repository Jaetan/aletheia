// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Self-contained lazy-load + FFI dispatch for the cross-binding-
// identical Rational pretty-printer (R20 cluster Y stage 2).
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so.  The renderer dlopens
// the library on first use via `std::call_once` for the format/free symbols,
// but does NOT initialise the GHC RTS — that is an FfiBackend's job.  If the
// runtime is not up it throws (point 2) rather than self-initialising (which
// would squander the FfiBackend's bus-count -N; the RTS is one-shot per
// process).  No local C++ fallback exists; `format_value(const Rational&)`
// (in `enrich.cpp`) is byte-identical to Python's and Go's output by
// construction, not by a test corpus.

#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

#include "detail/rts_init.hpp"

#include <dlfcn.h>

#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <memory>
#include <mutex>
#include <string>
#include <string_view>

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

// Locate libaletheia-ffi.so for the lazy-load.  Search order:
//   (1) ALETHEIA_LIB env var (operator override)
//   (2) Path registered via `register_default_lib_path` (the .so the
//       user passed to `make_ffi_backend(lib_path, ...)`)
//   (3) Relative-path heuristic (ctest from `cpp/build`)
// Returns the empty path when no candidate exists; the caller surfaces
// that as an `AletheiaException(Ffi)` so the operator knows to set
// `ALETHEIA_LIB` or run `cabal run shake -- build`.
static auto find_library_path() -> std::filesystem::path {
    namespace fs = std::filesystem;
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        const std::string_view env_sv{env};
        if (!env_sv.empty()) {
            const fs::path p{env_sv};
            if (fs::exists(p))
                return p;
        }
    }
    // R21 cluster 2: registered path from FfiBackend ctor.
    {
        auto& d = default_path_state();
        const std::scoped_lock lk{d.mu};
        if (!d.path.empty()) {
            const fs::path p{d.path};
            if (fs::exists(p))
                return p;
        }
    }
    // Heuristic: ctest runs from `cpp/build`; integration / parity
    // tests already navigate to `<repo>/build/libaletheia-ffi.so`.
    for (const auto* candidate : {
             "../../build/libaletheia-ffi.so",
             "../build/libaletheia-ffi.so",
             "build/libaletheia-ffi.so",
         }) {
        const fs::path p = fs::current_path() / candidate;
        if (fs::exists(p))
            return fs::canonical(p);
    }
    return {};
}

// dlopen + dlsym the library.  Records either the resolved function
// pointers or a load-error string in the singleton state.  Does NOT
// initialise the GHC RTS (point 2 — that is an FfiBackend's job).
// Called exactly once per process via `std::call_once`.
static void init_renderer() {
    auto& s = state();
    auto lib_path = find_library_path();
    if (lib_path.empty()) {
        s.load_error = "libaletheia-ffi.so not found; build with: cabal run shake -- build";
        return;
    }
    void* handle = dlopen(lib_path.c_str(), RTLD_NOW | RTLD_LOCAL);
    if (handle == nullptr) {
        s.load_error = std::string{"renderer dlopen failed: "} + dlerror();
        return;
    }
    auto load_sym = [&](const char* name) -> void* {
        dlerror(); // clear previous errors
        void* sym = dlsym(handle, name);
        if (const char* err = dlerror(); err != nullptr) {
            s.load_error = std::string{"renderer dlsym "} + name + ": " + err;
            return nullptr;
        }
        return sym;
    };
    void* fmt_sym = load_sym("aletheia_format_rational");
    if (fmt_sym == nullptr)
        return;
    void* free_sym = load_sym("aletheia_free_str");
    if (free_sym == nullptr)
        return;
    void* parse_decimal_sym = load_sym("aletheia_parse_decimal");
    if (parse_decimal_sym == nullptr)
        return;

    // The renderer does NOT initialise the GHC RTS (point 2): an FfiBackend is
    // the sole initialiser, so it only resolves the format/free/parse symbols here.
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    s.format_fn = reinterpret_cast<FormatRationalFn>(fmt_sym);
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    s.free_fn = reinterpret_cast<FreeStrFn>(free_sym);
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    s.parse_decimal_fn = reinterpret_cast<ParseDecimalFn>(parse_decimal_sym);
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

auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::string {
    ensure_loaded();
    // The renderer is a consumer of a runtime an FfiBackend must bring up: be
    // vocal (throw) when it is down rather than self-initialising (which would
    // squander the FfiBackend's bus-count -N) or calling the kernel with the RTS
    // uninitialised (undefined behaviour). The caller must create a backend first.
    if (!rts_initialized())
        throw AletheiaException(AletheiaError{
            ErrorKind::Ffi, "GHC runtime not initialized: create a backend before rendering"});
    auto& s = state();
    char* raw = s.format_fn(num, denom);
    if (raw == nullptr)
        // Unreachable for a well-formed rational (the kernel never returns null);
        // throw rather than fabricating "0" — a null means a kernel/ABI
        // malfunction, and a silent "0" would hide the bug. Matches Rust/Go.
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi, "aletheia_format_rational returned a null pointer"});
    auto deleter = [&s](char* p) { s.free_fn(p); };
    const std::unique_ptr<char, decltype(deleter)> guard{raw, deleter};
    return std::string{raw};
}

auto parse_decimal_ffi(std::string_view input) -> std::string {
    ensure_loaded();
    // Same vocal contract as format_rational_ffi: parsing a decimal calls into the
    // kernel, which requires a live GHC RTS that only an FfiBackend brings up. Be
    // vocal (throw) when it is down rather than self-initialising (which would
    // squander the FfiBackend's bus-count -N) or calling the kernel with the RTS
    // uninitialised (undefined behaviour). The caller must create a backend first.
    if (!rts_initialized())
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi,
                          "GHC runtime not initialized: create a backend before parsing decimals"});
    // Reject an interior NUL before marshaling: the kernel takes a NUL-terminated
    // C string, so a NUL inside the input would silently truncate the literal
    // (e.g. "1\0xyz" -> "1") and accept a value the caller did not intend. A NUL
    // is not in the decimal grammar, so this is a user-input fault (Validation),
    // mirroring Rust's CString::new rejection — cross-binding parity.
    if (input.contains('\0'))
        throw AletheiaException(
            AletheiaError{ErrorKind::Validation, "decimal literal contains an interior NUL byte"});
    auto& s = state();
    // The kernel takes a NUL-terminated C string; materialise one from the view.
    const std::string buf{input};
    char* raw = s.parse_decimal_fn(buf.c_str());
    if (raw == nullptr)
        // Unreachable for a well-formed call (the kernel returns the error
        // envelope as a string, never null); a null means a kernel/ABI
        // malfunction, so throw rather than fabricating a value. Matches Rust/Go.
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi, "aletheia_parse_decimal returned a null pointer"});
    auto deleter = [&s](char* p) { s.free_fn(p); };
    const std::unique_ptr<char, decltype(deleter)> guard{raw, deleter};
    return std::string{raw};
}

void register_default_lib_path(const std::filesystem::path& lib_path) {
    auto& d = default_path_state();
    const std::scoped_lock lk{d.mu};
    if (d.path.empty()) // first-write-wins
        d.path = lib_path.string();
}

} // namespace aletheia::detail

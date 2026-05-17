// SPDX-License-Identifier: BSD-2-Clause
//
// Self-contained lazy-load + FFI dispatch for the cross-binding-
// identical Rational pretty-printer (R20 cluster Y stage 2).
//
// Single source of truth: every render flows through
// `aletheia_format_rational` in libaletheia-ffi.so.  The library is
// dlopened on first use via `std::call_once` — independently of
// `FfiBackend`, so unit tests that never instantiate a backend still
// route through the same Agda kernel function.  No local C++ fallback
// exists; `format_value(const Rational&)` (in `enrich.cpp`) is
// byte-identical to Python's and Go's output by construction, not by a
// test corpus.

#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/error.hpp>

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

using HsInitFn = void (*)(int*, char***);
using FormatRationalFn = char* (*)(std::int64_t, std::int64_t);
using FreeStrFn = void (*)(char*);

struct RendererState {
    std::once_flag init;
    bool loaded = false;
    std::string load_error;
    FormatRationalFn format_fn = nullptr;
    FreeStrFn free_fn = nullptr;
};

// Function-local static for the singleton state.  Wrapped in an
// accessor so it isn't flagged as a non-const global
// (cppcoreguidelines-avoid-non-const-global-variables); function-static
// initialisation is thread-safe per [stmt.dcl]/4 ("magic statics").
auto state() -> RendererState& {
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
struct DefaultPathState {
    std::mutex mu;
    std::string path;
};

auto default_path_state() -> DefaultPathState& {
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
auto find_library_path() -> std::filesystem::path {
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
        const std::lock_guard lk{d.mu};
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

// dlopen + dlsym + hs_init the library.  Records either the resolved
// function pointers or a load-error string in the singleton state.
// Called exactly once per process via `std::call_once`.
void init_renderer() {
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
    void* hs_init_sym = load_sym("hs_init");
    if (hs_init_sym == nullptr)
        return;
    void* fmt_sym = load_sym("aletheia_format_rational");
    if (fmt_sym == nullptr)
        return;
    void* free_sym = load_sym("aletheia_free_str");
    if (free_sym == nullptr)
        return;

    // hs_init is idempotent in GHC; if `FfiBackend` has already
    // initialised the RTS (with `+RTS -N<cores>` flags maybe), this
    // no-op call doesn't disturb that.  If we win the race, FfiBackend
    // observes `rts.initialized == true` and skips its own hs_init.
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto hs_init = reinterpret_cast<HsInitFn>(hs_init_sym);
    hs_init(nullptr, nullptr);

    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    s.format_fn = reinterpret_cast<FormatRationalFn>(fmt_sym);
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    s.free_fn = reinterpret_cast<FreeStrFn>(free_sym);
    s.loaded = true;
}

void ensure_loaded() {
    auto& s = state();
    std::call_once(s.init, init_renderer);
    if (!s.loaded)
        throw AletheiaException(
            AletheiaError{ErrorKind::Ffi,
                          "Rational pretty-printer requires libaletheia-ffi.so: " + s.load_error});
}

} // namespace

auto format_rational_ffi(std::int64_t num, std::int64_t denom) -> std::string {
    ensure_loaded();
    auto& s = state();
    char* raw = s.format_fn(num, denom);
    if (raw == nullptr) {
        // Defensive: the Agda function always returns a non-null
        // CString (denom = 0 returns the literal "0").  Reach here
        // only on a catastrophic Haskell-side allocation failure.
        return std::string{"0"};
    }
    auto deleter = [&s](char* p) { s.free_fn(p); };
    const std::unique_ptr<char, decltype(deleter)> guard{raw, deleter};
    return std::string{raw};
}

void register_default_lib_path(const std::filesystem::path& lib_path) {
    auto& d = default_path_state();
    const std::lock_guard lk{d.mu};
    if (d.path.empty())  // first-write-wins
        d.path = lib_path.string();
}

} // namespace aletheia::detail

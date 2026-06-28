// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Point 2 ("whine if the runtime is uninitialised"): the rational renderer no
// longer self-initialises the GHC RTS — an FfiBackend is the sole initialiser
// (see cpp/src/detail/rts_init.hpp + rational_renderer.cpp). This test asserts
// the renderer is *vocal* when no FfiBackend has brought the runtime up: a
// pre-backend `format_rational_ffi` must throw, neither self-initialising (which
// would latch a default -N and squander the FfiBackend's bus-count -N) nor
// calling the kernel with the RTS down.
//
// Must run in its own process (one ctest entry) because the GHC RTS is
// process-global: any FfiBackend-first test in the same process would bring the
// runtime up and defeat the assertion. The unit_tests listener that brings the
// RTS up lives in a *different* binary (unit_tests_rts_setup.cpp), so it does not
// interfere here.
//
// (The backend-first ordering — FfiBackend(cores=N) then renderer — is covered by
// integration_tests; this binary is the renderer-first / runtime-down case.)

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <cstdlib>
#include <filesystem>
#include <string_view>

namespace fs = std::filesystem;

namespace {

auto find_lib() -> fs::path {
    // Existence-check ALETHEIA_LIB and fall through if stale, mirroring the
    // renderer's find_library_path verbatim (getenv → string_view !empty →
    // fs::exists): a stale env value must not shadow a present .so, else the
    // renderer would miss the library and this test would throw the wrong error
    // (missing-library, not runtime-not-initialised). Only when EVERY candidate is
    // exhausted do we SKIP — locating the .so is a hard precondition for the test.
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        const std::string_view env_sv{env};
        if (!env_sv.empty()) {
            if (const fs::path p{env_sv}; fs::exists(p))
                return p;
        }
    }
    if (auto* repo = std::getenv("ALETHEIA_REPO_ROOT")) {
        const std::string_view repo_sv{repo};
        if (!repo_sv.empty()) {
            const fs::path candidate = fs::path{repo_sv} / "build" / "libaletheia-ffi.so";
            if (fs::exists(candidate))
                return candidate;
        }
    }
    SKIP(
        "libaletheia-ffi.so not found — set ALETHEIA_LIB or build with 'cabal run shake -- build'");
    return {};
}

} // namespace

TEST_CASE("renderer is vocal (throws) when the GHC runtime is uninitialised",
          "[rational_renderer][rts_init]") {
    const auto lib = find_lib(); // SKIPs if the .so cannot be located

    // Register the .so so the renderer locates it (loads the format/free symbols)
    // and the throw below is the runtime-not-initialised error, not a missing-
    // library error.
    aletheia::detail::register_default_lib_path(lib);

    // No FfiBackend has been created in this process, so the GHC RTS is down. The
    // renderer must be vocal — throw rather than self-init or fabricate a value.
    REQUIRE_THROWS_WITH(aletheia::detail::format_rational_ffi(22, 7),
                        Catch::Matchers::ContainsSubstring("runtime not initialized"));
}

TEST_CASE("Rational::from_decimal is vocal (throws) when the GHC runtime is uninitialised",
          "[rational_renderer][rts_init][decimal]") {
    const auto lib = find_lib(); // SKIPs if the .so cannot be located

    // Register the .so so the parse path locates it (loads the parse/free symbols)
    // and the throw below is the runtime-not-initialised error, not a missing-
    // library error.
    aletheia::detail::register_default_lib_path(lib);

    // Decimal parsing is RTS-gated exactly like rational rendering: with no
    // FfiBackend in this process the GHC RTS is down, so from_decimal must throw
    // rather than self-initialising the runtime or calling the kernel with it
    // down (the float principle's decimal SSOT shares the renderer's vocal gate).
    REQUIRE_THROWS_WITH(aletheia::Rational::from_decimal("3.14"),
                        Catch::Matchers::ContainsSubstring("runtime not initialized"));
}

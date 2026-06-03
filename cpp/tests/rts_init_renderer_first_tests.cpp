// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// R23 — CPP-D-17.1: cross-singleton GHC RTS init ordering.
//
// Renderer-first scenario: trigger `format_rational_ffi` (lazy renderer
// init via `rational_renderer.cpp`'s singleton) BEFORE constructing any
// `FfiBackend`.  Then construct `FfiBackend(lib, rts_cores = 4)` and
// assert that the `rts_mismatch_info()` warning surfaces with
// active_cores = 1 (the renderer's default) and requested_cores = 4
// (the user's argument).
//
// Before the shared `rts_init_state` (`cpp/src/detail/rts_init.hpp`),
// each TU held its own `rts_state` and FfiBackend would silently
// re-attempt `hs_init` (idempotent in GHC, second call no-op) without
// detecting the renderer had already initialized the RTS at the
// default -N.  The `rts.cores_mismatch` warning never fired and the
// user's `rts_cores` argument was silently dropped.
//
// The backend-first ordering (FfiBackend(cores=N) then renderer) is
// already covered by the existing integration_tests cases at
// `cpp/tests/integration_tests.cpp:1469+` — those work entirely
// through FfiBackend so the renderer is never the first singleton in
// that process.  This binary runs in its own process (one ctest entry)
// so the renderer-first init is observable; the GHC RTS is
// process-global so this scenario cannot share a process with any
// FfiBackend-first test.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <cstdlib>
#include <filesystem>

namespace fs = std::filesystem;

namespace {

auto find_lib() -> fs::path {
    if (auto* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0') {
        return env;
    }
    if (auto* repo = std::getenv("ALETHEIA_REPO_ROOT"); repo != nullptr && *repo != '\0') {
        const fs::path candidate = fs::path{repo} / "build" / "libaletheia-ffi.so";
        if (fs::exists(candidate))
            return candidate;
    }
    SKIP(
        "libaletheia-ffi.so not found — set ALETHEIA_LIB or build with 'cabal run shake -- build'");
    return {};
}

} // namespace

TEST_CASE("renderer-first init then FfiBackend(rts_cores>1) surfaces cores_mismatch",
          "[ffi_backend][rts_init]") {
    const auto lib = find_lib();

    // 1. Renderer-first init.  Triggering `format_rational_ffi` calls
    //    `hs_init(nullptr, nullptr)` inside `rational_renderer.cpp`'s
    //    `init_renderer()` and records `cores = 1` in the shared
    //    `detail::rts_init_state()`.
    const auto rendered = aletheia::detail::format_rational_ffi(22, 7);
    CHECK_FALSE(rendered.empty());

    // 2. Construct an FfiBackend with rts_cores = 4.  Before R23 —
    //    CPP-D-17.1 this silently dropped the `-N4` flag (GHC hs_init
    //    is idempotent; second call no-op).  After the fix, FfiBackend
    //    sees the renderer's prior init via the shared state and
    //    populates `rts_mismatch_info()` so Client emits the standard
    //    `rts.cores_mismatch` structured log event.
    auto backend = aletheia::make_ffi_backend(lib, /*rts_cores=*/4);
    REQUIRE(backend != nullptr);

    const auto info = backend->rts_mismatch_info();
    REQUIRE(info.has_value());
    CHECK(info->first == 1);  // active cores = renderer's default
    CHECK(info->second == 4); // requested cores = user's rts_cores
}

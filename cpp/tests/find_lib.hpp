// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Where a test that loads the real kernel finds libaletheia-ffi.so, or skips.
// Two units of the integration suite load it, so the lookup is written once.

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <filesystem>

#include "repo_root.hpp"

namespace aletheia::test {

[[nodiscard]] inline auto find_lib() -> std::filesystem::path {
    // The environment first, for CI and custom builds, but only when it names
    // a file that is there: an empty or stale value must not shadow a library
    // that is, else a missing file becomes a construction failure rather than
    // the skip this function exists for.
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        if (const std::filesystem::path p{env}; !p.empty() && std::filesystem::exists(p))
            return p;
    }

    // Default: project build directory
    auto const project_root = repo_root();
    auto lib = project_root / "build" / "libaletheia-ffi.so";
    if (std::filesystem::exists(lib))
        return lib;

    // Dist directory
    auto dist = project_root / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so";
    if (std::filesystem::exists(dist))
        return dist;

    SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    return {};
}

} // namespace aletheia::test

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Where a test that loads the real kernel finds libaletheia-ffi.so, or skips
// when it is nowhere. ALETHEIA_LIB, set, is the library asked for, as the
// binding's own search takes it: one naming no file fails the test, so a
// mistyped value is a red run rather than skipped tests or another library.

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <filesystem>
#include <string_view>

#include "repo_root.hpp"

namespace aletheia::test {

// The value of ALETHEIA_LIB when it is set and not empty.
[[nodiscard]] inline auto set_aletheia_lib() -> const char* {
    const char* env = std::getenv("ALETHEIA_LIB");
    return env != nullptr && !std::string_view{env}.empty() ? env : nullptr;
}

[[nodiscard]] inline auto find_lib() -> std::filesystem::path {
    if (auto const* env = set_aletheia_lib()) {
        const std::filesystem::path p{env};
        if (!std::filesystem::exists(p))
            FAIL("ALETHEIA_LIB=" << env << " does not exist");
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

    SKIP("libaletheia-ffi.so not found: run 'cabal run shake -- build' first");
    return {};
}

} // namespace aletheia::test

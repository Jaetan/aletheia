// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Runtime GHC RTS parameters — C++ parity (the C++ leg of the K.1 runtime tier).
//
// Reads docs/RESOURCE_BUDGETS.yaml (the cross-binding SSOT, itself enforced
// against every binding by the `check-rts-runtime` run_ci gate) and asserts the
// C++ mirror constants (src/detail/rts_params.hpp) match.  Pure vocabulary test:
// no RTS, no FFI backend.  Mirrors test_wire_codes_parity.cpp's YAML mechanics.

#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include "detail/rts_params.hpp"

#include <cstdlib>
#include <filesystem>
#include <stdexcept>
#include <string>

using namespace aletheia::detail;

namespace {

// Repo root via env var, see test_feature_matrix_parity.cpp.
auto repo_root() -> std::filesystem::path {
    if (const char* env = std::getenv("ALETHEIA_REPO_ROOT"); env != nullptr && *env != '\0') {
        return std::filesystem::path{env};
    }
    throw std::runtime_error("ALETHEIA_REPO_ROOT env var not set; expected to be passed by ctest "
                             "via set_tests_properties(ENVIRONMENT ...) in cpp/CMakeLists.txt");
}

} // namespace

TEST_CASE("C++ RTS mirror matches docs/RESOURCE_BUDGETS.yaml", "[parity][rts]") {
    const auto path = repo_root() / "docs" / "RESOURCE_BUDGETS.yaml";
    REQUIRE(std::filesystem::exists(path));
    const auto root = YAML::LoadFile(path.string());
    const auto runtime = root["runtime"];
    REQUIRE(runtime);

    CHECK(runtime["heap_cap"]["flag"].as<std::string>() == std::string{rts_heap_cap_flag});
    CHECK(runtime["default_cores"]["value"].as<int>() == rts_default_cores);
    CHECK(runtime["init_symbol"].as<std::string>() == std::string{rts_init_symbol});
    CHECK(runtime["heap_cap"]["override_env"].as<std::string>() == std::string{rts_override_env});
}

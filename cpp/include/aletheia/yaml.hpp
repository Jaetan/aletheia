// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// YAML loader for declarative CAN signal checks.
//
// Loads check definitions from YAML files or strings and compiles them
// through the Check API into LTL properties.
//
// ```cpp
// if (!start_runtime_from_env(1)) // the kernel reads numbers
//     return 1;
// auto from_file = load_checks_from_yaml("checks.yaml");
// auto from_text = load_checks_from_yaml_string(R"(
// checks:
//   - signal: VehicleSpeed
//     condition: never_exceeds
//     value: 220
// )");
// ```
//
#pragma once

// load_checks_from_yaml returns Result<vector<CheckResult>> — callers need
// Check, CheckResult, and the Result/AletheiaError vocabulary without a
// separate direct include.
#include <aletheia/check.hpp> // IWYU pragma: export
#include <aletheia/error.hpp> // IWYU pragma: export

#include <filesystem>
#include <string_view>
#include <vector>

namespace aletheia {

/// Load checks from a YAML file.
[[nodiscard]] auto load_checks_from_yaml(std::filesystem::path const& path)
    -> Result<std::vector<CheckResult>>;

/// Load checks from a YAML string.
[[nodiscard]] auto load_checks_from_yaml_string(std::string_view yaml)
    -> Result<std::vector<CheckResult>>;

} // namespace aletheia

// SPDX-License-Identifier: BSD-2-Clause
//
// YAML loader for declarative CAN signal checks.
//
// Loads check definitions from YAML files or strings and compiles them
// through the Check API into LTL properties.
//
//   auto checks = load_checks_from_yaml("my_checks.yaml");
//   auto checks = load_checks_from_yaml_string(R"(
//     checks:
//       - signal: VehicleSpeed
//         condition: never_exceeds
//         value: 220
//   )");
//
#pragma once

#include <aletheia/check.hpp>
#include <aletheia/error.hpp>

#include <expected>
#include <filesystem>
#include <string_view>
#include <vector>

namespace aletheia {

/// Load checks from a YAML file.
auto load_checks_from_yaml(const std::filesystem::path& path) -> Result<std::vector<CheckResult>>;

/// Load checks from a YAML string.
auto load_checks_from_yaml_string(std::string_view yaml) -> Result<std::vector<CheckResult>>;

} // namespace aletheia

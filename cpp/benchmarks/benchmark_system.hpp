// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The host description and the timestamp every benchmark mode's JSON report
// carries.

#include <nlohmann/json.hpp>

#include <string>

namespace aletheia::bench {

auto get_system_info() -> nlohmann::json;
auto iso_timestamp() -> std::string;

} // namespace aletheia::bench

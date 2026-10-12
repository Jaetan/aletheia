// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Where the human-readable report goes, and the rules and headings it is drawn
// with.

#include <cstdio>
#include <string_view>

namespace aletheia::bench {

auto out_file() -> std::FILE*&;

inline constexpr std::string_view k_rule_heavy =
    "======================================================================";

void print_header(std::string_view title);
void print_separator();

} // namespace aletheia::bench

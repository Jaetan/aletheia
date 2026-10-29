// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Where the human-readable report goes, the rules and headings it is drawn
// with, and the check that a mode's report reached its stream.

#include <cstdio>
#include <functional>
#include <string_view>

namespace aletheia::bench {

auto out_file() -> std::FILE*&;

inline constexpr std::string_view k_rule_heavy =
    "======================================================================";

void print_header(std::string_view title);
void print_separator();

// Runs `lane`, which writes the `mode` report to `report`, then flushes the
// report. A write the report refused, while the lane ran or at the flush,
// throws a std::system_error reading "writing the <mode> report failed:
// <reason>", whatever the report's size: the system's reason for the write
// that failed, or EIO's "Input/output error" when the report's error indicator
// alone records it. Any other error the lane raises passes through as it was
// raised.
void write_mode_report(std::FILE* report, std::string_view mode, std::function<void()> const& lane);

} // namespace aletheia::bench

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The destination of the human-readable report and the rule lines its headings
// and tables are drawn with.

#include "benchmark_output.hpp"

#include <cstdio>
#include <print>
#include <string_view>

// ---------------------------------------------------------------------------
// Output helpers
// ---------------------------------------------------------------------------

namespace aletheia::bench {

// Output destination: stderr when --json is set, stdout otherwise. Held in a
// function-local static so the destination is reachable without a mutable
// object at namespace scope.
auto out_file() -> std::FILE*& {
    static auto* destination = stdout;
    return destination;
}

} // namespace aletheia::bench

static constexpr std::string_view k_rule_light =
    "----------------------------------------------------------------------";

namespace aletheia::bench {

void print_header(std::string_view title) {
    std::println(out_file(), "{}\n{}\n{}", k_rule_heavy, title, k_rule_heavy);
}

void print_separator() {
    std::println(out_file(), "{}", k_rule_light);
}

} // namespace aletheia::bench

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The destination of the human-readable report, the rule lines its headings
// and tables are drawn with, and the check that a mode's report reached its
// stream.

#include "benchmark_output.hpp"
#include "report_flush.hpp"

#include <cstdio>
#include <format>
#include <functional>
#include <print>
#include <string_view>
#include <system_error>

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

void write_mode_report(std::FILE* report, std::string_view mode,
                       std::function<void()> const& lane) {
    auto const refused = [mode](std::error_code reason) {
        return std::system_error{reason, std::format("writing the {} report failed", mode)};
    };
    try {
        lane();
    } catch (std::system_error const& e) {
        // The print path throws when a write it makes to the stream fails; the
        // report's error indicator tells that failure from the lane's own.
        if (std::ferror(report) == 0)
            throw;
        throw refused(e.code());
    }
    // A write can fail inside the print path without throwing: under
    // libstdc++ 16, a line that, with its newline, fills the stream's buffer
    // exactly, printed after an earlier print to the stream, drops the buffer
    // it could not write, so the flush finds nothing to write and the error
    // indicator alone records the failure, which flush_report reads.
    if (auto const reason = flush_report(report))
        throw refused(reason);
}

} // namespace aletheia::bench

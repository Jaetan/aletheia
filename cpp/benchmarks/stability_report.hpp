// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The stability harness's verdict and the report that carries it: the gate
// each watched resource is judged under, the JSON the lane archives, and the
// write that puts the report on its stream. The write answers why when the
// report does not reach the stream: a report the stream only buffered is lost
// at the flush on exit without a word, and the lane would read an exit status
// with no report behind it.
#pragma once

#include "report_flush.hpp"
#include "stability_snapshot.hpp"

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <expected>
#include <format>
#include <iterator>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace aletheia::bench {

// One resource's verdict: its reading at each snapshot, the drift between
// them, and the gate it was judged under. The kernel's allocation also carries
// each cycle's bytes and the most one cycle allocated less what the least did.
struct SubCheck {
    std::string name;
    std::string gate; // "hard_zero", "equal_per_cycle" or "report"
    std::int64_t start;
    std::int64_t end;
    std::int64_t delta;
    std::int64_t threshold;
    bool passed;
    std::vector<std::int64_t> per_cycle;
    std::int64_t spread = 0;
};

// Each cycle's bytes: the difference of each reading of the kernel's
// allocation and the one before it.
inline auto per_cycle_of(std::vector<std::int64_t> const& readings) -> std::vector<std::int64_t> {
    return readings | std::views::pairwise_transform([](std::int64_t before, std::int64_t after) {
               return after - before;
           }) |
           std::ranges::to<std::vector>();
}

// Each resource the harness watches: the exact counts as the pair of snapshots
// they are judged on, the kernel's allocation as its readings before and after
// every cycle (`readings` holds at least the opening one), and the resident set
// and the allocator's bytes reported, deciding nothing.
inline auto build_sub_checks(Snapshot const& start, Snapshot const& end,
                             std::vector<std::int64_t> const& readings) -> std::vector<SubCheck> {
    auto const per_cycle = per_cycle_of(readings);
    auto const spread =
        per_cycle.empty() ? 0 : std::ranges::max(per_cycle) - std::ranges::min(per_cycle);
    return {
        {.name = "rss",
         .gate = "report",
         .start = start.rss_bytes,
         .end = end.rss_bytes,
         .delta = end.rss_bytes - start.rss_bytes,
         .threshold = 0,
         .passed = true},
        {.name = "fd_count",
         .gate = "hard_zero",
         .start = start.fd_count,
         .end = end.fd_count,
         .delta = end.fd_count - start.fd_count,
         .threshold = 0,
         .passed = end.fd_count == start.fd_count},
        {.name = "active_thread_count",
         .gate = "hard_zero",
         .start = start.active_thread_count,
         .end = end.active_thread_count,
         .delta = end.active_thread_count - start.active_thread_count,
         .threshold = 0,
         .passed = end.active_thread_count == start.active_thread_count},
        {.name = "malloc_info",
         .gate = "report",
         .start = start.malloc_info_bytes,
         .end = end.malloc_info_bytes,
         .delta = end.malloc_info_bytes - start.malloc_info_bytes,
         .threshold = 0,
         .passed = true},
        {.name = "kernel_allocation",
         .gate = "equal_per_cycle",
         .start = readings.front(),
         .end = readings.back(),
         .delta = readings.back() - readings.front(),
         .threshold = 0,
         .passed = spread == 0,
         .per_cycle = per_cycle,
         .spread = spread},
    };
}

// The run's verdict: every check passed.
inline auto all_passed(std::vector<SubCheck> const& sub_checks) -> bool {
    return std::ranges::all_of(sub_checks, &SubCheck::passed);
}

// The JSON report of `cycles` cycles of `frames` frames each, measured over
// `elapsed_seconds`: the counts, each check, and the verdict.
inline auto report_text(int cycles, int frames, double elapsed_seconds,
                        std::vector<SubCheck> const& sub_checks) -> std::string {
    auto text =
        std::format("{{\n"
                    "  \"binding\": \"cpp\",\n"
                    "  \"cycles\": {},\n"
                    "  \"frames_per_cycle\": {},\n"
                    "  \"total_frames\": {},\n"
                    "  \"elapsed_seconds\": {},\n"
                    "  \"sub_checks\": [\n",
                    cycles, frames, static_cast<std::int64_t>(cycles) * frames, elapsed_seconds);
    for (auto const [i, c] : std::views::enumerate(sub_checks)) {
        std::format_to(std::back_inserter(text),
                       "{}    {{\n"
                       "      \"name\": \"{}\",\n"
                       "      \"gate\": \"{}\",\n"
                       "      \"start\": {},\n"
                       "      \"end\": {},\n"
                       "      \"delta\": {},\n"
                       "      \"threshold\": {},\n",
                       i == 0 ? "" : ",\n", c.name, c.gate, c.start, c.end, c.delta, c.threshold);
        if (c.gate == "equal_per_cycle")
            std::format_to(std::back_inserter(text),
                           "      \"per_cycle\": {},\n"
                           "      \"spread\": {},\n",
                           c.per_cycle, c.spread);
        std::format_to(std::back_inserter(text),
                       "      \"passed\": {}\n"
                       "    }}",
                       c.passed);
    }
    std::format_to(std::back_inserter(text),
                   "\n  ],\n"
                   "  \"passed\": {}\n"
                   "}}\n",
                   all_passed(sub_checks));
    return text;
}

// Writes `text` to `out` and flushes it, or answers why `out` did not take it:
// the system's reason for the write that failed, or flush_report's.
inline auto write_report_text(std::FILE* out, std::string_view text)
    -> std::expected<void, std::string> {
    if (std::fwrite(text.data(), 1, text.size(), out) != text.size())
        return std::unexpected(std::generic_category().message(errno));
    if (auto const reason = flush_report(out))
        return std::unexpected(reason.message());
    return {};
}

} // namespace aletheia::bench

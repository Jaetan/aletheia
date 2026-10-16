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
#include <cstdlib>
#include <expected>
#include <format>
#include <iterator>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace aletheia::bench {

// Soft-threshold caps, established empirically on a quiet WSL2 host; revise
// inline if a host rejects them as too tight or too loose.
inline constexpr std::int64_t k_rss_delta_bytes_cap = 50LL * 1024 * 1024;    // 50 MiB
inline constexpr std::int64_t k_malloc_delta_bytes_cap = 50LL * 1024 * 1024; // 50 MiB

// One resource's verdict: its reading at each snapshot, the drift between
// them, and the gate and threshold it was judged under.
struct SubCheck {
    std::string name;
    std::string gate; // "hard_zero" or "soft_threshold"
    std::int64_t start;
    std::int64_t end;
    std::int64_t delta;
    std::int64_t threshold;
    bool passed;
};

// Each resource the harness watches, as the pair of snapshots it is judged on.
inline auto build_sub_checks(const Snapshot& start, const Snapshot& end) -> std::vector<SubCheck> {
    return {
        {.name = "rss",
         .gate = "soft_threshold",
         .start = start.rss_bytes,
         .end = end.rss_bytes,
         .delta = end.rss_bytes - start.rss_bytes,
         .threshold = k_rss_delta_bytes_cap,
         .passed = std::abs(end.rss_bytes - start.rss_bytes) <= k_rss_delta_bytes_cap},
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
         .gate = "soft_threshold",
         .start = start.malloc_info_bytes,
         .end = end.malloc_info_bytes,
         .delta = end.malloc_info_bytes - start.malloc_info_bytes,
         .threshold = k_malloc_delta_bytes_cap,
         .passed =
             std::abs(end.malloc_info_bytes - start.malloc_info_bytes) <= k_malloc_delta_bytes_cap},
    };
}

// The run's verdict: every check passed.
inline auto all_passed(const std::vector<SubCheck>& sub_checks) -> bool {
    return std::ranges::all_of(sub_checks, &SubCheck::passed);
}

// The JSON report of `cycles` cycles of `frames` frames each, measured over
// `elapsed_seconds`: the counts, each check, and the verdict.
inline auto report_text(int cycles, int frames, double elapsed_seconds,
                        const std::vector<SubCheck>& sub_checks) -> std::string {
    auto text =
        std::format("{{\n"
                    "  \"binding\": \"cpp\",\n"
                    "  \"cycles\": {},\n"
                    "  \"frames_per_cycle\": {},\n"
                    "  \"total_frames\": {},\n"
                    "  \"elapsed_seconds\": {},\n"
                    "  \"sub_checks\": [\n",
                    cycles, frames, static_cast<std::int64_t>(cycles) * frames, elapsed_seconds);
    for (auto const [i, c] : std::views::enumerate(sub_checks))
        std::format_to(std::back_inserter(text),
                       "{}    {{\n"
                       "      \"name\": \"{}\",\n"
                       "      \"gate\": \"{}\",\n"
                       "      \"start\": {},\n"
                       "      \"end\": {},\n"
                       "      \"delta\": {},\n"
                       "      \"threshold\": {},\n"
                       "      \"passed\": {}\n"
                       "    }}",
                       i == 0 ? "" : ",\n", c.name, c.gate, c.start, c.end, c.delta, c.threshold,
                       c.passed);
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

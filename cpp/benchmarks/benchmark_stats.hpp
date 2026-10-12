// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The summary statistics the benchmark modes reduce their samples to.

#include <cstddef>
#include <vector>

namespace aletheia::bench {

struct Stats {
    double mean = 0;
    double stdev = 0;
    double min_val = 0;
    double max_val = 0;
};

auto compute_stats(const std::vector<double>& data) -> Stats;

struct LatencyStats {
    std::size_t count = 0;
    double mean_us = 0;
    double min_us = 0;
    double max_us = 0;
    double p50_us = 0;
    double p90_us = 0;
    double p99_us = 0;
    double p999_us = 0;
};

auto compute_latency_stats(std::vector<double>& latencies_us) -> LatencyStats;

} // namespace aletheia::bench

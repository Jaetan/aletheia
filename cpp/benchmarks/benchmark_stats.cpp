// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The mean, spread and extremes of a set of runs, and the percentiles of a set of
// per-call latencies.

#include "benchmark_stats.hpp"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <numeric>
#include <vector>

// ---------------------------------------------------------------------------
// Statistics helpers
// ---------------------------------------------------------------------------

namespace aletheia::bench {

auto compute_stats(std::vector<double> const& data) -> Stats {
    if (data.empty())
        return {};
    auto const n = static_cast<double>(data.size());
    auto const sum = std::reduce(data.begin(), data.end(), 0.0);
    auto const mean = sum / n;
    double sq_sum = 0;
    for (auto const v : data)
        sq_sum += (v - mean) * (v - mean);
    auto const stdev = (data.size() > 1) ? std::sqrt(sq_sum / (n - 1.0)) : 0.0;
    return {
        .mean = mean,
        .stdev = stdev,
        .min_val = *std::ranges::min_element(data),
        .max_val = *std::ranges::max_element(data),
    };
}

} // namespace aletheia::bench

static auto percentile(std::vector<double> const& sorted, double p) -> double {
    if (sorted.empty())
        return 0.0;
    auto const k = static_cast<double>(sorted.size() - 1) * p / 100.0;
    auto const f = static_cast<std::size_t>(k);
    auto const c = (f + 1 < sorted.size()) ? f + 1 : f;
    return sorted.at(f) + ((k - static_cast<double>(f)) * (sorted.at(c) - sorted.at(f)));
}

namespace aletheia::bench {

auto compute_latency_stats(std::vector<double>& latencies_us) -> LatencyStats {
    if (latencies_us.empty())
        return {};
    std::ranges::sort(latencies_us);
    auto const sum = std::reduce(latencies_us.begin(), latencies_us.end(), 0.0);
    return {
        .count = latencies_us.size(),
        .mean_us = sum / static_cast<double>(latencies_us.size()),
        .min_us = latencies_us.front(),
        .max_us = latencies_us.back(),
        .p50_us = percentile(latencies_us, 50),
        .p90_us = percentile(latencies_us, 90),
        .p99_us = percentile(latencies_us, 99),
        .p999_us = percentile(latencies_us, 99.9),
    };
}

} // namespace aletheia::bench

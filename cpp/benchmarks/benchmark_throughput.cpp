// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The throughput mode: frames per second of streaming, extraction and building,
// over repeated runs.

#include "benchmark_throughput.hpp"
#include "benchmark_client.hpp"
#include "benchmark_fixtures.hpp"
#include "benchmark_output.hpp"
#include "benchmark_stats.hpp"
#include "benchmark_system.hpp"
#include "measure.hpp"

#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <cmath>
#include <filesystem>
#include <print>
#include <ranges>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

using aletheia::bench::Stats, aletheia::bench::bench_streaming, aletheia::bench::can20_dlc,
    aletheia::bench::can20_frame, aletheia::bench::can20_id, aletheia::bench::can20_signals,
    aletheia::bench::canfd_dlc, aletheia::bench::canfd_frame, aletheia::bench::canfd_id,
    aletheia::bench::canfd_signals, aletheia::bench::compute_stats, aletheia::bench::make_can20_dbc,
    aletheia::bench::make_can20_properties, aletheia::bench::make_canfd_dbc,
    aletheia::bench::make_canfd_properties, aletheia::bench::make_client,
    aletheia::bench::operations_per_second, aletheia::bench::out_file;
using aletheia::CanId, aletheia::DbcDefinition, aletheia::Dlc, aletheia::FramePayload,
    aletheia::SignalValue;
using Json = nlohmann::json;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Benchmark: throughput
// ---------------------------------------------------------------------------

namespace {
struct ThroughputResult {
    std::string name;
    int num_frames;
    int num_runs;
    Stats fps;
    std::vector<double> all_fps;
};
} // namespace

static auto bench_extraction(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                             const FramePayload& frame, int num_frames) -> double {
    auto client = make_client(lib, dbc);
    return operations_per_second(num_frames, "extract_signals", [&](auto) {
        return client.extract_signals(std::stop_token{}, id, dlc, frame);
    });
}

static auto bench_building(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                           const std::vector<SignalValue>& signals, int num_frames) -> double {
    auto client = make_client(lib, dbc);
    return operations_per_second(num_frames, "build_frame", [&](auto) {
        return client.build_frame(std::stop_token{}, id, dlc, signals);
    });
}

static auto run_throughput_bench(std::string name, auto bench_fn, int num_frames, int num_runs,
                                 int warmup_runs) -> ThroughputResult {
    // Warmup
    std::ranges::for_each(std::views::repeat(0, warmup_runs),
                          [&](auto) { bench_fn(num_frames / 10); });

    // Actual runs
    std::vector<double> results;
    results.reserve(num_runs);
    std::ranges::for_each(std::views::repeat(0, num_runs),
                          [&](auto) { results.push_back(bench_fn(num_frames)); });

    auto const stats = compute_stats(results);

    std::println(out_file(), "\n{}:", name);
    std::println(out_file(), "----------------------------------------");
    for (auto const [r, fps] : std::views::enumerate(results))
        std::println(out_file(), "  Run {}/{}: {:.0f} ops/sec", r + 1, num_runs, fps);

    return ThroughputResult{
        .name = std::move(name),
        .num_frames = num_frames,
        .num_runs = num_runs,
        .fps = stats,
        .all_fps = std::move(results),
    };
}

// The six measurements the throughput mode takes, in the order the summary
// table prints them.
static auto collect_throughput_results(const fs::path& lib, int num_frames, int num_runs,
                                       int warmup) -> std::vector<ThroughputResult> {
    auto const dbc_20 = make_can20_dbc();
    auto const dbc_fd = make_canfd_dbc();

    std::vector<ThroughputResult> results;

    // CAN 2.0B benchmarks
    results.push_back(run_throughput_bench(
        "CAN 2.0B: Stream LTL (2 props)",
        [&](int n) {
            return bench_streaming(lib, dbc_20, make_can20_properties(), can20_id, can20_dlc,
                                   can20_frame(), n);
        },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN 2.0B: Signal Extraction",
        [&](int n) { return bench_extraction(lib, dbc_20, can20_id, can20_dlc, can20_frame(), n); },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN 2.0B: Frame Building",
        [&](int n) { return bench_building(lib, dbc_20, can20_id, can20_dlc, can20_signals(), n); },
        num_frames, num_runs, warmup));

    // CAN-FD benchmarks
    results.push_back(run_throughput_bench(
        "CAN-FD:   Stream LTL (3 props)",
        [&](int n) {
            return bench_streaming(lib, dbc_fd, make_canfd_properties(), canfd_id, canfd_dlc,
                                   canfd_frame(), n);
        },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN-FD:   Signal Extraction",
        [&](int n) { return bench_extraction(lib, dbc_fd, canfd_id, canfd_dlc, canfd_frame(), n); },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN-FD:   Frame Building",
        [&](int n) { return bench_building(lib, dbc_fd, canfd_id, canfd_dlc, canfd_signals(), n); },
        num_frames, num_runs, warmup));
    return results;
}

namespace aletheia::bench {

void run_throughput(const fs::path& lib, int num_frames, int num_runs, int warmup, bool emit_json) {
    print_header("Aletheia Throughput Benchmark (C++)");
    std::println(out_file(), "Frames per run: {}", num_frames);
    std::println(out_file(), "Runs: {}", num_runs);
    std::println(out_file(), "Warmup runs: {}", warmup);

    auto const results = collect_throughput_results(lib, num_frames, num_runs, warmup);

    // Summary table
    std::println(out_file(), "");
    print_header("Summary");
    std::println(out_file(), "{:<35} {:>12} {:>10} {:>10} {:>10}", "Benchmark", "Mean", "Stdev",
                 "Min", "Max");
    print_separator();
    for (auto const& r : results) {
        std::println(out_file(), "{:<35} {:10.0f}/s {:9.0f} {:9.0f} {:9.0f}", r.name, r.fps.mean,
                     r.fps.stdev, r.fps.min_val, r.fps.max_val);
    }
    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json) {
        auto json_results = Json::array();
        for (auto const& r : results) {
            auto const us = (r.fps.mean > 0) ? 1'000'000.0 / r.fps.mean : 0;
            json_results.push_back({
                {"name", r.name},
                {"frames", r.num_frames},
                {"runs", r.num_runs},
                {"fps_mean", std::round(r.fps.mean * 10) / 10},
                {"fps_stdev", std::round(r.fps.stdev * 10) / 10},
                {"fps_min", std::round(r.fps.min_val * 10) / 10},
                {"fps_max", std::round(r.fps.max_val * 10) / 10},
                {"us_per_frame", std::round(us * 10) / 10},
            });
        }
        const Json output = {
            {"benchmark", "throughput"},
            {"language", "cpp"},
            {"timestamp", iso_timestamp()},
            {"system", get_system_info()},
            {"parameters", {{"frames", num_frames}, {"runs", num_runs}, {"warmup", warmup}}},
            {"results", json_results},
        };
        std::println("{}", output.dump(2));
    }
}

} // namespace aletheia::bench

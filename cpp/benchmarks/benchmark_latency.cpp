// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The latency mode: the time of each streaming, extraction and building call,
// reported as percentiles.

#include "benchmark_latency.hpp"
#include "benchmark_client.hpp"
#include "benchmark_fixtures.hpp"
#include "benchmark_output.hpp"
#include "benchmark_stats.hpp"
#include "benchmark_system.hpp"
#include "measure.hpp"

#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <cmath>
#include <filesystem>
#include <format>
#include <print>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

using aletheia::bench::LatencyStats, aletheia::bench::compute_latency_stats,
    aletheia::bench::latencies_us, aletheia::bench::make_client,
    aletheia::bench::make_streaming_client, aletheia::bench::out_file, aletheia::bench::require;
using aletheia::CanId, aletheia::DbcDefinition, aletheia::Dlc, aletheia::FramePayload,
    aletheia::LtlFormula, aletheia::SignalValue, aletheia::Timestamp;
using Json = nlohmann::json;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Benchmark: latency
// ---------------------------------------------------------------------------

namespace {
struct LatencyResult {
    std::string name;
    LatencyStats stats;
};
} // namespace

static void print_latency(std::string_view name, LatencyStats const& s) {
    std::println(out_file(), "\n{}:", name);
    std::println(out_file(), "--------------------------------------------------");
    std::println(out_file(), "  Count:    {} operations", s.count);
    std::println(out_file(), "  Mean:     {:.1f} us", s.mean_us);
    std::println(out_file(), "  Min:      {:.1f} us", s.min_us);
    std::println(out_file(), "  Max:      {:.1f} us", s.max_us);
    std::println(out_file(), "  p50:      {:.1f} us", s.p50_us);
    std::println(out_file(), "  p90:      {:.1f} us", s.p90_us);
    std::println(out_file(), "  p99:      {:.1f} us", s.p99_us);
    std::println(out_file(), "  p99.9:    {:.1f} us", s.p999_us);
    if (s.mean_us > 0)
        std::println(out_file(), "  Implied:  {:.0f} ops/sec (from mean)", 1'000'000.0 / s.mean_us);
}

static auto bench_latency_streaming(fs::path const& lib, DbcDefinition const& dbc,
                                    std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                                    FramePayload const& frame, int warmup, int ops)
    -> LatencyStats {
    auto client = make_streaming_client(lib, dbc, properties);
    // The stream reads timestamps in order, so the warmup frames carry the
    // first ones and the measured frames continue the count.
    auto latencies = latencies_us(warmup, ops, "send_frame", [&](int i) {
        return client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame);
    });
    require(client.end_stream(std::stop_token{}), "end_stream");
    return compute_latency_stats(latencies);
}

static auto bench_latency_extraction(fs::path const& lib, DbcDefinition const& dbc, CanId id,
                                     Dlc dlc, FramePayload const& frame, int warmup, int ops)
    -> LatencyStats {
    auto client = make_client(lib, dbc);
    auto latencies = latencies_us(warmup, ops, "extract_signals", [&](auto) {
        return client.extract_signals(std::stop_token{}, id, dlc, frame);
    });
    return compute_latency_stats(latencies);
}

static auto bench_latency_building(fs::path const& lib, DbcDefinition const& dbc, CanId id, Dlc dlc,
                                   std::vector<SignalValue> const& signals, int warmup, int ops)
    -> LatencyStats {
    auto client = make_client(lib, dbc);
    auto latencies = latencies_us(warmup, ops, "build_frame", [&](auto) {
        return client.build_frame(std::stop_token{}, id, dlc, signals);
    });
    return compute_latency_stats(latencies);
}

namespace aletheia::bench {

void run_latency(fs::path const& lib, int ops, int warmup, bool emit_json) {
    print_header("Aletheia Latency Benchmark (C++)");
    std::println(out_file(), "Operations: {}", ops);
    std::println(out_file(), "Warmup: {}", warmup);

    auto const dbc_20 = make_can20_dbc();
    auto const dbc_fd = make_canfd_dbc();

    std::vector<LatencyResult> results;

    auto const run_suite = [&](char const* label, DbcDefinition const& dbc,
                               std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                               FramePayload const& frame, std::vector<SignalValue> const& signals) {
        std::println(out_file(), "\nBenchmarking {} streaming...", label);
        auto const s1 =
            bench_latency_streaming(lib, dbc, std::move(properties), id, dlc, frame, warmup, ops);
        auto name = std::format("{} Streaming LTL", label);
        print_latency(name, s1);
        results.push_back({.name = name, .stats = s1});

        std::println(out_file(), "\nBenchmarking {} signal extraction...", label);
        auto const s2 = bench_latency_extraction(lib, dbc, id, dlc, frame, warmup, ops);
        name = std::format("{} Signal Extraction", label);
        print_latency(name, s2);
        results.push_back({.name = name, .stats = s2});

        std::println(out_file(), "\nBenchmarking {} frame building...", label);
        auto const s3 = bench_latency_building(lib, dbc, id, dlc, signals, warmup, ops);
        name = std::format("{} Frame Building", label);
        print_latency(name, s3);
        results.push_back({.name = name, .stats = s3});
    };

    run_suite("CAN 2.0B", dbc_20, make_can20_properties(), can20_id, can20_dlc, can20_frame(),
              can20_signals());
    run_suite("CAN-FD", dbc_fd, make_canfd_properties(), canfd_id, canfd_dlc, canfd_frame(),
              canfd_signals());

    // Summary table
    std::println(out_file(), "");
    print_header("Summary (all times in microseconds)");
    std::println(out_file(), "{:<30} {:>10} {:>10} {:>10} {:>10}", "Operation", "Mean", "p50",
                 "p99", "p99.9");
    print_separator();
    for (auto const& r : results) {
        std::println(out_file(), "{:<30} {:10.1f} {:10.1f} {:10.1f} {:10.1f}", r.name,
                     r.stats.mean_us, r.stats.p50_us, r.stats.p99_us, r.stats.p999_us);
    }
    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json) {
        auto json_results = Json::array();
        for (auto const& r : results) {
            json_results.push_back({
                {"name", r.name},
                {"count", r.stats.count},
                {"mean_us", std::round(r.stats.mean_us * 10) / 10},
                {"min_us", std::round(r.stats.min_us * 10) / 10},
                {"max_us", std::round(r.stats.max_us * 10) / 10},
                {"p50_us", std::round(r.stats.p50_us * 10) / 10},
                {"p90_us", std::round(r.stats.p90_us * 10) / 10},
                {"p99_us", std::round(r.stats.p99_us * 10) / 10},
                {"p999_us", std::round(r.stats.p999_us * 10) / 10},
            });
        }
        Json const output = {
            {"benchmark", "latency"},
            {"language", "cpp"},
            {"timestamp", iso_timestamp()},
            {"system", get_system_info()},
            {"parameters", {{"ops", ops}, {"warmup", warmup}}},
            {"results", json_results},
        };
        std::println("{}", output.dump(2));
    }
}

} // namespace aletheia::bench

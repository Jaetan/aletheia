// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The scaling mode: the streaming rate against trace length, property count and
// property complexity, and the DBC load time against the number of messages.

#include "benchmark_scaling.hpp"
#include "benchmark_client.hpp"
#include "benchmark_fixtures.hpp"
#include "benchmark_output.hpp"
#include "benchmark_stats.hpp"
#include "benchmark_system.hpp"
#include "measure.hpp"

#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <array>
#include <cmath>
#include <filesystem>
#include <format>
#include <print>
#include <ranges>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

using aletheia::AletheiaClient, aletheia::AlwaysPresent, aletheia::BitLength, aletheia::BitPosition,
    aletheia::ByteOrder, aletheia::CanId, aletheia::DbcComment, aletheia::DbcCommentTargetMessage,
    aletheia::DbcDefinition, aletheia::DbcNode, aletheia::DbcSignal, aletheia::Dlc,
    aletheia::ExtendedId, aletheia::FramePayload, aletheia::LtlFormula, aletheia::MessageName,
    aletheia::NodeName, aletheia::PhysicalValue, aletheia::Rational, aletheia::RationalBound,
    aletheia::RationalFactor, aletheia::RationalOffset, aletheia::SignalName, aletheia::Unit,
    aletheia::make_ffi_backend;
using aletheia::bench::bench_streaming, aletheia::bench::can20_dlc, aletheia::bench::can20_frame,
    aletheia::bench::can20_id, aletheia::bench::compute_stats, aletheia::bench::get_system_info,
    aletheia::bench::iso_timestamp, aletheia::bench::latencies_us, aletheia::bench::out_file,
    aletheia::bench::print_header, aletheia::bench::print_separator;
namespace ltl = aletheia::ltl;
namespace fs = std::filesystem;

// Scaling property templates (CAN 2.0B)
static auto make_scaling_property(int index) -> LtlFormula {
    // Rotate through different property definitions
    switch (index % 10) {
    case 0:
        return ltl::always(
            ltl::atomic(ltl::between(SignalName{"EngineSpeed"}, PhysicalValue{Rational{}},
                                     PhysicalValue{Rational{8000, 1}})));
    case 1:
        return ltl::always(
            ltl::atomic(ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-40, 1}},
                                     PhysicalValue{Rational{215, 1}})));
    case 2:
        return ltl::always(ltl::atomic(
            ltl::less_than(SignalName{"BrakePressure"}, PhysicalValue{Rational{13107, 2}})));
    case 3:
        return ltl::always(ltl::atomic(
            ltl::less_than(SignalName{"EngineSpeed"}, PhysicalValue{Rational{7000, 1}})));
    case 4:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"EngineTemp"}, PhysicalValue{Rational{200, 1}})));
    case 5:
        return ltl::always(ltl::atomic(
            ltl::less_than(SignalName{"BrakePressure"}, PhysicalValue{Rational{5000, 1}})));
    case 6:
        return ltl::always(
            ltl::atomic(ltl::between(SignalName{"EngineSpeed"}, PhysicalValue{Rational{500, 1}},
                                     PhysicalValue{Rational{7500, 1}})));
    case 7:
        return ltl::always(
            ltl::atomic(ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-20, 1}},
                                     PhysicalValue{Rational{180, 1}})));
    case 8:
        return ltl::always(
            ltl::atomic(ltl::between(SignalName{"BrakePressure"}, PhysicalValue{Rational{}},
                                     PhysicalValue{Rational{4000, 1}})));
    default:
        return ltl::always(ltl::atomic(
            ltl::less_than(SignalName{"EngineSpeed"}, PhysicalValue{Rational{6000, 1}})));
    }
}

// ---------------------------------------------------------------------------
// Benchmark: scaling
//
// Five sweeps emitted as a DICT keyed by sub-benchmark, in this exact order:
// trace_size_can20, trace_size_canfd, property_count, property_complexity,
// dbc_size. The canonical schema is benchmarks/SCHEMA.yaml; the semantic source
// is python/benchmarks/scaling.py; go/benchmarks/scaling.go runScaling is the
// conformant structural reference. Methodology (identical across bindings):
// every streaming sweep point is the MEAN fps over --runs streaming passes;
// relative = fps / (fps of the first row in the same sweep). A dbc_size point
// is the MINIMUM seconds over --runs DBC loads, each on a fresh client, and its
// relative compares messages per second to the first row's the same way.
// ---------------------------------------------------------------------------

namespace {
struct TraceSizeRow {
    int frames;
    double fps;
    double relative;
};
} // namespace

namespace {
struct PropCountRow {
    int properties;
    double fps;
    double us_per_frame;
    double relative;
};
} // namespace

namespace {
struct ComplexityRow {
    std::string complexity;
    double fps;
    double us_per_frame;
    double relative;
};
} // namespace

namespace {
struct DbcSizeRow {
    int messages;
    double seconds;
    double messages_per_sec;
    double relative;
};
} // namespace

// LtlFormula owns unique_ptr children (not copyable): clone the whole vector so
// each streaming pass gets its own tree.
static auto clone_props(const std::vector<LtlFormula>& props) -> std::vector<LtlFormula> {
    std::vector<LtlFormula> out;
    out.reserve(props.size());
    for (auto const& p : props)
        out.push_back(ltl::clone(p));
    return out;
}

// mean_fps averages streaming fps over num_runs passes (the robust methodology,
// identical across all four bindings — noise on an un-averaged baseline would
// multiply into every `relative` in the sweep).
static auto mean_fps(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                     const FramePayload& frame, const std::vector<LtlFormula>& props,
                     int num_frames, int num_runs) -> double {
    std::vector<double> fps_runs;
    fps_runs.reserve(num_runs);
    std::ranges::for_each(std::views::repeat(0, num_runs), [&](auto) {
        fps_runs.push_back(
            bench_streaming(lib, dbc, clone_props(props), id, dlc, frame, num_frames));
    });
    return compute_stats(fps_runs).mean;
}

static auto round1(double x) -> double {
    return std::round(x * 10) / 10;
}

static auto round3(double x) -> double {
    return std::round(x * 1000) / 1000;
}

static auto round4(double x) -> double {
    return std::round(x * 10000) / 10000;
}

static auto us_per_frame_of(double fps) -> double {
    return (fps > 0) ? 1'000'000.0 / fps : 0.0;
}

static auto relative_of(double fps, double baseline) -> double {
    return (baseline > 0) ? fps / baseline : 0.0;
}

static auto trace_sizes(bool quick) -> std::vector<int> {
    if (quick)
        return {1000, 5000, 10000, 50000};
    return {1000, 5000, 10000, 50000, 100000};
}

static auto dbc_sizes(bool quick) -> std::vector<int> {
    if (quick)
        return {2500, 5000, 10000};
    return {1250, 2500, 5000, 10000};
}

// The dbc_size sweep's DBC, identical in every binding, in which every kind of
// reference grows with the messages: message M{i} on extended ID 0x100000 + i
// carries one unsigned little-endian byte S{i}, is sent by node N{i} with
// N{(i + 1) % n} as its one additional sender, and S{i} is received by N{i};
// the nodes are N0 ... N{n - 1}, and one comment per message names it by its
// ID. Every name resolves, and no two messages share an ID, a name or a signal
// name, so every load succeeds.
static auto make_sized_dbc(int messages) -> DbcDefinition {
    auto const node = [messages](int i) { return NodeName{std::format("N{}", i % messages)}; };
    DbcDefinition sized{.version = "1.0"};
    sized.messages.reserve(static_cast<std::size_t>(messages));
    sized.nodes.reserve(static_cast<std::size_t>(messages));
    sized.comments.reserve(static_cast<std::size_t>(messages));
    for (auto const i : std::views::iota(0, messages)) {
        auto const id = CanId{ExtendedId::create(static_cast<std::uint32_t>(0x100000 + i)).value()};
        sized.messages.push_back({
            .id = id,
            .name = MessageName{std::format("M{}", i)},
            .dlc = Dlc::create(8).value(),
            .sender = node(i),
            .senders = {node(i + 1)},
            .signals = {DbcSignal{
                .name = SignalName{std::format("S{}", i)},
                .start_bit = BitPosition{0},
                .bit_length = BitLength{8},
                .byte_order = ByteOrder::LittleEndian,
                .is_signed = false,
                .factor = RationalFactor{Rational{1, 1}},
                .offset = RationalOffset{Rational{0, 1}},
                .minimum = RationalBound{Rational{0, 1}},
                .maximum = RationalBound{Rational{255, 1}},
                .unit = Unit{""},
                .presence = AlwaysPresent{},
                .receivers = {node(i)},
            }},
        });
        sized.nodes.push_back(DbcNode{.name = node(i)});
        sized.comments.push_back(
            DbcComment{.target = DbcCommentTargetMessage{.id = id}, .text = "c"});
    }
    return sized;
}

// One load's wall-clock seconds: a fresh client, and only its parse_dbc call
// timed. The client closes as it leaves scope, after the clock has stopped.
static auto load_seconds(const fs::path& lib, const DbcDefinition& dbc) -> double {
    AletheiaClient client(make_ffi_backend(lib));
    auto const timed = latencies_us(0, 1, "parse_dbc",
                                    [&](auto) { return client.parse_dbc(std::stop_token{}, dbc); });
    return timed.front() / 1'000'000.0;
}

// The least of num_runs load times: the minimum is the estimate of a load's
// work the host's other activity disturbs least.
static auto min_load_seconds(const fs::path& lib, const DbcDefinition& dbc, int num_runs)
    -> double {
    std::vector<double> seconds;
    seconds.reserve(num_runs);
    std::ranges::for_each(std::views::repeat(0, num_runs),
                          [&](auto) { seconds.push_back(load_seconds(lib, dbc)); });
    return compute_stats(seconds).min_val;
}

// always_between / always_less_than build the Always-wrapped atomic predicates
// the scaling sweeps share; the exact signals/bounds mirror scaling.py.
static auto always_between(const char* sig, Rational lo, Rational hi) -> LtlFormula {
    return ltl::always(
        ltl::atomic(ltl::between(SignalName{sig}, PhysicalValue{lo}, PhysicalValue{hi})));
}

static auto always_less_than(const char* sig, Rational value) -> LtlFormula {
    return ltl::always(ltl::atomic(ltl::less_than(SignalName{sig}, PhysicalValue{value})));
}

// The five property-complexity levels (CAN 2.0B), verbatim labels in order. The
// "Implication" level uses ltl::implies (antecedent -> consequent lowers to
// Or(Not(antecedent), consequent)).
static auto complexity_levels() -> std::vector<std::pair<std::string, std::vector<LtlFormula>>> {
    std::vector<std::pair<std::string, std::vector<LtlFormula>>> levels;

    {
        std::vector<LtlFormula> props;
        props.push_back(always_less_than("EngineSpeed", Rational{8000, 1}));
        levels.emplace_back("Simple predicate", std::move(props));
    }
    {
        std::vector<LtlFormula> props;
        props.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
        levels.emplace_back("Range predicate", std::move(props));
    }
    {
        std::vector<LtlFormula> props;
        props.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
        props.push_back(always_between("EngineTemp", Rational{-40, 1}, Rational{215, 1}));
        levels.emplace_back("Two predicates (AND)", std::move(props));
    }
    {
        std::vector<LtlFormula> props;
        props.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
        props.push_back(always_between("EngineTemp", Rational{-40, 1}, Rational{215, 1}));
        // BrakePressure bound is the RATIONAL 13107/2 (= 6553.5), not an integer.
        props.push_back(always_less_than("BrakePressure", Rational{13107, 2}));
        levels.emplace_back("Three predicates", std::move(props));
    }
    {
        std::vector<LtlFormula> props;
        props.push_back(ltl::always(
            ltl::implies(ltl::atomic(ltl::less_than(SignalName{"EngineSpeed"},
                                                    PhysicalValue{Rational{1000, 1}})),
                         ltl::atomic(ltl::less_than(SignalName{"EngineTemp"},
                                                    PhysicalValue{Rational{100, 1}})))));
        levels.emplace_back("Implication", std::move(props));
    }

    return levels;
}

// The scaling payload. Written through ordered_json rather than the default,
// because the schema pins the sub-benchmark key order and the whole document
// has to preserve insertion order end to end.
static void emit_scaling_json(int num_runs, bool quick,
                              const std::vector<TraceSizeRow>& trace_can20,
                              const std::vector<TraceSizeRow>& trace_canfd,
                              const std::vector<PropCountRow>& prop_count,
                              const std::vector<ComplexityRow>& complexity,
                              const std::vector<DbcSizeRow>& dbc_size) {
    // ordered_json (NOT default json, which sorts object keys alphabetically):
    // the schema pins the sub-benchmark key order, so the whole payload must
    // preserve insertion order end-to-end.
    using Ordered = nlohmann::ordered_json;

    auto const trace_json = [](const std::vector<TraceSizeRow>& rows) -> Ordered {
        auto arr = Ordered::array();
        for (auto const& r : rows)
            arr.push_back({
                {"frames", r.frames},
                {"fps", round1(r.fps)},
                {"relative", round3(r.relative)},
            });
        return arr;
    };

    auto prop_count_json = Ordered::array();
    for (auto const& r : prop_count)
        prop_count_json.push_back({
            {"properties", r.properties},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    auto complexity_json = Ordered::array();
    for (auto const& r : complexity)
        complexity_json.push_back({
            {"complexity", r.complexity},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    auto dbc_size_json = Ordered::array();
    for (auto const& r : dbc_size)
        dbc_size_json.push_back({
            {"messages", r.messages},
            {"seconds", round4(r.seconds)},
            {"messages_per_sec", round1(r.messages_per_sec)},
            {"relative", round3(r.relative)},
        });

    Ordered results;
    results["trace_size_can20"] = trace_json(trace_can20);
    results["trace_size_canfd"] = trace_json(trace_canfd);
    results["property_count"] = prop_count_json;
    results["property_complexity"] = complexity_json;
    results["dbc_size"] = dbc_size_json;

    Ordered output;
    output["benchmark"] = "scaling";
    output["language"] = "cpp";
    output["timestamp"] = iso_timestamp();
    output["system"] = get_system_info();
    output["parameters"] = {{"runs", num_runs}, {"quick", quick}};
    output["results"] = results;

    std::println("{}", output.dump(2));
}

// The property-count sweep: the same trace measured against a growing bundle,
// each count's rate reported against the first as a baseline.
static auto scan_property_count(const fs::path& lib, const DbcDefinition& dbc, int num_frames,
                                int num_runs) -> std::vector<PropCountRow> {
    std::println(out_file(), "");
    print_header("Property Count Scaling");
    std::println(out_file(), "{:>10} {:>12} {:>10} {:>10}", "Properties", "Frames/sec", "us/frame",
                 "Relative");
    print_separator();
    std::vector<PropCountRow> prop_count;
    {
        constexpr std::array counts{1, 2, 3, 5, 7, 10};
        double baseline = 0;
        for (auto const count : counts) {
            std::vector<LtlFormula> props;
            props.reserve(count);
            for (auto const i : std::views::iota(0, count))
                props.push_back(make_scaling_property(i));
            auto const fps =
                mean_fps(lib, dbc, can20_id, can20_dlc, can20_frame(), props, num_frames, num_runs);
            if (baseline == 0)
                baseline = fps;
            auto const relative = relative_of(fps, baseline);
            auto const us = us_per_frame_of(fps);
            std::println(out_file(), "{:10} {:12.0f} {:10.1f} {:10.2f}x", count, fps, us, relative);
            prop_count.push_back(
                {.properties = count, .fps = fps, .us_per_frame = us, .relative = relative});
        }
    }
    return prop_count;
}

// The property-complexity sweep (CAN 2.0B): the same trace measured against
// five labelled bundles, each level's rate reported against the first.
static auto scan_property_complexity(const fs::path& lib, const DbcDefinition& dbc, int num_frames,
                                     int num_runs) -> std::vector<ComplexityRow> {
    std::println(out_file(), "");
    print_header("Property Complexity Scaling");
    std::println(out_file(), "{:<25} {:>12} {:>10} {:>10}", "Complexity", "Frames/sec", "us/frame",
                 "Relative");
    print_separator();
    std::vector<ComplexityRow> complexity;
    double baseline = 0;
    for (auto const& [label, props] : complexity_levels()) {
        auto const fps =
            mean_fps(lib, dbc, can20_id, can20_dlc, can20_frame(), props, num_frames, num_runs);
        if (baseline == 0)
            baseline = fps;
        auto const relative = relative_of(fps, baseline);
        auto const us = us_per_frame_of(fps);
        std::println(out_file(), "{:<25} {:12.0f} {:10.1f} {:10.2f}x", label, fps, us, relative);
        complexity.push_back(
            {.complexity = label, .fps = fps, .us_per_frame = us, .relative = relative});
    }
    return complexity;
}

// The DBC-size sweep: a warm-up load whose time is discarded, then each size's
// minimum load time over num_runs loads, its rate reported against the first
// size's.
static auto scan_dbc_size(const fs::path& lib, int num_runs, bool quick)
    -> std::vector<DbcSizeRow> {
    [[maybe_unused]] auto const warmed = load_seconds(lib, make_sized_dbc(500));
    std::println(out_file(), "");
    print_header("5. DBC Size Scaling");
    std::println(out_file(), "{:>10} {:>10} {:>12} {:>10}", "Messages", "Time (s)", "Messages/sec",
                 "Relative");
    print_separator();
    std::vector<DbcSizeRow> rows;
    double baseline = 0;
    for (auto const size : dbc_sizes(quick)) {
        auto const seconds = min_load_seconds(lib, make_sized_dbc(size), num_runs);
        auto const rate = static_cast<double>(size) / seconds;
        if (baseline == 0)
            baseline = rate;
        auto const relative = relative_of(rate, baseline);
        std::println(out_file(), "{:10} {:10.4f} {:12.0f} {:10.2f}x", size, seconds, rate,
                     relative);
        rows.push_back(
            {.messages = size, .seconds = seconds, .messages_per_sec = rate, .relative = relative});
    }
    std::println(out_file(),
                 "Expected: Relative stays near 1.0x (load time linear in the number of messages)");
    return rows;
}

namespace aletheia::bench {

void run_scaling(const fs::path& lib, int num_runs, bool quick, bool emit_json) {
    print_header("Aletheia Scaling Benchmark (C++)");
    std::println(out_file(), "Runs: {}", num_runs);
    std::println(out_file(), "Quick: {}", quick ? "true" : "false");

    auto const dbc_20 = make_can20_dbc();
    auto const dbc_fd = make_canfd_dbc();
    auto const num_frames = quick ? 5000 : 10000;

    // Warmup
    std::println(out_file(), "\nWarming up...");
    {
        std::vector<LtlFormula> warm;
        warm.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
        [[maybe_unused]] auto const warmed =
            mean_fps(lib, dbc_20, can20_id, can20_dlc, can20_frame(), warm, 1000, 1);
    }
    std::println(out_file(), "Done.");

    // 1./2. Trace-size sweeps (CAN 2.0B, then CAN-FD).
    auto const scan_trace = [&](const char* title, const DbcDefinition& dbc, CanId id, Dlc dlc,
                                const FramePayload& frame,
                                const std::vector<LtlFormula>& props) -> std::vector<TraceSizeRow> {
        std::println(out_file(), "");
        print_header(title);
        std::println(out_file(), "{:>10} {:>12} {:>10}", "Frames", "Frames/sec", "Relative");
        print_separator();
        std::vector<TraceSizeRow> rows;
        double baseline = 0;
        for (auto const size : trace_sizes(quick)) {
            auto const fps = mean_fps(lib, dbc, id, dlc, frame, props, size, num_runs);
            if (baseline == 0)
                baseline = fps;
            auto const relative = relative_of(fps, baseline);
            std::println(out_file(), "{:10} {:12.0f} {:10.2f}x", size, fps, relative);
            rows.push_back({.frames = size, .fps = fps, .relative = relative});
        }
        return rows;
    };

    std::vector<LtlFormula> trace_props_can20;
    trace_props_can20.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
    auto const trace_can20 = scan_trace("Trace Size Scaling (CAN 2.0B)", dbc_20, can20_id,
                                        can20_dlc, can20_frame(), trace_props_can20);

    std::vector<LtlFormula> trace_props_canfd;
    trace_props_canfd.push_back(always_between("GPSSpeed", Rational{0, 1}, Rational{655, 1}));
    auto const trace_canfd = scan_trace("Trace Size Scaling (CAN-FD)", dbc_fd, canfd_id, canfd_dlc,
                                        canfd_frame(), trace_props_canfd);

    auto const prop_count = scan_property_count(lib, dbc_20, num_frames, num_runs);
    auto const complexity = scan_property_complexity(lib, dbc_20, num_frames, num_runs);
    auto const dbc_size = scan_dbc_size(lib, num_runs, quick);

    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json)
        emit_scaling_json(num_runs, quick, trace_can20, trace_canfd, prop_count, complexity,
                          dbc_size);
}

} // namespace aletheia::bench

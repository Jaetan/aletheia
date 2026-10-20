// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The scaling mode: the streaming rate against trace length, property count and
// property complexity, and a DBC load's time and allocated bytes against the
// number of messages and against the length of one number literal, written in a
// DBC text and in a parseDBC command.

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
#include <chrono>
#include <cmath>
#include <concepts>
#include <filesystem>
#include <format>
#include <print>
#include <ranges>
#include <stdexcept>
#include <stop_token>
#include <string>
#include <string_view>
#include <type_traits>
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
    aletheia::bench::iso_timestamp, aletheia::bench::out_file, aletheia::bench::print_header,
    aletheia::bench::print_separator, aletheia::bench::require;
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
// The sweeps are emitted as a DICT keyed by sub-benchmark, in this exact order:
// trace_size_can20, trace_size_canfd, property_count, property_complexity,
// dbc_size, text_literal_length, json_literal_length. The canonical schema is
// benchmarks/SCHEMA.yaml; the semantic source is python/benchmarks/scaling.py;
// go/benchmarks/scaling.go runScaling is the conformant structural reference.
// Methodology (identical across bindings): every streaming sweep point is the
// MEAN fps over --runs streaming passes; relative = fps / (fps of the first row
// in the same sweep). A dbc_size point is taken over --runs DBC loads and a
// text_literal_length point over --runs loads of a DBC text, each load on a
// fresh client, and a json_literal_length point over --runs parseDBC commands
// sent through the backend's raw command path, each on a fresh session. A
// point keeps the MINIMUM seconds of its loads and, taken apart, the MINIMUM
// allocated bytes, and its relative compares messages, or digits, per second
// to the first row's the same way. A load's allocated bytes are the kernel's
// allocation count read after the load less the count read before it, both
// read while the load's session is open and outside the timed span.
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
    std::uint64_t allocated_bytes;
    double messages_per_sec;
    double relative;
};
} // namespace

namespace {
struct LiteralLengthRow {
    int digits;
    double seconds;
    std::uint64_t allocated_bytes;
    double digits_per_sec;
    double relative;
};
} // namespace

namespace {
// What one DBC load cost: its wall-clock seconds and the bytes the kernel
// allocated while it ran.
struct LoadCost {
    double seconds;
    std::uint64_t allocated_bytes;
};
} // namespace

namespace {
// Every sweep's rows, one member a sweep, in the order the payload emits them.
struct ScalingResults {
    std::vector<TraceSizeRow> trace_size_can20;
    std::vector<TraceSizeRow> trace_size_canfd;
    std::vector<PropCountRow> property_count;
    std::vector<ComplexityRow> property_complexity;
    std::vector<DbcSizeRow> dbc_size;
    std::vector<LiteralLengthRow> text_literal_length;
    std::vector<LiteralLengthRow> json_literal_length;
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
// identical across the bindings; noise on an un-averaged baseline would
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

static auto literal_lengths(bool quick) -> std::vector<int> {
    if (quick)
        return {25000, 50000, 100000};
    return {12500, 25000, 50000, 100000};
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

// The text_literal_length sweep's DBC text, identical in every binding: one
// message whose one signal has the factor 1 written with `digits` zeros after
// the point. The kernel reduces the factor to 1, so every load succeeds, and
// what grows with `digits` is the literal the load reads.
static auto make_literal_text(int digits) -> std::string {
    return std::format("VERSION \"\"\n"
                       "\n"
                       "NS_ :\n"
                       "\n"
                       "BS_:\n"
                       "\n"
                       "BU_: ECU\n"
                       "\n"
                       "BO_ 200 Msg: 8 ECU\n"
                       " SG_ Sel : 0|8@1+ (1.{},0) [0|255] \"\" ECU\n",
                       std::string(static_cast<std::size_t>(digits), '0'));
}

// The json_literal_length sweep's command, identical in every binding:
// make_literal_text's DBC as one line of JSON with no spaces, the factor
// spliced in as written, since an encoder would write the number as 1.
static auto make_literal_command(int digits) -> std::string {
    return std::string{
               R"({"type":"command","command":"parseDBC","dbc":{"version":"","messages":[{"id":200,)"
               R"("name":"Msg","dlc":8,"sender":"ECU","senders":[],"extended":false,"signals":[{)"
               R"("name":"Sel","startBit":0,"length":8,"byteOrder":"little_endian","signed":false,)"
               R"("factor":1.)"} +
           std::string(static_cast<std::size_t>(digits), '0') +
           R"(,"offset":0,"minimum":0,"maximum":255,"unit":"","presence":"always",)"
           R"("receivers":["ECU"],"valueDescriptions":[]}]}],"signalGroups":[],)"
           R"("environmentVars":[],"valueTables":[],"nodes":[{"name":"ECU"}],"comments":[],)"
           R"("attributes":[],"unresolvedValueDescs":[]}})";
}

// The kernel's allocation count, read through the library that started the
// runtime: every read follows the making of a load's backend, which starts the
// runtime or finds it started, so the count is there to read.
static auto allocation_count() -> std::uint64_t {
    auto const count = aletheia::allocated_bytes();
    if (!count)
        throw std::runtime_error("allocated_bytes: no backend has started the kernel's runtime");
    return *count;
}

// The cost of one call of `run` on a session the caller holds open: the count
// is read, the clock started, `run` called, the clock stopped and the count
// read again, so neither the session's start nor its close lands in either
// figure. `run`'s answer comes back beside the cost, for the caller to check
// after both reads, so the check is in neither figure either.
template<std::invocable<> Run>
static auto timed_load(Run run) -> std::pair<LoadCost, std::invoke_result_t<Run>> {
    auto const before = allocation_count();
    auto const start = std::chrono::steady_clock::now();
    auto answer = run();
    auto const stop = std::chrono::steady_clock::now();
    auto const after = allocation_count();
    return {LoadCost{.seconds = std::chrono::duration<double>(stop - start).count(),
                     .allocated_bytes = after - before},
            std::move(answer)};
}

// One load's cost on a fresh client. A refused load throws, named by `step`.
template<std::invocable<AletheiaClient&> Load>
static auto client_load_cost(const fs::path& lib, std::string_view step, Load load) -> LoadCost {
    AletheiaClient client(make_ffi_backend(lib));
    auto const [cost, answer] = timed_load([&] { return load(client); });
    require(answer, step);
    return cost;
}

static auto dbc_load_cost(const fs::path& lib, const DbcDefinition& dbc) -> LoadCost {
    return client_load_cost(
        lib, std::format("parse_dbc of a {}-message DBC", dbc.messages.size()),
        [&](AletheiaClient& client) { return client.parse_dbc(std::stop_token{}, dbc); });
}

static auto text_load_cost(const fs::path& lib, int digits, std::string_view text) -> LoadCost {
    return client_load_cost(
        lib, std::format("parse_dbc_text of a {}-digit literal", digits),
        [&](AletheiaClient& client) { return client.parse_dbc_text(std::stop_token{}, text); });
}

// Throws unless `reply` is the kernel accepting the command: a reply that does
// not decode, or one whose status is not success, names the step and, for the
// second, the reply's status, code and message.
static void require_accepted(std::string_view step, const std::string& reply) {
    auto const answer = nlohmann::json::parse(reply, nullptr, false);
    if (!answer.is_object())
        throw std::runtime_error(
            std::format("{} failed: the reply does not decode as a JSON object", step));
    auto const status = answer.value("status", "");
    if (status != "success")
        throw std::runtime_error(std::format("{} failed: {}: {}: {}", step, status,
                                             answer.value("code", ""),
                                             answer.value("message", "")));
}

// One load's cost through the raw command path, on a fresh session of a fresh
// backend: the command is sent by `process` and its reply checked after both
// reads.
static auto command_load_cost(const fs::path& lib, int digits, std::string_view command)
    -> LoadCost {
    auto const backend = make_ffi_backend(lib);
    auto const state = backend->init();
    auto const [cost, reply] = timed_load([&] { return backend->process(state, command); });
    require_accepted(std::format("process of a {}-digit parseDBC command", digits), reply);
    return cost;
}

// The least seconds and the least allocated bytes of num_runs loads, each
// minimum taken apart: the minimum is the estimate of a load's work the host's
// other activity disturbs least. The argument parser holds num_runs to at
// least one, so there is a least.
template<std::invocable<> Measure>
static auto least_load_cost(int num_runs, Measure measure) -> LoadCost {
    std::vector<LoadCost> costs;
    costs.reserve(static_cast<std::size_t>(num_runs));
    std::ranges::for_each(std::views::repeat(0, num_runs),
                          [&](auto) { costs.push_back(measure()); });
    return {.seconds = std::ranges::min(costs, {}, &LoadCost::seconds).seconds,
            .allocated_bytes =
                std::ranges::min(costs, {}, &LoadCost::allocated_bytes).allocated_bytes};
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
static void emit_scaling_json(int num_runs, bool quick, const ScalingResults& sweeps) {
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
    for (auto const& r : sweeps.property_count)
        prop_count_json.push_back({
            {"properties", r.properties},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    auto complexity_json = Ordered::array();
    for (auto const& r : sweeps.property_complexity)
        complexity_json.push_back({
            {"complexity", r.complexity},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    auto dbc_size_json = Ordered::array();
    for (auto const& r : sweeps.dbc_size)
        dbc_size_json.push_back({
            {"messages", r.messages},
            {"seconds", round4(r.seconds)},
            {"allocated_bytes", r.allocated_bytes},
            {"messages_per_sec", round1(r.messages_per_sec)},
            {"relative", round3(r.relative)},
        });

    auto const literal_json = [](const std::vector<LiteralLengthRow>& rows) -> Ordered {
        auto arr = Ordered::array();
        for (auto const& r : rows)
            arr.push_back({
                {"digits", r.digits},
                {"seconds", round4(r.seconds)},
                {"allocated_bytes", r.allocated_bytes},
                {"digits_per_sec", round1(r.digits_per_sec)},
                {"relative", round3(r.relative)},
            });
        return arr;
    };

    Ordered results;
    results["trace_size_can20"] = trace_json(sweeps.trace_size_can20);
    results["trace_size_canfd"] = trace_json(sweeps.trace_size_canfd);
    results["property_count"] = prop_count_json;
    results["property_complexity"] = complexity_json;
    results["dbc_size"] = dbc_size_json;
    results["text_literal_length"] = literal_json(sweeps.text_literal_length);
    results["json_literal_length"] = literal_json(sweeps.json_literal_length);

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

// The DBC-size sweep: a warm-up load whose cost is discarded, then each size's
// least load time and least allocated bytes over num_runs loads, its rate
// reported against the first size's.
static auto scan_dbc_size(const fs::path& lib, int num_runs, bool quick)
    -> std::vector<DbcSizeRow> {
    [[maybe_unused]] auto const warmed = dbc_load_cost(lib, make_sized_dbc(500));
    std::println(out_file(), "");
    print_header("5. DBC Size Scaling");
    std::println(out_file(), "{:>10} {:>10} {:>14} {:>12} {:>10}", "Messages", "Time (s)",
                 "Allocated (B)", "Messages/sec", "Relative");
    print_separator();
    std::vector<DbcSizeRow> rows;
    double baseline = 0;
    for (auto const size : dbc_sizes(quick)) {
        auto const dbc = make_sized_dbc(size);
        auto const cost = least_load_cost(num_runs, [&] { return dbc_load_cost(lib, dbc); });
        auto const rate = static_cast<double>(size) / cost.seconds;
        if (baseline == 0)
            baseline = rate;
        auto const relative = relative_of(rate, baseline);
        std::println(out_file(), "{:10} {:10.4f} {:14} {:12.0f} {:10.2f}x", size, cost.seconds,
                     cost.allocated_bytes, rate, relative);
        rows.push_back({.messages = size,
                        .seconds = cost.seconds,
                        .allocated_bytes = cost.allocated_bytes,
                        .messages_per_sec = rate,
                        .relative = relative});
    }
    std::println(out_file(), "Expected: the allocated bytes double with the messages (the check "
                             "gates them; the time decides nothing)");
    return rows;
}

// A literal-length sweep through one route, `source` building what the route
// sends at a length and `load` loading it on a fresh session: a warm-up load of
// a 1000-digit literal whose cost is discarded, so an allocation the process
// makes once lands in no point, then each length's least load time and least
// allocated bytes over num_runs loads, its rate reported against the first
// length's.
template<std::invocable<int> Source, std::invocable<const fs::path&, int, std::string_view> Load>
static auto scan_literal_length(const fs::path& lib, int num_runs, bool quick,
                                std::string_view heading, Source source, Load load)
    -> std::vector<LiteralLengthRow> {
    [[maybe_unused]] auto const warmed = load(lib, 1000, source(1000));
    std::println(out_file(), "");
    print_header(heading);
    std::println(out_file(), "{:>10} {:>10} {:>14} {:>12} {:>10}", "Digits", "Time (s)",
                 "Allocated (B)", "Digits/sec", "Relative");
    print_separator();
    std::vector<LiteralLengthRow> rows;
    double baseline = 0;
    for (auto const digits : literal_lengths(quick)) {
        auto const sent = source(digits);
        auto const cost = least_load_cost(num_runs, [&] { return load(lib, digits, sent); });
        auto const rate = static_cast<double>(digits) / cost.seconds;
        if (baseline == 0)
            baseline = rate;
        auto const relative = relative_of(rate, baseline);
        std::println(out_file(), "{:10} {:10.4f} {:14} {:12.0f} {:10.2f}x", digits, cost.seconds,
                     cost.allocated_bytes, rate, relative);
        rows.push_back({.digits = digits,
                        .seconds = cost.seconds,
                        .allocated_bytes = cost.allocated_bytes,
                        .digits_per_sec = rate,
                        .relative = relative});
    }
    std::println(out_file(), "Expected: the allocated bytes double with the digits (the check "
                             "gates them; the time decides nothing)");
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
    std::vector<LtlFormula> trace_props_canfd;
    trace_props_canfd.push_back(always_between("GPSSpeed", Rational{0, 1}, Rational{655, 1}));

    // The sweeps run in the order their members are initialised, which is the
    // order the payload emits them; the literal sweeps load one number of
    // growing digits through the DBC text and through a parseDBC command.
    auto const sweeps = ScalingResults{
        .trace_size_can20 = scan_trace("Trace Size Scaling (CAN 2.0B)", dbc_20, can20_id, can20_dlc,
                                       can20_frame(), trace_props_can20),
        .trace_size_canfd = scan_trace("Trace Size Scaling (CAN-FD)", dbc_fd, canfd_id, canfd_dlc,
                                       canfd_frame(), trace_props_canfd),
        .property_count = scan_property_count(lib, dbc_20, num_frames, num_runs),
        .property_complexity = scan_property_complexity(lib, dbc_20, num_frames, num_runs),
        .dbc_size = scan_dbc_size(lib, num_runs, quick),
        .text_literal_length =
            scan_literal_length(lib, num_runs, quick, "6. Text Literal Length Scaling",
                                make_literal_text, text_load_cost),
        .json_literal_length =
            scan_literal_length(lib, num_runs, quick, "7. JSON Literal Length Scaling",
                                make_literal_command, command_load_cost),
    };

    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json)
        emit_scaling_json(num_runs, quick, sweeps);
}

} // namespace aletheia::bench

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++ Benchmark
//
// Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
// through the Aletheia FFI backend.
//
// Usage: ./benchmark [throughput|latency|scaling] [--frames N] [--runs N] [--quick] [--json]

#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <array>
#include <charconv>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <format>
#include <fstream>
#include <functional>
#include <memory>
#include <print>
#include <ratio>
#include <span>
#include <stdexcept>
#include <stop_token>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

// The names this harness uses, declared rather than pulled in wholesale, so a
// reader sees which part of the API a benchmark touches.
using aletheia::AletheiaClient, aletheia::AlwaysPresent, aletheia::BitLength, aletheia::BitPosition,
    aletheia::ByteOrder, aletheia::CanId, aletheia::DbcDefinition, aletheia::DbcMessage,
    aletheia::DbcSignal, aletheia::Dlc, aletheia::FramePayload, aletheia::LtlFormula,
    aletheia::MessageName, aletheia::NodeName, aletheia::PhysicalValue, aletheia::Rational,
    aletheia::RationalBound, aletheia::RationalFactor, aletheia::RationalOffset, aletheia::Result,
    aletheia::SignalName, aletheia::SignalValue, aletheia::StandardId, aletheia::Timestamp,
    aletheia::Unit, aletheia::make_ffi_backend;
namespace ltl = aletheia::ltl;
using Json = nlohmann::json;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Library discovery
// ---------------------------------------------------------------------------

// The binding's one search; a benchmark that found a different library than
// the client under test would be measuring something else.
static auto find_lib() -> fs::path {
    auto found = aletheia::find_ffi_library();
    if (found.empty()) {
        std::println(stderr, "ERROR: libaletheia-ffi.so not found.\n"
                             "Set ALETHEIA_LIB or run 'cabal run shake -- build'.");
        std::exit(1);
    }
    return found;
}

// ---------------------------------------------------------------------------
// System info
// ---------------------------------------------------------------------------

static auto get_cpu_model() -> std::string {
    std::ifstream cpuinfo("/proc/cpuinfo");
    for (std::string line; std::getline(cpuinfo, line);) {
        if (line.starts_with("model name")) {
            if (auto colon = line.find(':'); colon != std::string::npos)
                return line.substr(colon + 2); // skip ": "
        }
    }
    return "unknown";
}

// NDEBUG is defined by CMake's Release/RelWithDebInfo/MinSizeRel build types.
// An absent NDEBUG means an unoptimized build — a silent 20%+ regression. We
// expose the build type via get_system_info() and fail loudly at startup in
// check_release_build() below.
#ifdef NDEBUG
constexpr auto k_build_type = "Release";
#else
constexpr auto k_build_type = "Debug";
#endif

static void check_release_build() {
#ifndef NDEBUG
    std::print(stderr,
               "ERROR: C++ benchmark built without NDEBUG (Debug build).\n"
               "       Reconfigure with -DCMAKE_BUILD_TYPE=Release:\n"
               "         rm -rf cpp/build && cmake -B cpp/build -DCMAKE_BUILD_TYPE=Release \\\n"
               "           && cmake --build cpp/build\n");
    std::exit(1);
#endif
}

static auto get_system_info() -> Json {
    return {
        {"cpu", get_cpu_model()},
        {"cores", static_cast<int>(std::thread::hardware_concurrency())},
        {"platform", "Linux"},
        {"build_type", k_build_type},
    };
}

static auto iso_timestamp() -> std::string {
    auto now = std::chrono::floor<std::chrono::seconds>(std::chrono::system_clock::now());
    return std::format("{:%FT%TZ}", now);
}

// ---------------------------------------------------------------------------
// DBC definitions, built in code. The signal layouts are those of
// examples/example.dbc (EngineStatus, BrakeStatus) and examples/example_canfd.dbc
// (SensorFusion); senders and the files' other messages are not needed here, and
// every binding's benchmark builds these same definitions.
// ---------------------------------------------------------------------------

static auto make_can20_dbc() -> DbcDefinition {
    // EngineStatus: ID=0x100, DLC=8, sender=ECU1
    DbcSignal engine_speed{
        .name = SignalName{"EngineSpeed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 4}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{8000, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };
    DbcSignal engine_temp{
        .name = SignalName{"EngineTemp"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{-40, 1}},
        .minimum = RationalBound{Rational{-40, 1}},
        .maximum = RationalBound{Rational{215, 1}},
        .unit = Unit{"celsius"},
        .presence = AlwaysPresent{},
    };

    DbcMessage engine_msg{
        .id = CanId{StandardId::create(0x100).value()},
        .name = MessageName{"EngineStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU1"},
        .signals = {engine_speed, engine_temp},
    };

    // BrakeStatus: ID=0x200, DLC=8, sender=ECU2
    DbcSignal brake_pressure{
        .name = SignalName{"BrakePressure"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 10}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 10}},
        .unit = Unit{"bar"},
        .presence = AlwaysPresent{},
    };
    DbcSignal brake_pressed{
        .name = SignalName{"BrakePressed"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{1},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{1, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };

    DbcMessage brake_msg{
        .id = CanId{StandardId::create(0x200).value()},
        .name = MessageName{"BrakeStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU2"},
        .signals = {brake_pressure, brake_pressed},
    };

    return DbcDefinition{.version = "", .messages = {engine_msg, brake_msg}};
}

static auto make_canfd_dbc() -> DbcDefinition {
    // Helper to build a signal with common defaults
    auto sig = [](const char* name, std::uint16_t start, std::uint8_t len, bool is_signed,
                  Rational factor, Rational offset, Rational min_val, Rational max_val,
                  const char* unit) -> DbcSignal {
        return DbcSignal{
            .name = SignalName{name},
            .start_bit = BitPosition{start},
            .bit_length = BitLength{len},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = is_signed,
            .factor = RationalFactor{factor},
            .offset = RationalOffset{offset},
            .minimum = RationalBound{min_val},
            .maximum = RationalBound{max_val},
            .unit = Unit{unit},
            .presence = AlwaysPresent{},
        };
    };

    DbcMessage sensor_fusion{
        .id = CanId{StandardId::create(0x200).value()},
        .name = MessageName{"SensorFusion"},
        .dlc = Dlc::create(15).value(),
        .sender = NodeName{"SensorGateway"},
        .signals =
            {
                sig("GPSLatitude", 0, 32, true, {1, 10000000}, {0, 1}, {-90, 1}, {90, 1}, "deg"),
                sig("GPSLongitude", 32, 32, true, {1, 10000000}, {0, 1}, {-180, 1}, {180, 1},
                    "deg"),
                sig("GPSAltitude", 64, 16, true, {1, 10}, {0, 1}, {-1000, 1}, {11107, 2}, "m"),
                sig("GPSSpeed", 80, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("YawRate", 96, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "deg/s"),
                sig("LateralAccel", 112, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "m/s2"),
                sig("LongAccel", 128, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "m/s2"),
                sig("SteeringAngle", 144, 16, true, {1, 10}, {0, 1}, {-32768, 10}, {32767, 10},
                    "deg"),
                sig("WheelSpeedFL", 160, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedFR", 176, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedRL", 192, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedRR", 208, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("BrakeTempFL", 224, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempFR", 236, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempRL", 248, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempRR", 260, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("TirePressFL", 272, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressFR", 280, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressRL", 288, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressRR", 296, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("SensorStatus", 304, 8, false, {1, 1}, {0, 1}, {0, 1}, {255, 1}, ""),
                sig("IMUTemp", 312, 8, true, {1, 1}, {-40, 1}, {-40, 1}, {215, 1}, "celsius"),
                sig("BatteryVolt", 320, 12, false, {1, 100}, {0, 1}, {0, 1}, {4095, 100}, "V"),
                sig("GPSHeading", 332, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "deg"),
                sig("TimestampMs", 348, 32, false, {1, 1}, {0, 1}, {0, 1}, {4294967295, 1}, "ms"),
            },
    };

    return DbcDefinition{.version = "", .messages = {sensor_fusion}};
}

// ---------------------------------------------------------------------------
// Frame payloads
// ---------------------------------------------------------------------------

// The payload fixtures are function-local: a container at namespace scope
// runs its constructor before main, where a throw cannot be caught.
static auto can20_frame() -> const FramePayload& {
    static const FramePayload frame = {
        std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
        std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00},
    };
    return frame;
}
static constexpr auto can20_id = CanId{StandardId::create(0x100).value()};
static constexpr auto can20_dlc = Dlc::create(8).value();

static auto make_canfd_frame() -> FramePayload {
    FramePayload frame(64, std::byte{0x00});
    // GPSLatitude  (raw ~100000000 -> 10.0 deg)
    frame[0] = std::byte{0x00};
    frame[1] = std::byte{0xE1};
    frame[2] = std::byte{0xF5};
    frame[3] = std::byte{0x05};
    // GPSLongitude (raw ~48100000 -> 4.81 deg)
    frame[4] = std::byte{0x00};
    frame[5] = std::byte{0x6C};
    frame[6] = std::byte{0xDC};
    frame[7] = std::byte{0x02};
    // GPSAltitude  (raw 1000 -> 100.0 m)
    frame[8] = std::byte{0xE8};
    frame[9] = std::byte{0x03};
    // GPSSpeed     (raw 2000 -> 20.0 m/s)
    frame[10] = std::byte{0xD0};
    frame[11] = std::byte{0x07};
    // YawRate, LateralAccel, LongAccel, SteeringAngle: all 0
    // WheelSpeedFL (raw 1000 -> 10.0 m/s)
    frame[20] = std::byte{0xE8};
    frame[21] = std::byte{0x03};
    // WheelSpeedFR
    frame[22] = std::byte{0xE8};
    frame[23] = std::byte{0x03};
    // WheelSpeedRL
    frame[24] = std::byte{0xE8};
    frame[25] = std::byte{0x03};
    // WheelSpeedRR
    frame[26] = std::byte{0xE8};
    frame[27] = std::byte{0x03};
    return frame;
}

static auto canfd_frame() -> const FramePayload& {
    static const FramePayload frame = make_canfd_frame();
    return frame;
}
static constexpr auto canfd_id = CanId{StandardId::create(0x200).value()};
static constexpr auto canfd_dlc = Dlc::create(15).value();

// CAN 2.0B signal values for frame building
static auto can20_signals() -> const std::vector<SignalValue>& {
    static const std::vector<SignalValue> values = {
        {.name = SignalName{"EngineSpeed"}, .value = PhysicalValue{Rational{2000, 1}}},
        {.name = SignalName{"EngineTemp"}, .value = PhysicalValue{Rational{90, 1}}},
    };
    return values;
}

// CAN-FD signal values for frame building
static auto canfd_signals() -> const std::vector<SignalValue>& {
    static const std::vector<SignalValue> values = {
        {.name = SignalName{"GPSSpeed"}, .value = PhysicalValue{Rational{20, 1}}},
        {.name = SignalName{"YawRate"}, .value = PhysicalValue{Rational{}}},
        {.name = SignalName{"WheelSpeedFL"}, .value = PhysicalValue{Rational{10, 1}}},
        {.name = SignalName{"WheelSpeedFR"}, .value = PhysicalValue{Rational{10, 1}}},
    };
    return values;
}

// ---------------------------------------------------------------------------
// LTL properties
// ---------------------------------------------------------------------------

static auto make_can20_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"EngineSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{8000, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-40, 1}},
                                 PhysicalValue{Rational{215, 1}}))));
    return props;
}

static auto make_canfd_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"GPSSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::between(SignalName{"YawRate"}, PhysicalValue{Rational{-327, 1}},
                                 PhysicalValue{Rational{327, 1}}))));
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"WheelSpeedFL"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    return props;
}

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
// Statistics helpers
// ---------------------------------------------------------------------------

namespace {
struct Stats {
    double mean = 0;
    double stdev = 0;
    double min_val = 0;
    double max_val = 0;
};
} // namespace

static auto compute_stats(const std::vector<double>& data) -> Stats {
    if (data.empty())
        return {};
    auto n = static_cast<double>(data.size());
    const double sum = std::ranges::fold_left(data, 0.0, std::plus{});
    const double mean = sum / n;
    double sq_sum = 0;
    for (auto v : data)
        sq_sum += (v - mean) * (v - mean);
    const double stdev = (data.size() > 1) ? std::sqrt(sq_sum / (n - 1.0)) : 0.0;
    return {
        .mean = mean,
        .stdev = stdev,
        .min_val = *std::ranges::min_element(data),
        .max_val = *std::ranges::max_element(data),
    };
}

namespace {
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
} // namespace

static auto percentile(const std::vector<double>& sorted, double p) -> double {
    if (sorted.empty())
        return 0.0;
    const double k = static_cast<double>(sorted.size() - 1) * p / 100.0;
    auto f = static_cast<std::size_t>(k);
    auto c = (f + 1 < sorted.size()) ? f + 1 : f;
    return sorted[f] + ((k - static_cast<double>(f)) * (sorted[c] - sorted[f]));
}

static auto compute_latency_stats(std::vector<double>& latencies_us) -> LatencyStats {
    if (latencies_us.empty())
        return {};
    std::ranges::sort(latencies_us);
    const double sum = std::ranges::fold_left(latencies_us, 0.0, std::plus{});
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

// ---------------------------------------------------------------------------
// Output helpers
// ---------------------------------------------------------------------------

// Output destination: stderr when --json is set, stdout otherwise. Held in a
// function-local static so the destination is reachable without a mutable
// object at namespace scope.
static auto out_file() -> std::FILE*& {
    static std::FILE* destination = stdout;
    return destination;
}

static constexpr std::string_view k_rule_heavy =
    "======================================================================";
static constexpr std::string_view k_rule_light =
    "----------------------------------------------------------------------";

static void print_header(std::string_view title) {
    std::println(out_file(), "{}\n{}\n{}", k_rule_heavy, title, k_rule_heavy);
}

static void print_separator() {
    std::println(out_file(), "{}", k_rule_light);
}

// ---------------------------------------------------------------------------
// Client setup shared by every benchmark
// ---------------------------------------------------------------------------

// A benchmark must never time a client whose setup failed, so every setup
// step that returns std::expected is checked and its error thrown.
template<typename T>
static auto require(Result<T> result, std::string_view step) -> T {
    if (!result)
        throw std::runtime_error(std::format("{} failed: {}", step, result.error().message()));
    if constexpr (!std::is_void_v<T>)
        return std::move(*result);
}

static auto make_client(const fs::path& lib, const DbcDefinition& dbc) -> AletheiaClient {
    AletheiaClient client(make_ffi_backend(lib));
    require(client.parse_dbc(std::stop_token{}, dbc), "parse_dbc");
    return client;
}

static auto make_streaming_client(const fs::path& lib, const DbcDefinition& dbc,
                                  std::span<const LtlFormula> properties) -> AletheiaClient {
    auto client = make_client(lib, dbc);
    require(client.set_properties(std::stop_token{}, properties), "set_properties");
    require(client.start_stream(std::stop_token{}), "start_stream");
    return client;
}

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

static auto bench_streaming(const fs::path& lib, const DbcDefinition& dbc,
                            std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                            const FramePayload& frame, int num_frames) -> double {
    auto client = make_streaming_client(lib, dbc, properties);

    auto start = std::chrono::steady_clock::now();
    for (int i = 0; i < num_frames; ++i) [[maybe_unused]]
        const auto sent = client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame);
    auto end = std::chrono::steady_clock::now();

    [[maybe_unused]] const auto ended = client.end_stream(std::stop_token{});

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto bench_extraction(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                             const FramePayload& frame, int num_frames) -> double {
    auto client = make_client(lib, dbc);

    auto start = std::chrono::steady_clock::now();
    for (int i = 0; i < num_frames; ++i) [[maybe_unused]]
        const auto extracted = client.extract_signals(std::stop_token{}, id, dlc, frame);
    auto end = std::chrono::steady_clock::now();

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto bench_building(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                           const std::vector<SignalValue>& signals, int num_frames) -> double {
    auto client = make_client(lib, dbc);

    auto start = std::chrono::steady_clock::now();
    for (int i = 0; i < num_frames; ++i) [[maybe_unused]]
        const auto built = client.build_frame(std::stop_token{}, id, dlc, signals);
    auto end = std::chrono::steady_clock::now();

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto run_throughput_bench(std::string name, auto bench_fn, int num_frames, int num_runs,
                                 int warmup_runs) -> ThroughputResult {
    // Warmup
    for (int w = 0; w < warmup_runs; ++w)
        bench_fn(num_frames / 10);

    // Actual runs
    std::vector<double> results;
    results.reserve(num_runs);
    for (int r = 0; r < num_runs; ++r) {
        const double fps = bench_fn(num_frames);
        results.push_back(fps);
    }

    auto stats = compute_stats(results);

    std::println(out_file(), "\n{}:", name);
    std::println(out_file(), "----------------------------------------");
    for (int r = 0; r < num_runs; ++r)
        std::println(out_file(), "  Run {}/{}: {:.0f} ops/sec", r + 1, num_runs, results[r]);

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
    auto dbc_20 = make_can20_dbc();
    auto dbc_fd = make_canfd_dbc();

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

static void run_throughput(const fs::path& lib, int num_frames, int num_runs, int warmup,
                           bool emit_json) {
    print_header("Aletheia Throughput Benchmark (C++)");
    std::println(out_file(), "Frames per run: {}", num_frames);
    std::println(out_file(), "Runs: {}", num_runs);
    std::println(out_file(), "Warmup runs: {}", warmup);

    const auto results = collect_throughput_results(lib, num_frames, num_runs, warmup);

    // Summary table
    std::println(out_file(), "");
    print_header("Summary");
    std::println(out_file(), "{:<35} {:>12} {:>10} {:>10} {:>10}", "Benchmark", "Mean", "Stdev",
                 "Min", "Max");
    print_separator();
    for (const auto& r : results) {
        std::println(out_file(), "{:<35} {:10.0f}/s {:9.0f} {:9.0f} {:9.0f}", r.name, r.fps.mean,
                     r.fps.stdev, r.fps.min_val, r.fps.max_val);
    }
    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json) {
        Json json_results = Json::array();
        for (const auto& r : results) {
            const double us = (r.fps.mean > 0) ? 1'000'000.0 / r.fps.mean : 0;
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
            {"benchmark", "throughput"},    {"language", "cpp"},
            {"timestamp", iso_timestamp()}, {"system", get_system_info()},
            {"results", json_results},
        };
        std::println("{}", output.dump(2));
    }
}

// ---------------------------------------------------------------------------
// Benchmark: latency
// ---------------------------------------------------------------------------

namespace {
struct LatencyResult {
    std::string name;
    LatencyStats stats;
};
} // namespace

static void print_latency(std::string_view name, const LatencyStats& s) {
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

static auto bench_latency_streaming(const fs::path& lib, const DbcDefinition& dbc,
                                    std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                                    const FramePayload& frame, int warmup, int ops)
    -> LatencyStats {
    auto client = make_streaming_client(lib, dbc, properties);

    // Warmup
    for (int i = 0; i < warmup; ++i) [[maybe_unused]]
        const auto sent = client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::steady_clock::now();
        [[maybe_unused]] const auto sent =
            client.send_frame(std::stop_token{}, Timestamp{warmup + i}, id, dlc, frame);
        auto end = std::chrono::steady_clock::now();
        auto us = std::chrono::duration<double, std::micro>(end - start).count();
        latencies.push_back(us);
    }

    [[maybe_unused]] const auto ended = client.end_stream(std::stop_token{});
    return compute_latency_stats(latencies);
}

static auto bench_latency_extraction(const fs::path& lib, const DbcDefinition& dbc, CanId id,
                                     Dlc dlc, const FramePayload& frame, int warmup, int ops)
    -> LatencyStats {
    auto client = make_client(lib, dbc);

    // Warmup
    for (int i = 0; i < warmup; ++i) [[maybe_unused]]
        const auto extracted = client.extract_signals(std::stop_token{}, id, dlc, frame);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::steady_clock::now();
        [[maybe_unused]] const auto extracted =
            client.extract_signals(std::stop_token{}, id, dlc, frame);
        auto end = std::chrono::steady_clock::now();
        latencies.push_back(std::chrono::duration<double, std::micro>(end - start).count());
    }

    return compute_latency_stats(latencies);
}

static auto bench_latency_building(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                                   const std::vector<SignalValue>& signals, int warmup, int ops)
    -> LatencyStats {
    auto client = make_client(lib, dbc);

    // Warmup
    for (int i = 0; i < warmup; ++i) [[maybe_unused]]
        const auto built = client.build_frame(std::stop_token{}, id, dlc, signals);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::steady_clock::now();
        [[maybe_unused]] const auto built = client.build_frame(std::stop_token{}, id, dlc, signals);
        auto end = std::chrono::steady_clock::now();
        latencies.push_back(std::chrono::duration<double, std::micro>(end - start).count());
    }

    return compute_latency_stats(latencies);
}

static void run_latency(const fs::path& lib, int ops, int warmup, bool emit_json) {
    print_header("Aletheia Latency Benchmark (C++)");
    std::println(out_file(), "Operations: {}", ops);
    std::println(out_file(), "Warmup: {}", warmup);

    auto dbc_20 = make_can20_dbc();
    auto dbc_fd = make_canfd_dbc();

    std::vector<LatencyResult> results;

    auto run_suite = [&](const char* label, const DbcDefinition& dbc,
                         std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                         const FramePayload& frame, const std::vector<SignalValue>& signals) {
        std::println(out_file(), "\nBenchmarking {} streaming...", label);
        auto s1 =
            bench_latency_streaming(lib, dbc, std::move(properties), id, dlc, frame, warmup, ops);
        auto name = std::format("{} Streaming LTL", label);
        print_latency(name, s1);
        results.push_back({.name = name, .stats = s1});

        std::println(out_file(), "\nBenchmarking {} signal extraction...", label);
        auto s2 = bench_latency_extraction(lib, dbc, id, dlc, frame, warmup, ops);
        name = std::format("{} Signal Extraction", label);
        print_latency(name, s2);
        results.push_back({.name = name, .stats = s2});

        std::println(out_file(), "\nBenchmarking {} frame building...", label);
        auto s3 = bench_latency_building(lib, dbc, id, dlc, signals, warmup, ops);
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
    for (const auto& r : results) {
        std::println(out_file(), "{:<30} {:10.1f} {:10.1f} {:10.1f} {:10.1f}", r.name,
                     r.stats.mean_us, r.stats.p50_us, r.stats.p99_us, r.stats.p999_us);
    }
    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json) {
        Json json_results = Json::array();
        for (const auto& r : results) {
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
        const Json output = {
            {"benchmark", "latency"},       {"language", "cpp"},
            {"timestamp", iso_timestamp()}, {"system", get_system_info()},
            {"results", json_results},
        };
        std::println("{}", output.dump(2));
    }
}

// ---------------------------------------------------------------------------
// Benchmark: scaling
//
// Four sweeps emitted as a DICT keyed by sub-benchmark, in this exact order:
// trace_size_can20, trace_size_canfd, property_count, property_complexity.
// The canonical schema is benchmarks/SCHEMA.yaml; the semantic source is
// python/benchmarks/scaling.py; go/benchmarks/main.go runScaling is the
// conformant structural reference. Methodology (identical across bindings):
// every sweep point is the MEAN fps over --runs streaming passes;
// relative = fps / (fps of the first row in the same sweep).
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

// LtlFormula owns unique_ptr children (not copyable): clone the whole vector so
// each streaming pass gets its own tree.
static auto clone_props(const std::vector<LtlFormula>& props) -> std::vector<LtlFormula> {
    std::vector<LtlFormula> out;
    out.reserve(props.size());
    for (const auto& p : props)
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
    for (int r = 0; r < num_runs; ++r)
        fps_runs.push_back(
            bench_streaming(lib, dbc, clone_props(props), id, dlc, frame, num_frames));
    return compute_stats(fps_runs).mean;
}

static auto round1(double x) -> double {
    return std::round(x * 10) / 10;
}

static auto round3(double x) -> double {
    return std::round(x * 1000) / 1000;
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
static void emit_scaling_json(const std::vector<TraceSizeRow>& trace_can20,
                              const std::vector<TraceSizeRow>& trace_canfd,
                              const std::vector<PropCountRow>& prop_count,
                              const std::vector<ComplexityRow>& complexity) {
    // ordered_json (NOT default json, which sorts object keys alphabetically):
    // the schema pins the sub-benchmark key order, so the whole payload must
    // preserve insertion order end-to-end.
    using Ordered = nlohmann::ordered_json;

    auto trace_json = [](const std::vector<TraceSizeRow>& rows) -> Ordered {
        Ordered arr = Ordered::array();
        for (const auto& r : rows)
            arr.push_back({
                {"frames", r.frames},
                {"fps", round1(r.fps)},
                {"relative", round3(r.relative)},
            });
        return arr;
    };

    Ordered prop_count_json = Ordered::array();
    for (const auto& r : prop_count)
        prop_count_json.push_back({
            {"properties", r.properties},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    Ordered complexity_json = Ordered::array();
    for (const auto& r : complexity)
        complexity_json.push_back({
            {"complexity", r.complexity},
            {"fps", round1(r.fps)},
            {"us_per_frame", round1(r.us_per_frame)},
            {"relative", round3(r.relative)},
        });

    Ordered results;
    results["trace_size_can20"] = trace_json(trace_can20);
    results["trace_size_canfd"] = trace_json(trace_canfd);
    results["property_count"] = prop_count_json;
    results["property_complexity"] = complexity_json;

    Ordered output;
    output["benchmark"] = "scaling";
    output["language"] = "cpp";
    output["timestamp"] = iso_timestamp();
    output["system"] = get_system_info();
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
        for (int count : counts) {
            std::vector<LtlFormula> props;
            props.reserve(count);
            for (int i = 0; i < count; ++i)
                props.push_back(make_scaling_property(i));
            double fps =
                mean_fps(lib, dbc, can20_id, can20_dlc, can20_frame(), props, num_frames, num_runs);
            if (baseline == 0)
                baseline = fps;
            double relative = relative_of(fps, baseline);
            double us = us_per_frame_of(fps);
            std::println(out_file(), "{:10} {:12.0f} {:10.1f} {:10.2f}x", count, fps, us, relative);
            prop_count.push_back(
                {.properties = count, .fps = fps, .us_per_frame = us, .relative = relative});
        }
    }
    return prop_count;
}

static void run_scaling(const fs::path& lib, int num_runs, bool quick, bool emit_json) {
    print_header("Aletheia Scaling Benchmark (C++)");
    std::println(out_file(), "Runs: {}", num_runs);
    std::println(out_file(), "Quick: {}", quick ? "true" : "false");

    auto dbc_20 = make_can20_dbc();
    auto dbc_fd = make_canfd_dbc();
    const int num_frames = quick ? 5000 : 10000;

    // Warmup
    std::println(out_file(), "\nWarming up...");
    {
        std::vector<LtlFormula> warm;
        warm.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
        [[maybe_unused]] const auto warmed =
            mean_fps(lib, dbc_20, can20_id, can20_dlc, can20_frame(), warm, 1000, 1);
    }
    std::println(out_file(), "Done.");

    // 1./2. Trace-size sweeps (CAN 2.0B, then CAN-FD).
    auto scan_trace = [&](const char* title, const DbcDefinition& dbc, CanId id, Dlc dlc,
                          const FramePayload& frame,
                          const std::vector<LtlFormula>& props) -> std::vector<TraceSizeRow> {
        std::println(out_file(), "");
        print_header(title);
        std::println(out_file(), "{:>10} {:>12} {:>10}", "Frames", "Frames/sec", "Relative");
        print_separator();
        std::vector<TraceSizeRow> rows;
        double baseline = 0;
        for (int size : trace_sizes(quick)) {
            double fps = mean_fps(lib, dbc, id, dlc, frame, props, size, num_runs);
            if (baseline == 0)
                baseline = fps;
            double relative = relative_of(fps, baseline);
            std::println(out_file(), "{:10} {:12.0f} {:10.2f}x", size, fps, relative);
            rows.push_back({.frames = size, .fps = fps, .relative = relative});
        }
        return rows;
    };

    std::vector<LtlFormula> trace_props_can20;
    trace_props_can20.push_back(always_between("EngineSpeed", Rational{0, 1}, Rational{8000, 1}));
    auto trace_can20 = scan_trace("Trace Size Scaling (CAN 2.0B)", dbc_20, can20_id, can20_dlc,
                                  can20_frame(), trace_props_can20);

    std::vector<LtlFormula> trace_props_canfd;
    trace_props_canfd.push_back(always_between("GPSSpeed", Rational{0, 1}, Rational{655, 1}));
    auto trace_canfd = scan_trace("Trace Size Scaling (CAN-FD)", dbc_fd, canfd_id, canfd_dlc,
                                  canfd_frame(), trace_props_canfd);

    const auto prop_count = scan_property_count(lib, dbc_20, num_frames, num_runs);

    // 4. Property-complexity sweep (CAN 2.0B), five labelled bundles.
    std::println(out_file(), "");
    print_header("Property Complexity Scaling");
    std::println(out_file(), "{:<25} {:>12} {:>10} {:>10}", "Complexity", "Frames/sec", "us/frame",
                 "Relative");
    print_separator();
    std::vector<ComplexityRow> complexity;
    {
        double baseline = 0;
        for (const auto& [label, props] : complexity_levels()) {
            double fps = mean_fps(lib, dbc_20, can20_id, can20_dlc, can20_frame(), props,
                                  num_frames, num_runs);
            if (baseline == 0)
                baseline = fps;
            double relative = relative_of(fps, baseline);
            double us = us_per_frame_of(fps);
            std::println(out_file(), "{:<25} {:12.0f} {:10.1f} {:10.2f}x", label, fps, us,
                         relative);
            complexity.push_back(
                {.complexity = label, .fps = fps, .us_per_frame = us, .relative = relative});
        }
    }

    std::println(out_file(), "{}", k_rule_heavy);

    if (emit_json)
        emit_scaling_json(trace_can20, trace_canfd, prop_count, complexity);
}

// ---------------------------------------------------------------------------
// CLI argument parsing
// ---------------------------------------------------------------------------

namespace {
struct Args {
    std::string mode; // "throughput", "latency", "scaling"
    int frames = 10000;
    int runs = 5;
    int warmup = 2;
    int ops = 5000;       // latency mode: number of operations
    int warmup_ops = 500; // latency mode: warmup operations
    bool quick = false;   // scaling mode: fewer iterations
    bool json_output = false;
};
} // namespace

static void print_usage(std::string_view argv0) {
    std::print(
        stderr,
        "Usage: {} [throughput|latency|scaling] [OPTIONS]\n\n"
        "Options:\n"
        "  --frames N   Frames per run (default: 10000, throughput/scaling)\n"
        "  --runs N     Number of runs (default: 5, throughput/scaling)\n"
        "  --warmup N   Warmup runs (default: 2, throughput) or ops (default: 500, latency)\n"
        "  --ops N      Operations to measure (default: 5000, latency)\n"
        "  --quick      Fewer iterations (scaling)\n"
        "  --json       Emit JSON to stdout\n",
        argv0);
}

// A count option must be a whole decimal number of zero or more; anything else
// (a word, a sign, trailing characters) is refused rather than read as zero and
// silently benchmarked.
static auto parse_count(std::string_view option, std::string_view text) -> int {
    int value = 0;
    const auto* const last = std::to_address(text.end());
    auto [end, ec] = std::from_chars(std::to_address(text.begin()), last, value);
    if (ec != std::errc{} || end != last || value < 0) {
        std::println(stderr, "{} expects a non-negative whole number, got '{}'", option, text);
        std::exit(1);
    }
    return value;
}

static auto parse_args(std::span<char* const> argv) -> Args {
    Args args;

    if (argv.size() < 2) {
        print_usage(argv[0]);
        std::exit(1);
    }

    args.mode = argv[1];
    if (args.mode != "throughput" && args.mode != "latency" && args.mode != "scaling") {
        std::println(stderr, "Unknown mode: {}", argv[1]);
        print_usage(argv[0]);
        std::exit(1);
    }

    for (std::size_t i = 2; i < argv.size(); ++i) {
        auto arg = std::string_view{argv[i]};
        if (arg == "--json") {
            args.json_output = true;
        } else if (arg == "--quick") {
            args.quick = true;
        } else if (arg == "--frames" && i + 1 < argv.size()) {
            args.frames = parse_count(arg, argv[++i]);
        } else if (arg == "--runs" && i + 1 < argv.size()) {
            args.runs = parse_count(arg, argv[++i]);
        } else if (arg == "--warmup" && i + 1 < argv.size()) {
            const int val = parse_count(arg, argv[++i]);
            args.warmup = val;
            args.warmup_ops = val;
        } else if (arg == "--ops" && i + 1 < argv.size()) {
            args.ops = parse_count(arg, argv[++i]);
        } else {
            std::println(stderr, "Unknown option: {}", arg);
            print_usage(argv[0]);
            std::exit(1);
        }
    }

    return args;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

static auto run(std::span<char* const> argv) -> int try {
    check_release_build();
    const auto args = parse_args(argv);

    // When --json is set, human-readable output goes to stderr.
    if (args.json_output)
        out_file() = stderr;

    auto lib = find_lib();

    if (args.mode == "throughput")
        run_throughput(lib, args.frames, args.runs, args.warmup, args.json_output);
    else if (args.mode == "latency")
        run_latency(lib, args.ops, args.warmup_ops, args.json_output);
    else if (args.mode == "scaling")
        run_scaling(lib, args.runs, args.quick, args.json_output);

    return 0;
} catch (const std::exception& e) {
    std::println(stderr, "benchmark: {}", e.what());
    return 1;
} catch (...) {
    return 1;
}

// Nothing leaves main: the harness that drives this binary reads its exit
// code, and an escaping exception would arrive as a signal instead, which the
// harness reads as a crash rather than as the refusal it is.
auto main(int argc, char* argv[]) -> int {
    try {
        return run(std::span{argv, static_cast<std::size_t>(argc)});
    } catch (...) {
        return 1;
    }
}

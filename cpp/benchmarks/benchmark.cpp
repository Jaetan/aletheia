// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++ Benchmark
//
// Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
// through the Aletheia FFI backend.
//
// Usage: ./benchmark [throughput|latency|scaling] [--frames N] [--runs N] [--json]

#include <aletheia/aletheia.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <filesystem>
#include <numeric>
#include <string>
#include <string_view>
#include <thread>
#include <vector>

using namespace aletheia;
using json = nlohmann::json;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Library discovery
// ---------------------------------------------------------------------------

static auto find_lib() -> fs::path {
    // 1. Environment variable
    if (auto* env = std::getenv("ALETHEIA_LIB"))
        return env;

    // 2. Relative to executable: ../build/libaletheia-ffi.so
    auto exe = fs::read_symlink("/proc/self/exe");
    auto dir = exe.parent_path();

    auto path1 = dir / ".." / "build" / "libaletheia-ffi.so";
    if (fs::exists(path1))
        return fs::canonical(path1);

    // 3. Relative to executable: ../../build/libaletheia-ffi.so
    auto path2 = dir / ".." / ".." / "build" / "libaletheia-ffi.so";
    if (fs::exists(path2))
        return fs::canonical(path2);

    std::fprintf(stderr, "ERROR: libaletheia-ffi.so not found.\n"
                         "Set ALETHEIA_LIB or run 'cabal run shake -- build'.\n");
    std::exit(1);
}

// ---------------------------------------------------------------------------
// System info
// ---------------------------------------------------------------------------

static auto get_cpu_model() -> std::string {
    std::FILE* f = std::fopen("/proc/cpuinfo", "r");
    if (f == nullptr)
        return "unknown";
    char line[256];
    while (std::fgets(line, sizeof(line), f) != nullptr) {
        if (std::strncmp(line, "model name", 10) == 0) {
            auto* colon = std::strchr(line, ':');
            if (colon != nullptr) {
                // Skip ": " prefix and strip trailing newline
                auto* start = colon + 2;
                auto len = std::strlen(start);
                if (len > 0 && start[len - 1] == '\n')
                    start[len - 1] = '\0';
                std::fclose(f);
                return start;
            }
        }
    }
    std::fclose(f);
    return "unknown";
}

static auto get_system_info() -> json {
    return {
        {"cpu", get_cpu_model()},
        {"cores", static_cast<int>(std::thread::hardware_concurrency())},
        {"platform", "Linux"},
    };
}

static auto iso_timestamp() -> std::string {
    auto now = std::chrono::system_clock::now();
    auto tt = std::chrono::system_clock::to_time_t(now);
    std::tm utc{};
    gmtime_r(&tt, &utc);
    char buf[32];
    std::strftime(buf, sizeof(buf), "%Y-%m-%dT%H:%M:%SZ", &utc);
    return buf;
}

// ---------------------------------------------------------------------------
// DBC definitions (programmatic, matching example.dbc / example_canfd.dbc)
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

static const FramePayload can20_frame = {
    std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
    std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00},
};
static const auto can20_id = CanId{StandardId::create(0x100).value()};
static const auto can20_dlc = Dlc::create(8).value();

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

static const FramePayload canfd_frame = make_canfd_frame();
static const auto canfd_id = CanId{StandardId::create(0x200).value()};
static const auto canfd_dlc = Dlc::create(15).value();

// CAN 2.0B signal values for frame building
static const std::vector<SignalValue> can20_signals = {
    {SignalName{"EngineSpeed"}, PhysicalValue{Rational{2000, 1}}},
    {SignalName{"EngineTemp"}, PhysicalValue{Rational{90, 1}}},
};

// CAN-FD signal values for frame building
static const std::vector<SignalValue> canfd_signals = {
    {SignalName{"GPSSpeed"}, PhysicalValue{Rational{20, 1}}},
    {SignalName{"YawRate"}, PhysicalValue{Rational{}}},
    {SignalName{"WheelSpeedFL"}, PhysicalValue{Rational{10, 1}}},
    {SignalName{"WheelSpeedFR"}, PhysicalValue{Rational{10, 1}}},
};

// ---------------------------------------------------------------------------
// LTL properties
// ---------------------------------------------------------------------------

static auto make_can20_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(
        ltl::between(SignalName{"EngineSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{8000, 1}}))));
    props.push_back(ltl::always(ltl::atomic(
        ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-40, 1}}, PhysicalValue{Rational{215, 1}}))));
    return props;
}

static auto make_canfd_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(
        ltl::between(SignalName{"GPSSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    props.push_back(ltl::always(ltl::atomic(
        ltl::between(SignalName{"YawRate"}, PhysicalValue{Rational{-327, 1}}, PhysicalValue{Rational{327, 1}}))));
    props.push_back(ltl::always(ltl::atomic(
        ltl::between(SignalName{"WheelSpeedFL"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    return props;
}

// Scaling property templates (CAN 2.0B)
static auto make_scaling_property(int index) -> LtlFormula {
    // Rotate through different property definitions
    switch (index % 10) {
    case 0:
        return ltl::always(ltl::atomic(
            ltl::between(SignalName{"EngineSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{8000, 1}})));
    case 1:
        return ltl::always(ltl::atomic(
            ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-40, 1}}, PhysicalValue{Rational{215, 1}})));
    case 2:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"BrakePressure"}, PhysicalValue{Rational{13107, 2}})));
    case 3:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"EngineSpeed"}, PhysicalValue{Rational{7000, 1}})));
    case 4:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"EngineTemp"}, PhysicalValue{Rational{200, 1}})));
    case 5:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"BrakePressure"}, PhysicalValue{Rational{5000, 1}})));
    case 6:
        return ltl::always(ltl::atomic(
            ltl::between(SignalName{"EngineSpeed"}, PhysicalValue{Rational{500, 1}}, PhysicalValue{Rational{7500, 1}})));
    case 7:
        return ltl::always(ltl::atomic(
            ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-20, 1}}, PhysicalValue{Rational{180, 1}})));
    case 8:
        return ltl::always(ltl::atomic(
            ltl::between(SignalName{"BrakePressure"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{4000, 1}})));
    default:
        return ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"EngineSpeed"}, PhysicalValue{Rational{6000, 1}})));
    }
}

// ---------------------------------------------------------------------------
// Statistics helpers
// ---------------------------------------------------------------------------

struct Stats {
    double mean = 0;
    double stdev = 0;
    double min_val = 0;
    double max_val = 0;
};

static auto compute_stats(const std::vector<double>& data) -> Stats {
    if (data.empty())
        return {};
    auto n = static_cast<double>(data.size());
    double sum = std::accumulate(data.begin(), data.end(), 0.0);
    double mean = sum / n;
    double sq_sum = 0;
    for (auto v : data)
        sq_sum += (v - mean) * (v - mean);
    double stdev = (data.size() > 1) ? std::sqrt(sq_sum / (n - 1.0)) : 0.0;
    return {
        .mean = mean,
        .stdev = stdev,
        .min_val = *std::min_element(data.begin(), data.end()),
        .max_val = *std::max_element(data.begin(), data.end()),
    };
}

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

static auto percentile(const std::vector<double>& sorted, double p) -> double {
    if (sorted.empty())
        return 0.0;
    double k = static_cast<double>(sorted.size() - 1) * p / 100.0;
    auto f = static_cast<std::size_t>(k);
    auto c = (f + 1 < sorted.size()) ? f + 1 : f;
    return sorted[f] + (k - static_cast<double>(f)) * (sorted[c] - sorted[f]);
}

static auto compute_latency_stats(std::vector<double>& latencies_us) -> LatencyStats {
    if (latencies_us.empty())
        return {};
    std::sort(latencies_us.begin(), latencies_us.end());
    double sum = std::accumulate(latencies_us.begin(), latencies_us.end(), 0.0);
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

// Output destination: stderr when --json is set, stdout otherwise.
static std::FILE* out_file = stdout;

static void print_header(const char* title) {
    std::fprintf(out_file,
                 "======================================================================\n");
    std::fprintf(out_file, "%s\n", title);
    std::fprintf(out_file,
                 "======================================================================\n");
}

static void print_separator() {
    std::fprintf(out_file,
                 "----------------------------------------------------------------------\n");
}

// ---------------------------------------------------------------------------
// Benchmark: throughput
// ---------------------------------------------------------------------------

struct ThroughputResult {
    std::string name;
    int num_frames;
    int num_runs;
    Stats fps;
    std::vector<double> all_fps;
};

static auto bench_streaming(const fs::path& lib, const DbcDefinition& dbc,
                            std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                            const FramePayload& frame, int num_frames) -> double {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));
    (void)client.set_properties(properties);
    (void)client.start_stream();

    auto start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < num_frames; ++i)
        (void)client.send_frame(Timestamp{i}, id, dlc, frame);
    auto end = std::chrono::high_resolution_clock::now();

    (void)client.end_stream();

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto bench_extraction(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                             const FramePayload& frame, int num_frames) -> double {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));

    auto start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < num_frames; ++i)
        (void)client.extract_signals(id, dlc, frame);
    auto end = std::chrono::high_resolution_clock::now();

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto bench_building(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                           const std::vector<SignalValue>& signals, int num_frames) -> double {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));

    auto start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < num_frames; ++i)
        (void)client.build_frame(id, dlc, signals);
    auto end = std::chrono::high_resolution_clock::now();

    auto elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(num_frames) / elapsed;
}

static auto run_throughput_bench(const char* name, auto bench_fn, int num_frames, int num_runs,
                                 int warmup_runs) -> ThroughputResult {
    // Warmup
    for (int w = 0; w < warmup_runs; ++w)
        bench_fn(num_frames / 10);

    // Actual runs
    std::vector<double> results;
    results.reserve(num_runs);
    for (int r = 0; r < num_runs; ++r) {
        double fps = bench_fn(num_frames);
        results.push_back(fps);
    }

    auto stats = compute_stats(results);

    std::fprintf(out_file, "\n%s:\n", name);
    std::fprintf(out_file, "----------------------------------------\n");
    for (int r = 0; r < num_runs; ++r)
        std::fprintf(out_file, "  Run %d/%d: %.0f ops/sec\n", r + 1, num_runs, results[r]);

    return ThroughputResult{
        .name = name,
        .num_frames = num_frames,
        .num_runs = num_runs,
        .fps = stats,
        .all_fps = std::move(results),
    };
}

static void run_throughput(const fs::path& lib, int num_frames, int num_runs, int warmup,
                           bool emit_json) {
    print_header("Aletheia Throughput Benchmark (C++)");
    std::fprintf(out_file, "Frames per run: %d\n", num_frames);
    std::fprintf(out_file, "Runs: %d\n", num_runs);
    std::fprintf(out_file, "Warmup runs: %d\n", warmup);

    auto dbc_20 = make_can20_dbc();
    auto dbc_fd = make_canfd_dbc();

    std::vector<ThroughputResult> results;

    // CAN 2.0B benchmarks
    results.push_back(run_throughput_bench(
        "CAN 2.0B: Stream LTL (2 props)",
        [&](int n) {
            return bench_streaming(lib, dbc_20, make_can20_properties(), can20_id, can20_dlc,
                                   can20_frame, n);
        },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN 2.0B: Signal Extraction",
        [&](int n) { return bench_extraction(lib, dbc_20, can20_id, can20_dlc, can20_frame, n); },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN 2.0B: Frame Building",
        [&](int n) { return bench_building(lib, dbc_20, can20_id, can20_dlc, can20_signals, n); },
        num_frames, num_runs, warmup));

    // CAN-FD benchmarks
    results.push_back(run_throughput_bench(
        "CAN-FD:   Stream LTL (3 props)",
        [&](int n) {
            return bench_streaming(lib, dbc_fd, make_canfd_properties(), canfd_id, canfd_dlc,
                                   canfd_frame, n);
        },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN-FD:   Signal Extraction",
        [&](int n) { return bench_extraction(lib, dbc_fd, canfd_id, canfd_dlc, canfd_frame, n); },
        num_frames, num_runs, warmup));

    results.push_back(run_throughput_bench(
        "CAN-FD:   Frame Building",
        [&](int n) { return bench_building(lib, dbc_fd, canfd_id, canfd_dlc, canfd_signals, n); },
        num_frames, num_runs, warmup));

    // Summary table
    std::fprintf(out_file, "\n");
    print_header("Summary");
    std::fprintf(out_file, "%-35s %12s %10s %10s %10s\n", "Benchmark", "Mean", "Stdev", "Min",
                 "Max");
    print_separator();
    for (const auto& r : results) {
        std::fprintf(out_file, "%-35s %10.0f/s %9.0f %9.0f %9.0f\n", r.name.c_str(), r.fps.mean,
                     r.fps.stdev, r.fps.min_val, r.fps.max_val);
    }
    std::fprintf(out_file,
                 "======================================================================\n");

    if (emit_json) {
        json json_results = json::array();
        for (const auto& r : results) {
            double us = (r.fps.mean > 0) ? 1'000'000.0 / r.fps.mean : 0;
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
        json output = {
            {"benchmark", "throughput"},    {"language", "cpp"},
            {"timestamp", iso_timestamp()}, {"system", get_system_info()},
            {"results", json_results},
        };
        std::printf("%s\n", output.dump(2).c_str());
    }
}

// ---------------------------------------------------------------------------
// Benchmark: latency
// ---------------------------------------------------------------------------

struct LatencyResult {
    std::string name;
    LatencyStats stats;
};

static void print_latency(const char* name, const LatencyStats& s) {
    std::fprintf(out_file, "\n%s:\n", name);
    std::fprintf(out_file, "--------------------------------------------------\n");
    std::fprintf(out_file, "  Count:    %zu operations\n", s.count);
    std::fprintf(out_file, "  Mean:     %.1f us\n", s.mean_us);
    std::fprintf(out_file, "  Min:      %.1f us\n", s.min_us);
    std::fprintf(out_file, "  Max:      %.1f us\n", s.max_us);
    std::fprintf(out_file, "  p50:      %.1f us\n", s.p50_us);
    std::fprintf(out_file, "  p90:      %.1f us\n", s.p90_us);
    std::fprintf(out_file, "  p99:      %.1f us\n", s.p99_us);
    std::fprintf(out_file, "  p99.9:    %.1f us\n", s.p999_us);
    if (s.mean_us > 0)
        std::fprintf(out_file, "  Implied:  %.0f ops/sec (from mean)\n", 1'000'000.0 / s.mean_us);
}

static auto bench_latency_streaming(const fs::path& lib, const DbcDefinition& dbc,
                                    std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                                    const FramePayload& frame, int warmup, int ops)
    -> LatencyStats {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));
    (void)client.set_properties(properties);
    (void)client.start_stream();

    // Warmup
    for (int i = 0; i < warmup; ++i)
        (void)client.send_frame(Timestamp{i}, id, dlc, frame);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::high_resolution_clock::now();
        (void)client.send_frame(Timestamp{warmup + i}, id, dlc, frame);
        auto end = std::chrono::high_resolution_clock::now();
        auto us = std::chrono::duration<double, std::micro>(end - start).count();
        latencies.push_back(us);
    }

    (void)client.end_stream();
    return compute_latency_stats(latencies);
}

static auto bench_latency_extraction(const fs::path& lib, const DbcDefinition& dbc, CanId id,
                                     Dlc dlc, const FramePayload& frame, int warmup, int ops)
    -> LatencyStats {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));

    // Warmup
    for (int i = 0; i < warmup; ++i)
        (void)client.extract_signals(id, dlc, frame);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::high_resolution_clock::now();
        (void)client.extract_signals(id, dlc, frame);
        auto end = std::chrono::high_resolution_clock::now();
        latencies.push_back(std::chrono::duration<double, std::micro>(end - start).count());
    }

    return compute_latency_stats(latencies);
}

static auto bench_latency_building(const fs::path& lib, const DbcDefinition& dbc, CanId id, Dlc dlc,
                                   const std::vector<SignalValue>& signals, int warmup, int ops)
    -> LatencyStats {
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse_result = client.parse_dbc(dbc);
    if (!parse_result)
        throw std::runtime_error("parse_dbc failed: " +
                                 std::string(parse_result.error().message()));

    // Warmup
    for (int i = 0; i < warmup; ++i)
        (void)client.build_frame(id, dlc, signals);

    // Measure
    std::vector<double> latencies;
    latencies.reserve(ops);
    for (int i = 0; i < ops; ++i) {
        auto start = std::chrono::high_resolution_clock::now();
        (void)client.build_frame(id, dlc, signals);
        auto end = std::chrono::high_resolution_clock::now();
        latencies.push_back(std::chrono::duration<double, std::micro>(end - start).count());
    }

    return compute_latency_stats(latencies);
}

static void run_latency(const fs::path& lib, int ops, int warmup, bool emit_json) {
    print_header("Aletheia Latency Benchmark (C++)");
    std::fprintf(out_file, "Operations: %d\n", ops);
    std::fprintf(out_file, "Warmup: %d\n", warmup);

    auto dbc_20 = make_can20_dbc();
    auto dbc_fd = make_canfd_dbc();

    std::vector<LatencyResult> results;

    auto run_suite = [&](const char* label, const DbcDefinition& dbc,
                         std::vector<LtlFormula> properties, CanId id, Dlc dlc,
                         const FramePayload& frame, const std::vector<SignalValue>& signals) {
        char name[128];

        std::fprintf(out_file, "\nBenchmarking %s streaming...\n", label);
        auto s1 =
            bench_latency_streaming(lib, dbc, std::move(properties), id, dlc, frame, warmup, ops);
        std::snprintf(name, sizeof(name), "%s Streaming LTL", label);
        print_latency(name, s1);
        results.push_back({name, s1});

        std::fprintf(out_file, "\nBenchmarking %s signal extraction...\n", label);
        auto s2 = bench_latency_extraction(lib, dbc, id, dlc, frame, warmup, ops);
        std::snprintf(name, sizeof(name), "%s Signal Extraction", label);
        print_latency(name, s2);
        results.push_back({name, s2});

        std::fprintf(out_file, "\nBenchmarking %s frame building...\n", label);
        auto s3 = bench_latency_building(lib, dbc, id, dlc, signals, warmup, ops);
        std::snprintf(name, sizeof(name), "%s Frame Building", label);
        print_latency(name, s3);
        results.push_back({name, s3});
    };

    run_suite("CAN 2.0B", dbc_20, make_can20_properties(), can20_id, can20_dlc, can20_frame,
              can20_signals);
    run_suite("CAN-FD", dbc_fd, make_canfd_properties(), canfd_id, canfd_dlc, canfd_frame,
              canfd_signals);

    // Summary table
    std::fprintf(out_file, "\n");
    print_header("Summary (all times in microseconds)");
    std::fprintf(out_file, "%-30s %10s %10s %10s %10s\n", "Operation", "Mean", "p50", "p99",
                 "p99.9");
    print_separator();
    for (const auto& r : results) {
        std::fprintf(out_file, "%-30s %10.1f %10.1f %10.1f %10.1f\n", r.name.c_str(),
                     r.stats.mean_us, r.stats.p50_us, r.stats.p99_us, r.stats.p999_us);
    }
    std::fprintf(out_file,
                 "======================================================================\n");

    if (emit_json) {
        json json_results = json::array();
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
        json output = {
            {"benchmark", "latency"},       {"language", "cpp"},
            {"timestamp", iso_timestamp()}, {"system", get_system_info()},
            {"results", json_results},
        };
        std::printf("%s\n", output.dump(2).c_str());
    }
}

// ---------------------------------------------------------------------------
// Benchmark: scaling (property count, CAN 2.0B only)
// ---------------------------------------------------------------------------

struct ScalingResult {
    int property_count;
    double fps;
    double us_per_frame;
    double relative;
};

static void run_scaling(const fs::path& lib, int num_frames, int num_runs, bool emit_json) {
    print_header("Aletheia Scaling Benchmark (C++)");
    std::fprintf(out_file, "Frames per run: %d\n", num_frames);

    auto dbc = make_can20_dbc();

    // Warmup
    std::fprintf(out_file, "\nWarming up...\n");
    {
        auto props = make_can20_properties();
        bench_streaming(lib, dbc, std::move(props), can20_id, can20_dlc, can20_frame, 1000);
    }
    std::fprintf(out_file, "Done.\n");

    // Property count scaling
    std::fprintf(out_file, "\n");
    print_header("Property Count Scaling");
    std::fprintf(out_file, "Testing throughput as property count increases...\n\n");
    std::fprintf(out_file, "%10s %12s %10s %10s\n", "Properties", "Frames/sec", "us/frame",
                 "Relative");
    print_separator();

    constexpr int counts[] = {1, 2, 3, 5, 7, 10};
    double baseline_fps = 0;
    std::vector<ScalingResult> results;

    for (int count : counts) {
        // Build properties for this count
        std::vector<LtlFormula> props;
        for (int i = 0; i < count; ++i)
            props.push_back(make_scaling_property(i));

        // Average over runs
        std::vector<double> fps_runs;
        for (int r = 0; r < num_runs; ++r) {
            // Need to copy properties for each run
            std::vector<LtlFormula> props_copy;
            for (int i = 0; i < count; ++i)
                props_copy.push_back(make_scaling_property(i));
            fps_runs.push_back(bench_streaming(lib, dbc, std::move(props_copy), can20_id, can20_dlc,
                                               can20_frame, num_frames));
        }
        auto stats = compute_stats(fps_runs);
        double fps = stats.mean;

        if (baseline_fps == 0)
            baseline_fps = fps;
        double relative = fps / baseline_fps;
        double us = 1'000'000.0 / fps;

        std::fprintf(out_file, "%10d %12.0f %10.1f %10.2fx\n", count, fps, us, relative);
        results.push_back({count, fps, us, relative});
    }

    std::fprintf(out_file, "\nExpected: Some degradation, but should be sub-linear\n");
    std::fprintf(out_file,
                 "======================================================================\n");

    if (emit_json) {
        json json_results = json::array();
        for (const auto& r : results) {
            json_results.push_back({
                {"properties", r.property_count},
                {"fps", std::round(r.fps * 10) / 10},
                {"us_per_frame", std::round(r.us_per_frame * 10) / 10},
                {"relative", std::round(r.relative * 1000) / 1000},
            });
        }
        json output = {
            {"benchmark", "scaling"},
            {"language", "cpp"},
            {"timestamp", iso_timestamp()},
            {"system", get_system_info()},
            {"results", {{"property_count", json_results}}},
        };
        std::printf("%s\n", output.dump(2).c_str());
    }
}

// ---------------------------------------------------------------------------
// CLI argument parsing
// ---------------------------------------------------------------------------

struct Args {
    std::string mode; // "throughput", "latency", "scaling"
    int frames = 10000;
    int runs = 5;
    int warmup = 2;
    int ops = 5000;       // latency mode: number of operations
    int warmup_ops = 500; // latency mode: warmup operations
    bool json_output = false;
};

static void print_usage(const char* argv0) {
    std::fprintf(stderr, "Usage: %s [throughput|latency|scaling] [OPTIONS]\n\n", argv0);
    std::fprintf(stderr, "Options:\n");
    std::fprintf(stderr, "  --frames N   Frames per run (default: 10000, throughput/scaling)\n");
    std::fprintf(stderr, "  --runs N     Number of runs (default: 5, throughput/scaling)\n");
    std::fprintf(
        stderr,
        "  --warmup N   Warmup runs (default: 2, throughput) or ops (default: 500, latency)\n");
    std::fprintf(stderr, "  --ops N      Operations to measure (default: 5000, latency)\n");
    std::fprintf(stderr, "  --json       Emit JSON to stdout\n");
}

static auto parse_args(int argc, char* argv[]) -> Args {
    Args args;

    if (argc < 2) {
        print_usage(argv[0]);
        std::exit(1);
    }

    args.mode = argv[1];
    if (args.mode != "throughput" && args.mode != "latency" && args.mode != "scaling") {
        std::fprintf(stderr, "Unknown mode: %s\n", argv[1]);
        print_usage(argv[0]);
        std::exit(1);
    }

    for (int i = 2; i < argc; ++i) {
        auto arg = std::string_view{argv[i]};
        if (arg == "--json") {
            args.json_output = true;
        } else if (arg == "--frames" && i + 1 < argc) {
            args.frames = std::atoi(argv[++i]);
        } else if (arg == "--runs" && i + 1 < argc) {
            args.runs = std::atoi(argv[++i]);
        } else if (arg == "--warmup" && i + 1 < argc) {
            int val = std::atoi(argv[++i]);
            args.warmup = val;
            args.warmup_ops = val;
        } else if (arg == "--ops" && i + 1 < argc) {
            args.ops = std::atoi(argv[++i]);
        } else {
            std::fprintf(stderr, "Unknown option: %s\n", argv[i]);
            print_usage(argv[0]);
            std::exit(1);
        }
    }

    return args;
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

int main(int argc, char* argv[]) {
    auto args = parse_args(argc, argv);

    // When --json is set, human-readable output goes to stderr.
    if (args.json_output)
        out_file = stderr;

    auto lib = find_lib();

    if (args.mode == "throughput")
        run_throughput(lib, args.frames, args.runs, args.warmup, args.json_output);
    else if (args.mode == "latency")
        run_latency(lib, args.ops, args.warmup_ops, args.json_output);
    else if (args.mode == "scaling")
        run_scaling(lib, args.frames, args.runs, args.json_output);

    return 0;
}

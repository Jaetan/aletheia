// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Aletheia C++ Benchmark
//
// Measures throughput, latency, and scaling for CAN 2.0B and CAN-FD frames
// through the Aletheia FFI backend.
//
// Usage: ./benchmark [throughput|latency|scaling] [--frames N] [--runs N] [--quick] [--json]

#include "benchmark_latency.hpp"
#include "benchmark_output.hpp"
#include "benchmark_scaling.hpp"
#include "benchmark_system.hpp"
#include "benchmark_throughput.hpp"

#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <nlohmann/json.hpp>

#include <array>
#include <charconv>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <format>
#include <fstream>
#include <memory>
#include <print>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <utility>
#include <vector>

// The names this harness uses, declared rather than pulled in wholesale, so a
// reader sees which part of the API a benchmark touches.
using aletheia::bench::out_file, aletheia::bench::run_latency, aletheia::bench::run_scaling,
    aletheia::bench::run_throughput, aletheia::bench::write_mode_report;
using aletheia::CanId, aletheia::FramePayload;
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
            if (auto const colon = line.find(':'); colon != std::string::npos)
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

// The compiler that built this binary, as it names itself: the toolchain the
// report names, where the other bindings name their runtime's version.
constexpr auto k_compiler = __VERSION__;

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

namespace aletheia::bench {

auto get_system_info() -> Json {
    return {
        {"cpu", get_cpu_model()}, {"cores", static_cast<int>(std::thread::hardware_concurrency())},
        {"platform", "Linux"},    {"build_type", k_build_type},
        {"compiler", k_compiler},
    };
}

auto iso_timestamp() -> std::string {
    auto const now = std::chrono::floor<std::chrono::seconds>(std::chrono::system_clock::now());
    return std::format("{:%FT%TZ}", now);
}

} // namespace aletheia::bench

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
    auto const* const last = std::to_address(text.end());
    auto const [end, ec] = std::from_chars(std::to_address(text.begin()), last, value);
    if (ec != std::errc{} || end != last || value < 0) {
        std::println(stderr, "{} expects a non-negative whole number, got '{}'", option, text);
        std::exit(1);
    }
    return value;
}

static auto parse_args(std::span<char* const> argv) -> Args {
    Args args;

    // The program's name and the mode, read checked.
    std::vector<std::string_view> const words(argv.begin(), argv.end());
    auto const program = words.at(0);
    if (words.size() < 2) {
        print_usage(program);
        std::exit(1);
    }

    args.mode = words.at(1);
    if (args.mode != "throughput" && args.mode != "latency" && args.mode != "scaling") {
        std::println(stderr, "Unknown mode: {}", args.mode);
        print_usage(program);
        std::exit(1);
    }

    // A cursor over what is left after the program name and the mode, because a
    // flag that takes a value consumes the argument after it: the step is one
    // or two, so the remainder carries the position rather than an index.
    auto rest = argv.subspan(2);
    auto const take_value = [&rest] {
        auto const* const value = rest.front();
        rest = rest.subspan(1);
        return value;
    };
    while (!rest.empty()) {
        auto const arg = std::string_view{rest.front()};
        rest = rest.subspan(1);
        auto const has_value = !rest.empty();
        if (arg == "--json") {
            args.json_output = true;
        } else if (arg == "--quick") {
            args.quick = true;
        } else if (arg == "--frames" && has_value) {
            args.frames = parse_count(arg, take_value());
        } else if (arg == "--runs" && has_value) {
            args.runs = parse_count(arg, take_value());
        } else if (arg == "--warmup" && has_value) {
            auto const val = parse_count(arg, take_value());
            args.warmup = val;
            args.warmup_ops = val;
        } else if (arg == "--ops" && has_value) {
            args.ops = parse_count(arg, take_value());
        } else {
            std::println(stderr, "Unknown option: {}", arg);
            print_usage(program);
            std::exit(1);
        }
    }

    // A count of zero measures nothing, and a row computed from nothing reads
    // as a rate of zero rather than as a failure. Each is checked whichever
    // mode runs, so the refusal does not depend on which flag that mode reads;
    // a warmup of zero is a measurement with no warmup and stays legal.
    for (auto const [option, value] :
         std::array{std::pair{"--frames", args.frames}, std::pair{"--runs", args.runs},
                    std::pair{"--ops", args.ops}}) {
        if (value < 1) {
            std::println(stderr, "{} must be at least 1, got {}", option, value);
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
    auto const args = parse_args(argv);

    // When --json is set, human-readable output goes to stderr.
    if (args.json_output)
        out_file() = stderr;

    auto const lib = find_lib();

    // Every mode's report is on stdout: the text tables, or the JSON report
    // under --json.
    write_mode_report(stdout, args.mode, [&] {
        if (args.mode == "throughput")
            run_throughput(lib, args.frames, args.runs, args.warmup, args.json_output);
        else if (args.mode == "latency")
            run_latency(lib, args.ops, args.warmup_ops, args.json_output);
        else if (args.mode == "scaling")
            run_scaling(lib, args.runs, args.quick, args.json_output);
    });

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

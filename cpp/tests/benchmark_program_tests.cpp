// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The benchmark program's exit status, which benchmarks/run_all.sh reads to
// tell a run from a failure, held by running the built program with its stdout
// and stderr on files this test opens: arguments it refuses exit 1 before the
// kernel is searched for, a run that finds no kernel exits 1 saying so, and a
// report its stdout refuses exits 1 naming the mode and the system's reason.
// The launcher these runs and the stability harness's go through runs a
// program in the directory it names, and reads a program a signal ends as no
// exit code, so a run that crashes after writing its report never reads as a
// clean exit.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <filesystem>
#include <string>
#include <utility>
#include <vector>

#include "child_process.hpp"
#include "find_lib.hpp"
#include "temp_path.hpp"
#include "text_file.hpp"

#ifndef ALETHEIA_BENCHMARK_BIN
#error "ALETHEIA_BENCHMARK_BIN must be defined (the benchmark program's path)"
#endif

using aletheia::test::AsDirectory, aletheia::test::TempPath, aletheia::test::scratch_dir;
using Catch::Matchers::ContainsSubstring, Catch::Matchers::StartsWith;

namespace {

// How a run of the program ended: its exit code, or -1 when a signal ended
// it, and what it wrote to stderr.
struct Ended {
    int code;
    std::string errors;
};

// Arguments the program refuses and the line its refusal opens with; the
// refusal of a word it does not take goes on with the usage, the refusal of a
// count is the line alone, and a run naming no mode is the usage alone.
struct Refusal {
    std::vector<std::string> arguments;
    std::string line;
    bool usage;
};

} // namespace

// Runs the program in `where` with `arguments`, its stdout on `report` and
// `library` as the kernel it searches for first, and answers how it ended.
static auto run_benchmark(const std::vector<std::string>& arguments,
                          const std::filesystem::path& report, const std::filesystem::path& library,
                          const std::filesystem::path& where) -> Ended {
    std::vector<std::string> words{ALETHEIA_BENCHMARK_BIN};
    words.insert(words.end(), arguments.begin(), arguments.end());
    const TempPath errors{"benchmark-stderr"};
    auto const code = aletheia::test::run_program(
        std::move(words), aletheia::test::environment_with({"ALETHEIA_LIB=" + library.string()}),
        where, report, errors.path);
    return {.code = code, .errors = aletheia::test::read_text_file(errors.path)};
}

// ALETHEIA_LIB names a file that is not there and the program runs two levels
// under a directory of this test's, so every build tree the search tries from
// there is inside that directory and holds no library: an argument check made
// after the search would fail on the search instead.
TEST_CASE("an argument the program refuses exits 1 naming it before the kernel is searched for",
          "[benchmark][program]") {
    auto const refusal = GENERATE(values<Refusal>({
        {.arguments = {"bogus"}, .line = "Unknown mode: bogus", .usage = true},
        {.arguments = {"--frames", "10", "latency"},
         .line = "Unknown mode: --frames",
         .usage = true},
        {.arguments = {"throughput", "stray"}, .line = "Unknown option: stray", .usage = true},
        {.arguments = {"throughput", "--bogus"}, .line = "Unknown option: --bogus", .usage = true},
        {.arguments = {}, .line = "", .usage = true},
        {.arguments = {"throughput", "--frames"},
         .line = "Unknown option: --frames",
         .usage = true},
        {.arguments = {"throughput", "--runs"}, .line = "Unknown option: --runs", .usage = true},
        {.arguments = {"throughput", "--warmup"},
         .line = "Unknown option: --warmup",
         .usage = true},
        {.arguments = {"latency", "--ops"}, .line = "Unknown option: --ops", .usage = true},
        {.arguments = {"throughput", "--frames", "0"},
         .line = "--frames must be at least 1, got 0",
         .usage = false},
        {.arguments = {"latency", "--runs", "0"},
         .line = "--runs must be at least 1, got 0",
         .usage = false},
        {.arguments = {"throughput", "--ops", "0"},
         .line = "--ops must be at least 1, got 0",
         .usage = false},
        {.arguments = {"throughput", "--frames", "x"},
         .line = "--frames expects a non-negative whole number, got 'x'",
         .usage = false},
        {.arguments = {"throughput", "--frames", "-5"},
         .line = "--frames expects a non-negative whole number, got '-5'",
         .usage = false},
    }));
    CAPTURE(refusal.arguments);
    const TempPath searched{scratch_dir() / "benchmark-searched", AsDirectory{}};
    const TempPath where{searched.path / "one" / "two", AsDirectory{}};
    const TempPath report{"benchmark-report"};
    auto const [code, errors] =
        run_benchmark(refusal.arguments, report.path, searched.path / "absent.so", where.path);
    CHECK(code == 1);
    if (refusal.usage)
        CHECK_THAT(errors,
                   StartsWith(refusal.line.empty() ? "Usage: " : refusal.line + "\nUsage: "));
    else
        CHECK(errors == refusal.line + "\n");
    CHECK(aletheia::test::read_text_file(report.path).empty());
}

// Arguments the program takes, with ALETHEIA_LIB naming no file, or empty with
// no kernel anywhere the search tries from the directory the program runs in:
// each is the search's refusal, printed after the program's prefix.
TEST_CASE("a run that finds no kernel exits 1 saying so", "[benchmark][program]") {
    const TempPath searched{scratch_dir() / "benchmark-searched", AsDirectory{}};
    const TempPath where{searched.path / "one" / "two", AsDirectory{}};
    const TempPath report{"benchmark-report"};
    std::vector<std::string> const arguments{"throughput", "--frames", "1", "--runs",
                                             "1",          "--warmup", "0"};
    SECTION("ALETHEIA_LIB naming no file") {
        auto const absent = searched.path / "absent.so";
        auto const [code, errors] = run_benchmark(arguments, report.path, absent, where.path);
        CHECK(code == 1);
        CHECK(errors == "ERROR: ALETHEIA_LIB=" + absent.string() + " does not exist\n");
    }
    SECTION("no kernel anywhere the search looks") {
        auto const [code, errors] = run_benchmark(arguments, report.path, {}, where.path);
        CHECK(code == 1);
        CHECK(errors == "ERROR: libaletheia-ffi.so not found; set $ALETHEIA_LIB or run "
                        "'cabal run shake -- build'\n");
    }
    CHECK(aletheia::test::read_text_file(report.path).empty());
}

// The smallest run the program takes, one frame once, with stdout on
// /dev/full, whose every write fails; the report is the text tables, or the
// JSON report under --json, which moves the tables to stderr.
TEST_CASE("a report that cannot be written exits 1 naming the mode", "[benchmark][program]") {
    auto const library = aletheia::test::find_lib();
    auto const json = GENERATE(false, true);
    CAPTURE(json);
    std::vector<std::string> args{"throughput", "--frames", "1", "--runs", "1", "--warmup", "0"};
    if (json)
        args.emplace_back("--json");
    const TempPath where{scratch_dir() / "benchmark-where", AsDirectory{}};
    auto const [code, errors] = run_benchmark(args, "/dev/full", library, where.path);
    CHECK(code == 1);
    CHECK_THAT(errors, ContainsSubstring("benchmark: writing the throughput report failed: "));
}

TEST_CASE("the launcher reads a program a signal ends as no exit code", "[program]") {
    const TempPath out{"launcher-stdout"};
    const TempPath err{"launcher-stderr"};
    CHECK(aletheia::test::run_program({"/bin/sh", "-c", "kill -KILL $$"},
                                      aletheia::test::environment_with({}),
                                      std::filesystem::current_path(), out.path, err.path) == -1);
}

TEST_CASE("the launcher runs the program in the directory it names", "[program]") {
    const TempPath where{scratch_dir() / "launcher-where", AsDirectory{}};
    const TempPath out{"launcher-stdout"};
    const TempPath err{"launcher-stderr"};
    CHECK(aletheia::test::run_program({"/bin/sh", "-c", "pwd -P"},
                                      aletheia::test::environment_with({}), where.path, out.path,
                                      err.path) == 0);
    CHECK(aletheia::test::read_text_file(out.path) ==
          std::filesystem::canonical(where.path).string() + "\n");
}

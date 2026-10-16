// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The stability harness's exit paths, each held by a run of the built harness
// in a process of its own, since the exit status is the claim. A run that
// reaches no verdict exits 2 with its line on stderr and nothing on stdout: a
// refused count, a warm-up the kernel refuses, a snapshot that cannot read
// the status file, a measured cycle that cannot load the kernel. A report that
// cannot be written exits 2 naming the write, and a run whose line stderr
// cannot take exits 2 all the same. A short run exits 0 with its report on
// stdout, and one that leaks a descriptor between the snapshots exits 1 with
// the descriptor gate failed. The snapshots fail, the descriptor leaks and the
// cycle's load fails through status_open_fault, a library preloaded into the
// harness alone. Each run writes its stdout and its stderr to the files this
// test names, and runs one cycle of one frame unless its claim needs more.

#include "child_process.hpp"
#include "repo_root.hpp"
#include "temp_path.hpp"
#include "text_file.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <cerrno>
#include <filesystem>
#include <format>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#if !defined(ALETHEIA_STABILITY_BENCH) || !defined(ALETHEIA_STATUS_OPEN_FAULT) ||                  \
    !defined(ALETHEIA_TEST_RECORDING_KERNEL)
#error "the harness's, the preload's and the stand-in kernel's paths are compile definitions"
#endif

using aletheia::test::TempPath;

namespace {

// How a run of the harness ended: its exit code, or -1 when a signal ended
// it, and what it wrote to stderr.
struct Ending {
    int code;
    std::string err;
};

} // namespace

// The name a `NAME=value` setting sets.
static auto name_of(std::string_view set) -> std::string_view {
    return set.substr(0, set.find('='));
}

// Runs the harness with its stdout on the file at `out_path` and its stderr
// on the file at `err_path`, over the environment this process started with,
// with each `NAME=value` of `extra` set and, where `extra` sets none, the
// kernel to load and one cycle of one frame, and answers its exit code, or -1
// when a signal ended it.
static auto exit_code(const std::filesystem::path& out_path, const std::filesystem::path& err_path,
                      const std::vector<std::string>& extra) -> int {
    auto settings = extra;
    for (auto& set : std::vector<std::string>{
             "ALETHEIA_LIB=" +
                 (aletheia::test::repo_root() / "build" / "libaletheia-ffi.so").string(),
             "ALETHEIA_STABILITY_CYCLES=1", "ALETHEIA_STABILITY_FRAMES=1"})
        if (std::ranges::none_of(
                extra, [&set](std::string_view given) { return name_of(given) == name_of(set); }))
            settings.push_back(std::move(set));
    return aletheia::test::run_program({ALETHEIA_STABILITY_BENCH},
                                       aletheia::test::environment_with(settings),
                                       std::filesystem::current_path(), out_path, err_path);
}

// The same run with its stderr on a file of its own, read back.
static auto run_harness(const std::filesystem::path& out_path,
                        const std::vector<std::string>& extra = {}) -> Ending {
    const TempPath err_path("stability_bench_stderr");
    auto const code = exit_code(out_path, err_path.path, extra);
    return {.code = code, .err = aletheia::test::read_text_file(err_path.path)};
}

// The setting that preloads the fault library into the harness.
static auto preload() -> std::string {
    return std::string{"LD_PRELOAD="} + ALETHEIA_STATUS_OPEN_FAULT;
}

TEST_CASE("a count that is not a whole number from 1 to 2147483647 exits 2 naming the variable",
          "[stability][process]") {
    auto const name =
        GENERATE(as<std::string>{}, "ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES");
    auto const value = GENERATE(as<std::string>{}, "abc", "0", "-3", "5x", "", "+5", " 5",
                                "2147483648", "99999999999999999999");
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {std::format("{}={}", name, value)});
    CHECK(ending.code == 2);
    CHECK(ending.err ==
          std::format("setup: {} must be a whole number from 1 to 2147483647, got '{}'\n", name,
                      value));
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("a warm-up the kernel refuses exits 2 naming the step", "[stability][process]") {
    // The stand-in answers every call with a refusal.
    const TempPath out("stability_bench_stdout");
    auto const ending =
        run_harness(out.path, {std::string{"ALETHEIA_LIB="} + ALETHEIA_TEST_RECORDING_KERNEL});
    CHECK(ending.code == 2);
    CHECK(ending.err.starts_with("warm-up: parse_dbc failed: "));
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("an opening snapshot that cannot read the status file exits 2 naming it",
          "[stability][process]") {
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {preload(), "ALETHEIA_TEST_STATUS_OPENS=0"});
    CHECK(ending.code == 2);
    CHECK(ending.err ==
          "the opening snapshot failed: reading /proc/self/status: the file does not open\n");
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("a closing snapshot that cannot read the status file exits 2 naming it",
          "[stability][process]") {
    // Each snapshot opens the file twice, for the resident set and for the
    // thread count, so the third open is the closing snapshot's first.
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {preload(), "ALETHEIA_TEST_STATUS_OPENS=2"});
    CHECK(ending.code == 2);
    CHECK(ending.err ==
          "the closing snapshot failed: reading /proc/self/status: the file does not open\n");
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("a measured cycle that cannot load the kernel exits 2 naming the cycle",
          "[stability][process]") {
    // The warm-up loads the kernel, and every load after the opening
    // snapshot's first read of the status file is refused.
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {preload(), "ALETHEIA_TEST_REFUSE_LATE_LOADS=1"});
    CHECK(ending.code == 2);
    CHECK(ending.err.starts_with("cycle 0: dlopen failed: "));
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("a report that cannot be written exits 2 naming the write", "[stability][process]") {
    auto const ending = run_harness("/dev/full");
    CHECK(ending.code == 2);
    CHECK(ending.err ==
          std::format("writing the report failed: {}\n", std::generic_category().message(ENOSPC)));
}

TEST_CASE("a refusal whose line stderr cannot take still exits 2", "[stability][process]") {
    // Writing the refused count's line to a full device throws, and main
    // answers 2 for what leaves the run rather than letting it end the process.
    const TempPath out("stability_bench_stdout");
    CHECK(exit_code(out.path, "/dev/full", {"ALETHEIA_STABILITY_CYCLES=0"}) == 2);
    CHECK(aletheia::test::read_text_file(out.path).empty());
}

TEST_CASE("a short run exits 0 with its report on stdout", "[stability][process]") {
    // Two frames, so the report's counts tell the cycles from the frames.
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {"ALETHEIA_STABILITY_FRAMES=2"});
    CHECK(ending.code == 0);
    CHECK(ending.err.empty());
    auto const report = nlohmann::json::parse(aletheia::test::read_text_file(out.path));
    CHECK(report.at("binding") == "cpp");
    CHECK(report.at("cycles") == 1);
    CHECK(report.at("frames_per_cycle") == 2);
    CHECK(report.at("total_frames") == 2);
    CHECK(report.at("passed") == true);
    std::vector<std::string> names;
    for (auto const& check : report.at("sub_checks"))
        names.push_back(check.at("name").get<std::string>());
    CHECK(names ==
          std::vector<std::string>{"rss", "fd_count", "active_thread_count", "malloc_info"});
}

TEST_CASE("a descriptor leaked between the snapshots exits 1 with the descriptor gate failed",
          "[stability][process]") {
    // The third open of the status file, the closing snapshot's first, leaks
    // one before the snapshot lists the descriptors.
    const TempPath out("stability_bench_stdout");
    auto const ending = run_harness(out.path, {preload(), "ALETHEIA_TEST_STATUS_LEAK=2"});
    CHECK(ending.code == 1);
    CHECK(ending.err.empty());
    auto const report = nlohmann::json::parse(aletheia::test::read_text_file(out.path));
    CHECK(report.at("passed") == false);
    auto const& checks = report.at("sub_checks");
    auto const fds = std::ranges::find_if(
        checks, [](const nlohmann::json& check) { return check.at("name") == "fd_count"; });
    REQUIRE(fds != checks.end());
    CHECK(fds->at("delta") == 1);
    CHECK(fds->at("passed") == false);
}

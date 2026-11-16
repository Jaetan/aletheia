// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the stability harness judges each resource under its own gate,
// reports the verdict as the JSON the lane archives, and answers why when the
// report does not reach its stream. The snapshots are written here and the
// report goes to streams this test opens, so no case reads the host's state.
#include "owned_file.hpp"
#include "stability_report.hpp"
#include "stability_snapshot.hpp"

#include <aletheia/detail/checked.hpp>

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>

#include <array>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

using aletheia::bench::all_passed;
using aletheia::bench::build_sub_checks;
using aletheia::bench::report_text;
using aletheia::bench::Snapshot;
using aletheia::bench::write_report_text;
using aletheia::test::File;

namespace {

constexpr Snapshot start{.rss_bytes = std::int64_t{1024} * 1024,
                         .fd_count = 5,
                         .active_thread_count = 3,
                         .malloc_info_bytes = 4096};

// The kernel's allocation read once, before no cycle: no drift to judge.
std::vector<std::int64_t> const opening_only{500};

// What one check is expected to read: its name and its gate.
struct Gate {
    std::string_view name;
    std::string_view gate;
};

constexpr std::array<Gate, 5> gates{{
    {.name = "rss", .gate = "report"},
    {.name = "fd_count", .gate = "hard_zero"},
    {.name = "active_thread_count", .gate = "hard_zero"},
    {.name = "malloc_info", .gate = "report"},
    {.name = "kernel_allocation", .gate = "equal_per_cycle"},
}};

} // namespace

// `start` with the field `name` names moved by `by`.
static auto drifted(std::string_view name, std::int64_t by) -> Snapshot {
    auto end = start;
    if (name == "rss")
        end.rss_bytes += by;
    else if (name == "fd_count")
        end.fd_count += by;
    else if (name == "active_thread_count")
        end.active_thread_count += by;
    else
        end.malloc_info_bytes += by;
    return end;
}

TEST_CASE("build_sub_checks passes every gate with no drift", "[benchmark][stability]") {
    auto const checks = build_sub_checks(start, start, opening_only);
    REQUIRE(checks.size() == gates.size());
    for (auto const [check, gate] : std::views::zip(checks, gates)) {
        CHECK(check.name == gate.name);
        CHECK(check.gate == gate.gate);
        CHECK(check.threshold == 0);
        CHECK(check.delta == 0);
        CHECK(check.passed);
    }
    CHECK(all_passed(checks));
}

TEST_CASE("build_sub_checks fails an exact gate on a drift of one either way, and that gate alone",
          "[benchmark][stability]") {
    auto const name = GENERATE(as<std::string>{}, "fd_count", "active_thread_count");
    auto const by = GENERATE(std::int64_t{1}, std::int64_t{-1});
    auto const checks = build_sub_checks(start, drifted(name, by), opening_only);
    for (auto const& check : checks) {
        CAPTURE(check.name);
        CHECK(check.passed == (check.name != name));
        CHECK(check.delta == (check.name == name ? by : 0));
        CHECK(check.end - check.start == check.delta);
    }
    CHECK_FALSE(all_passed(checks));
}

TEST_CASE("build_sub_checks reports the resident set and the allocator's bytes whatever they drift",
          "[benchmark][stability]") {
    auto const name = GENERATE(as<std::string>{}, "rss", "malloc_info");
    auto const by = GENERATE(std::int64_t{1024} * 1024 * 1024 * 1024, -(std::int64_t{512} * 1024));
    auto const checks = build_sub_checks(start, drifted(name, by), opening_only);
    for (auto const& check : checks) {
        CAPTURE(check.name);
        CHECK(check.passed);
        CHECK(check.delta == (check.name == name ? by : 0));
    }
    CHECK(all_passed(checks));
}

TEST_CASE("build_sub_checks holds the kernel's allocation equal in every cycle",
          "[benchmark][stability]") {
    struct Case {
        std::vector<std::int64_t> readings;
        std::vector<std::int64_t> per_cycle;
        std::int64_t spread;
    };
    auto const c = GENERATE(values<Case>({
        {.readings = {500, 1500, 2500, 3500}, .per_cycle = {1000, 1000, 1000}, .spread = 0},
        {.readings = {500, 1500, 2500, 3501}, .per_cycle = {1000, 1000, 1001}, .spread = 1},
        {.readings = {500, 1501, 2501, 3501}, .per_cycle = {1001, 1000, 1000}, .spread = 1},
    }));
    auto const checks = build_sub_checks(start, start, c.readings);
    auto const& allocation = checks.back();
    CHECK(allocation.name == "kernel_allocation");
    CHECK(allocation.per_cycle == c.per_cycle);
    CHECK(allocation.spread == c.spread);
    CHECK(allocation.delta == c.readings.back() - c.readings.front());
    CHECK(allocation.passed == (c.spread == 0));
    CHECK(all_passed(checks) == (c.spread == 0));
    for (auto const& check : checks | std::views::take(checks.size() - 1)) {
        CAPTURE(check.name);
        CHECK(check.passed);
    }
}

TEST_CASE("report_text writes the counts, each check in order, and the verdict",
          "[benchmark][stability]") {
    auto end = start;
    end.rss_bytes = std::int64_t{2} * 1024 * 1024;
    end.fd_count = 6;
    CHECK(report_text(2, 3, 1.5, build_sub_checks(start, end, {500, 1500, 2501})) == R"({
  "binding": "cpp",
  "cycles": 2,
  "frames_per_cycle": 3,
  "total_frames": 6,
  "elapsed_seconds": 1.5,
  "sub_checks": [
    {
      "name": "rss",
      "gate": "report",
      "start": 1048576,
      "end": 2097152,
      "delta": 1048576,
      "threshold": 0,
      "passed": true
    },
    {
      "name": "fd_count",
      "gate": "hard_zero",
      "start": 5,
      "end": 6,
      "delta": 1,
      "threshold": 0,
      "passed": false
    },
    {
      "name": "active_thread_count",
      "gate": "hard_zero",
      "start": 3,
      "end": 3,
      "delta": 0,
      "threshold": 0,
      "passed": true
    },
    {
      "name": "malloc_info",
      "gate": "report",
      "start": 4096,
      "end": 4096,
      "delta": 0,
      "threshold": 0,
      "passed": true
    },
    {
      "name": "kernel_allocation",
      "gate": "equal_per_cycle",
      "start": 500,
      "end": 2501,
      "delta": 2001,
      "threshold": 0,
      "per_cycle": [1000, 1001],
      "spread": 1,
      "passed": false
    }
  ],
  "passed": false
}
)");
}

TEST_CASE("report_text counts the total frames past an int", "[benchmark][stability]") {
    auto const text =
        report_text(100000, 100000, 0.0, build_sub_checks(start, start, opening_only));
    CHECK(text.contains("\"total_frames\": 10000000000,\n"));
    CHECK(text.ends_with("  \"passed\": true\n}\n"));
}

TEST_CASE("write_report_text puts the whole text on its stream", "[benchmark][stability]") {
    char* written = nullptr;
    std::size_t size = 0;
    File stream{open_memstream(&written, &size)};
    REQUIRE(stream != nullptr);
    CHECK(write_report_text(stream.get(), "{\"passed\": true}\n").has_value());
    // Closing the stream publishes its buffer.
    stream.reset();
    std::unique_ptr<char, decltype(&std::free)> const owner(written, &std::free);
    CHECK(std::string_view{written, size} == "{\"passed\": true}\n");
}

TEST_CASE("write_report_text answers why a stream that buffers the text cannot flush it",
          "[benchmark][stability]") {
    File const full{std::fopen("/dev/full", "we")};
    REQUIRE(full != nullptr);
    auto const written = write_report_text(full.get(), "{\"passed\": true}\n");
    REQUIRE_FALSE(written.has_value());
    CHECK(written.error() == std::generic_category().message(ENOSPC));
}

TEST_CASE("write_report_text answers why a stream that does not buffer cannot take the text",
          "[benchmark][stability]") {
    File const full{std::fopen("/dev/full", "we")};
    REQUIRE(full != nullptr);
    REQUIRE(std::setvbuf(full.get(), nullptr, _IONBF, 0) == 0);
    auto const written = write_report_text(full.get(), "{\"passed\": true}\n");
    REQUIRE_FALSE(written.has_value());
    CHECK(written.error() == std::generic_category().message(ENOSPC));
}

// A read tried on a stream open for writing fails and sets the stream's error
// indicator alone, so the text reaches memory and the flush succeeds: the
// indicator is all that records a failure on the stream.
TEST_CASE("write_report_text refuses a stream whose error indicator is set",
          "[benchmark][stability]") {
    std::array<char, 64> memory{};
    File const stream{fmemopen(memory.data(), memory.size(), "w")};
    REQUIRE(stream != nullptr);
    REQUIRE(std::fgetc(stream.get()) == EOF);
    REQUIRE(std::ferror(stream.get()) != 0);
    auto const written = write_report_text(stream.get(), "{\"passed\": true}\n");
    CHECK(std::string_view{memory.data()} == "{\"passed\": true}\n");
    REQUIRE_FALSE(written.has_value());
    CHECK(aletheia::detail::error_of(written) == std::generic_category().message(EIO));
}

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
using aletheia::bench::k_malloc_delta_bytes_cap;
using aletheia::bench::k_rss_delta_bytes_cap;
using aletheia::bench::report_text;
using aletheia::bench::Snapshot;
using aletheia::bench::write_report_text;
using aletheia::test::File;

namespace {

constexpr Snapshot start{.rss_bytes = std::int64_t{1024} * 1024,
                         .fd_count = 5,
                         .active_thread_count = 3,
                         .malloc_info_bytes = 4096};

// What one check is expected to read: its name, its gate and its threshold.
struct Gate {
    std::string_view name;
    std::string_view gate;
    std::int64_t threshold;
};

constexpr std::array<Gate, 4> gates{{
    {.name = "rss", .gate = "soft_threshold", .threshold = k_rss_delta_bytes_cap},
    {.name = "fd_count", .gate = "hard_zero", .threshold = 0},
    {.name = "active_thread_count", .gate = "hard_zero", .threshold = 0},
    {.name = "malloc_info", .gate = "soft_threshold", .threshold = k_malloc_delta_bytes_cap},
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
    auto const checks = build_sub_checks(start, start);
    REQUIRE(checks.size() == gates.size());
    for (auto const [check, gate] : std::views::zip(checks, gates)) {
        CHECK(check.name == gate.name);
        CHECK(check.gate == gate.gate);
        CHECK(check.threshold == gate.threshold);
        CHECK(check.delta == 0);
        CHECK(check.passed);
    }
    CHECK(all_passed(checks));
}

TEST_CASE("build_sub_checks fails an exact gate on a drift of one either way, and that gate alone",
          "[benchmark][stability]") {
    auto const name = GENERATE(as<std::string>{}, "fd_count", "active_thread_count");
    auto const by = GENERATE(std::int64_t{1}, std::int64_t{-1});
    auto const checks = build_sub_checks(start, drifted(name, by));
    for (auto const& check : checks) {
        CAPTURE(check.name);
        CHECK(check.passed == (check.name != name));
        CHECK(check.delta == (check.name == name ? by : 0));
        CHECK(check.end - check.start == check.delta);
    }
    CHECK_FALSE(all_passed(checks));
}

TEST_CASE("build_sub_checks fails a soft gate only past its cap, either way",
          "[benchmark][stability]") {
    auto const [name, cap] = GENERATE(table<std::string, std::int64_t>(
        {{"rss", k_rss_delta_bytes_cap}, {"malloc_info", k_malloc_delta_bytes_cap}}));
    auto const sign = GENERATE(std::int64_t{1}, std::int64_t{-1});
    auto const at_cap = build_sub_checks(start, drifted(name, sign * cap));
    CHECK(all_passed(at_cap));
    auto const past_cap = build_sub_checks(start, drifted(name, sign * (cap + 1)));
    for (auto const& check : past_cap) {
        CAPTURE(check.name);
        CHECK(check.passed == (check.name != name));
        CHECK(check.delta == (check.name == name ? sign * (cap + 1) : 0));
        CHECK(check.end - check.start == check.delta);
    }
    CHECK_FALSE(all_passed(past_cap));
}

TEST_CASE("report_text writes the counts, each check in order, and the verdict",
          "[benchmark][stability]") {
    auto end = start;
    end.rss_bytes = std::int64_t{2} * 1024 * 1024;
    end.fd_count = 6;
    CHECK(report_text(2, 3, 1.5, build_sub_checks(start, end)) == R"({
  "binding": "cpp",
  "cycles": 2,
  "frames_per_cycle": 3,
  "total_frames": 6,
  "elapsed_seconds": 1.5,
  "sub_checks": [
    {
      "name": "rss",
      "gate": "soft_threshold",
      "start": 1048576,
      "end": 2097152,
      "delta": 1048576,
      "threshold": 52428800,
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
      "gate": "soft_threshold",
      "start": 4096,
      "end": 4096,
      "delta": 0,
      "threshold": 52428800,
      "passed": true
    }
  ],
  "passed": false
}
)");
}

TEST_CASE("report_text counts the total frames past an int", "[benchmark][stability]") {
    auto const text = report_text(100000, 100000, 0.0, build_sub_checks(start, start));
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
    const std::unique_ptr<char, decltype(&std::free)> owner(written, &std::free);
    CHECK(std::string_view{written, size} == "{\"passed\": true}\n");
}

TEST_CASE("write_report_text answers why a stream that buffers the text cannot flush it",
          "[benchmark][stability]") {
    const File full{std::fopen("/dev/full", "we")};
    REQUIRE(full != nullptr);
    auto const written = write_report_text(full.get(), "{\"passed\": true}\n");
    REQUIRE_FALSE(written.has_value());
    CHECK(written.error() == std::generic_category().message(ENOSPC));
}

TEST_CASE("write_report_text answers why a stream that does not buffer cannot take the text",
          "[benchmark][stability]") {
    const File full{std::fopen("/dev/full", "we")};
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
    const File stream{fmemopen(memory.data(), memory.size(), "w")};
    REQUIRE(stream != nullptr);
    REQUIRE(std::fgetc(stream.get()) == EOF);
    REQUIRE(std::ferror(stream.get()) != 0);
    auto const written = write_report_text(stream.get(), "{\"passed\": true}\n");
    CHECK(std::string_view{memory.data()} == "{\"passed\": true}\n");
    REQUIRE_FALSE(written.has_value());
    CHECK(aletheia::detail::error_of(written) == std::generic_category().message(EIO));
}

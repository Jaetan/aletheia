// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the benchmark harness's report destination and the rules its
// headings and tables are drawn with, read back from a stream over memory; and
// its report check: a report its stream refuses fails the run naming the mode
// and the reason, whether the refusal comes while the lane prints, at the
// flush after it or in the stream's error indicator alone, and a report its
// stream takes is flushed whole. The refusing stream is /dev/full, whose every
// write fails with ENOSPC, and each stream writes through a buffer of the
// test's own size, so a report under or over the buffer is a byte count rather
// than the host's. The size is one the C library fills before it writes, as it
// fills stdout's: under 128 bytes, glibc writes what it is given straight
// through.
#include "benchmark_output.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>

#include <array>
#include <cerrno>
#include <cstddef>
#include <cstdio>
#include <format>
#include <functional>
#include <print>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>

#include "owned_file.hpp"

using aletheia::bench::k_rule_heavy, aletheia::bench::out_file, aletheia::bench::print_header,
    aletheia::bench::print_separator, aletheia::bench::write_mode_report;
using aletheia::test::File;
using Catch::Matchers::Message;

namespace {

constexpr std::size_t buffer_size = 256;
using Buffer = std::array<char, buffer_size>;

// Points the report's destination at `stream` for this object's scope, and
// back at the one it replaced after it, so no later case prints into a closed
// stream.
class Destination {
public:
    explicit Destination(std::FILE* stream) : replaced_{std::exchange(out_file(), stream)} {}
    ~Destination() { out_file() = replaced_; }

    Destination(Destination const&) = delete;
    Destination(Destination&&) = delete;
    auto operator=(Destination const&) -> Destination& = delete;
    auto operator=(Destination&&) -> Destination& = delete;

private:
    std::FILE* replaced_;
};

} // namespace

// `file`, opened or not, writing through `buffer` once it is full.
static auto buffered(std::FILE* file, Buffer& buffer) -> File {
    REQUIRE(file != nullptr);
    File owned{file};
    REQUIRE(std::setvbuf(owned.get(), buffer.data(), _IOFBF, buffer.size()) == 0);
    return owned;
}

// A report shorter than the buffer stays in it until the flush, the only write
// that can fail.
TEST_CASE("a report under the buffer that cannot be written names the mode",
          "[benchmark][report]") {
    Buffer buffer{};
    auto const report = buffered(std::fopen("/dev/full", "w"), buffer);
    REQUIRE_THROWS_MATCHES(
        write_mode_report(report.get(), "throughput",
                          [&report] { std::println(report.get(), "Throughput"); }),
        std::system_error,
        Message("writing the throughput report failed: No space left on device"));
}

// A report longer than the buffer is written while the lane prints, and the
// print path throws out of the lane when that write fails. The reason it gives
// is the standard library's, so the test reads it from the same write unchecked.
TEST_CASE("a report over the buffer that cannot be written names the mode", "[benchmark][report]") {
    auto const line = std::string(buffer_size * 2, '-');
    Buffer unchecked_buffer{};
    auto const unchecked = buffered(std::fopen("/dev/full", "w"), unchecked_buffer);
    auto reason = std::error_code{};
    try {
        std::println(unchecked.get(), "{}", line);
    } catch (std::system_error const& e) {
        reason = e.code();
    }
    REQUIRE(reason);

    Buffer buffer{};
    auto const report = buffered(std::fopen("/dev/full", "w"), buffer);
    REQUIRE_THROWS_MATCHES(
        write_mode_report(report.get(), "latency",
                          [&report, &line] { std::println(report.get(), "{}", line); }),
        std::system_error,
        Message(std::format("writing the latency report failed: {}", reason.message())));
}

// A write that failed before the check leaves the stream's error indicator set
// and its buffer empty, so the flush has nothing to write and succeeds.
TEST_CASE("a report whose stream already failed a write names the mode", "[benchmark][report]") {
    Buffer buffer{};
    auto const report = buffered(std::fopen("/dev/full", "w"), buffer);
    REQUIRE(std::fputc('\n', report.get()) == '\n');
    REQUIRE(std::fflush(report.get()) == EOF);
    REQUIRE_THROWS_MATCHES(write_mode_report(report.get(), "scaling", [] {}), std::system_error,
                           Message("writing the scaling report failed: Input/output error"));
}

// The second line, with its newline, fills the buffer exactly. libstdc++ 16
// drops that buffer without throwing, leaving the error indicator alone to
// record the failure; libstdc++ 15 throws EIO from the print. Either way the
// report reads EIO.
TEST_CASE("a report whose print fills a buffer it cannot write names the mode",
          "[benchmark][report]") {
    auto const line = std::string(buffer_size - 1, '-');
    Buffer buffer{};
    auto const report = buffered(std::fopen("/dev/full", "w"), buffer);
    REQUIRE_THROWS_MATCHES(write_mode_report(report.get(), "latency",
                                             [&report, &line] {
                                                 std::println(report.get(), "Latency");
                                                 std::println(report.get(), "{}", line);
                                             }),
                           std::system_error,
                           Message("writing the latency report failed: Input/output error"));
}

TEST_CASE("a report its stream takes is flushed whole", "[benchmark][report]") {
    Buffer buffer{};
    Buffer memory{};
    auto const report = buffered(fmemopen(memory.data(), memory.size(), "w"), buffer);
    REQUIRE_NOTHROW(write_mode_report(report.get(), "throughput",
                                      [&report] { std::print(report.get(), "Throughput"); }));
    CHECK(std::string_view{memory.data()} == "Throughput");
}

// The report's stream decides: an error the lane raises while the report is
// whole is the lane's own, and leaves as it was raised.
TEST_CASE("an error the lane raises passes through unchanged", "[benchmark][report]") {
    Buffer buffer{};
    Buffer memory{};
    auto const report = buffered(fmemopen(memory.data(), memory.size(), "w"), buffer);
    SECTION("a system error") {
        REQUIRE_THROWS_MATCHES(
            write_mode_report(
                report.get(), "throughput",
                [] { throw std::system_error{ENOENT, std::generic_category(), "dlopen"}; }),
            std::system_error, Message("dlopen: No such file or directory"));
    }
    SECTION("any other error") {
        REQUIRE_THROWS_MATCHES(
            write_mode_report(report.get(), "throughput",
                              [] { throw std::runtime_error{"extract_signals failed"}; }),
            std::runtime_error, Message("extract_signals failed"));
    }
}

// What `print` writes to the report's destination, read back from a stream
// over memory.
static auto printed(std::function<void()> const& print) -> std::string {
    Buffer memory{};
    File const report{fmemopen(memory.data(), memory.size(), "w")};
    REQUIRE(report != nullptr);
    {
        Destination const destination{report.get()};
        print();
    }
    REQUIRE(std::fflush(report.get()) == 0);
    auto const length = std::ftell(report.get());
    REQUIRE(length >= 0);
    return {memory.data(), static_cast<std::size_t>(length)};
}

// The harness moves the destination to stderr under --json, which keeps stdout
// for the JSON report.
TEST_CASE("the report's destination is stdout until the harness moves it", "[benchmark][report]") {
    CHECK(out_file() == stdout);
}

TEST_CASE("a heading is its title between two heavy rules", "[benchmark][report]") {
    CHECK(printed([] { print_header("Summary"); }) ==
          std::format("{}\nSummary\n{}\n", k_rule_heavy, k_rule_heavy));
}

TEST_CASE("a table's separator is a light rule as wide as the heavy one", "[benchmark][report]") {
    CHECK(printed([] { print_separator(); }) == std::string(k_rule_heavy.size(), '-') + '\n');
}

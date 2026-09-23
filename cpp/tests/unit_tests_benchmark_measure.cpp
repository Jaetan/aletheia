// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the benchmarks' timed loops abort on a failed operation and
// compute their figures from the clock they are given. Every case runs under
// a clock that advances a fixed step per reading, so nothing here reads the
// host's time and every number asserted is exact.
#include "measure.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>
#include <catch2/matchers/catch_matchers_floating_point.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/error.hpp>

#include <chrono>
#include <expected>
#include <stdexcept>
#include <vector>

using namespace aletheia;
using aletheia::bench::latencies_us;
using aletheia::bench::operations_per_second;
using Catch::Matchers::ContainsSubstring;
using Catch::Matchers::MessageMatches;
using Catch::Matchers::WithinRel;

namespace {

// Reads ten microseconds later on every call, counting from zero at reset, and
// never the host's time: the reading is arithmetic on how often it was asked.
struct SteppingClock {
    static constexpr std::chrono::microseconds step{10};

    static auto now() -> std::chrono::steady_clock::time_point {
        readings() += 1;
        return std::chrono::steady_clock::time_point{readings() * step};
    }
    static auto readings() -> int& {
        static int count = 0;
        return count;
    }
    static void reset() { readings() = 0; }
};

constexpr auto never = 1'000'000;

} // namespace

// An operation that records every index it is called with, succeeds below
// `failing_at` and fails from that index on.
static auto failing_at(int failing_at, std::vector<int>& calls) {
    return [failing_at, &calls](int i) -> Result<void> {
        calls.push_back(i);
        if (i >= failing_at)
            return std::unexpected(AletheiaError{ErrorKind::State, "not streaming"});
        return {};
    };
}

TEST_CASE("operations_per_second divides the count by the clock's elapsed seconds",
          "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    // Two readings, one step apart: 4 operations in 10 us.
    auto const fps =
        operations_per_second<SteppingClock>(4, "send_frame", failing_at(never, calls));
    CHECK_THAT(fps, WithinRel(400'000.0, 1e-12));
    CHECK(calls == std::vector<int>{0, 1, 2, 3});
    CHECK(SteppingClock::readings() == 2);
}

TEST_CASE("operations_per_second aborts at the first failed operation, naming the step",
          "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    CHECK_THROWS_MATCHES(
        operations_per_second<SteppingClock>(5, "extract_signals", failing_at(2, calls)),
        std::runtime_error,
        MessageMatches(ContainsSubstring("extract_signals failed: ") &&
                       ContainsSubstring("not streaming")));
    // The failing call is the last one made.
    CHECK(calls == std::vector<int>{0, 1, 2});
}

TEST_CASE("latencies_us times each measured call and skips the warmup", "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    auto const latencies =
        latencies_us<SteppingClock>(2, 3, "build_frame", failing_at(never, calls));
    CHECK(latencies == std::vector<double>{10.0, 10.0, 10.0});
    // Warmup calls are made and untimed, and the measured calls continue the
    // index from where the warmup left it.
    CHECK(calls == std::vector<int>{0, 1, 2, 3, 4});
    // Two readings per measured call, none for the warmup.
    CHECK(SteppingClock::readings() == 6);
}

TEST_CASE("latencies_us aborts on a failed warmup call", "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    CHECK_THROWS_MATCHES(latencies_us<SteppingClock>(2, 3, "send_frame", failing_at(1, calls)),
                         std::runtime_error,
                         MessageMatches(ContainsSubstring("send_frame failed")));
    CHECK(calls == std::vector<int>{0, 1});
}

TEST_CASE("latencies_us aborts on a failed measured call", "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    CHECK_THROWS_MATCHES(latencies_us<SteppingClock>(2, 3, "send_frame", failing_at(3, calls)),
                         std::runtime_error,
                         MessageMatches(ContainsSubstring("send_frame failed")));
    CHECK(calls == std::vector<int>{0, 1, 2, 3});
}

TEST_CASE("a zero count measures nothing and returns nothing", "[benchmark][measure]") {
    SteppingClock::reset();
    std::vector<int> calls;
    CHECK(latencies_us<SteppingClock>(0, 0, "send_frame", failing_at(never, calls)).empty());
    CHECK(calls.empty());
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The step check the benchmark and stability harnesses share, and the
// benchmark harness's timed loops. An operation that fails inside one measures
// nothing: its error leaves the loop as an exception naming the step, and the
// lane aborts with it instead of timing the failure as a success. The clock is
// a type parameter so a test can drive the loops with one that reads no host
// time.
#pragma once

#include <aletheia/error.hpp>

#include <chrono>
#include <concepts>
#include <format>
#include <ranges>
#include <ratio>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace aletheia::bench {

// Throws the error a step returned, named by the step.
template<typename T>
void require(const Result<T>& result, std::string_view step) {
    if (!result)
        throw std::runtime_error(std::format("{} failed: {}", step, result.error().message()));
}

// Operations per second over `count` calls of op(i), i counting from zero,
// under one reading of the clock before the first call and one after the last.
template<typename Clock = std::chrono::steady_clock, std::invocable<int> Op>
auto operations_per_second(int count, std::string_view step, Op op) -> double {
    auto const start = Clock::now();
    for (auto const i : std::views::iota(0, count))
        require(op(i), step);
    auto const end = Clock::now();
    auto const elapsed = std::chrono::duration<double>(end - start).count();
    return static_cast<double>(count) / elapsed;
}

// Microseconds per call, one entry per timed call. The first `warmup` calls
// run untimed and the timed ones continue the count, so op(i) sees every i
// below warmup + count once, whether or not that call was timed.
template<typename Clock = std::chrono::steady_clock, std::invocable<int> Op>
auto latencies_us(int warmup, int count, std::string_view step, Op op) -> std::vector<double> {
    for (auto const i : std::views::iota(0, warmup))
        require(op(i), step);
    std::vector<double> latencies;
    for (auto const i : std::views::iota(0, count)) {
        auto const start = Clock::now();
        require(op(warmup + i), step);
        auto const end = Clock::now();
        latencies.push_back(std::chrono::duration<double, std::micro>(end - start).count());
    }
    return latencies;
}

} // namespace aletheia::bench

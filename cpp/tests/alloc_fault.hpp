// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Fails a chosen heap allocation, so a test can reach the cleanup path a
// throwing container leaves behind, and counts the blocks the program holds,
// so anything that path forgets to release is visible as an imbalance.
// The replacement of the global allocation functions lives in alloc_fault.cpp.
#pragma once

#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

namespace aletheia::test::alloc_fault {

// Blocks the program holds: one per allocation, less one per release.
[[nodiscard]] auto live_blocks() -> std::int64_t;

// Allocations the program has made so far, whoever made them: a call's
// count is the difference across it.
[[nodiscard]] auto allocations() -> std::int64_t;

// The allocations `call` makes, whoever makes them.
[[nodiscard]] auto allocations_of(auto call) -> std::int64_t {
    auto const before = allocations();
    static_cast<void>(call());
    return allocations() - before;
}

// Arms the nth allocation made by this thread, from here on, to fail with
// std::bad_alloc, once. An allocation the JSON or the spreadsheet library
// makes for itself does not count and is never failed: the JSON library's
// document destructor allocates to flatten what it is freeing, and a
// destructor is noexcept, so a failure there ends the program instead of
// unwinding, and the spreadsheet library ends the program the same way. The
// code under test is reached by failing its own allocations, which this
// leaves alone.
// Disarms when it goes out of scope, fired or not.
class Arm {
public:
    explicit Arm(std::int64_t nth);
    ~Arm();
    Arm(const Arm&) = delete;
    Arm(Arm&&) = delete;
    auto operator=(const Arm&) -> Arm& = delete;
    auto operator=(Arm&&) -> Arm& = delete;

    // Whether the armed allocation was reached.
    [[nodiscard]] auto fired() const -> bool { return fired_; }

private:
    bool fired_ = false;
};

// Records, over one run of the code between the two calls, the ordinal of
// every allocation that is this project's own, into `ordinals`. Ending the
// recording says whether it held them all.
void begin_recording(std::vector<std::int64_t>& ordinals);
[[nodiscard]] auto end_recording() -> bool;

// The ordinals of the allocations `call` makes for itself, from one recorded
// run, or none when the recording could not hold them. Every exception is
// swallowed here and below: a refusal still records what it allocated.
template<typename Call>
[[nodiscard]] auto own_allocations(Call call) -> std::vector<std::int64_t> {
    std::vector<std::int64_t> ordinals;
    begin_recording(ordinals);
    try {
        static_cast<void>(call());
    } catch (...) { // NOLINT(bugprone-empty-catch): a refusal still records what it allocated
    }
    if (!end_recording()) {
        ordinals.clear();
    }
    return ordinals;
}

// Runs `call` once per ordinal, failing that allocation each time, and says
// whether every fault was reached: one that was not says the call does not
// allocate the same way twice, rather than that it leaks.
template<typename Call>
[[nodiscard]] auto fault_each(Call call, const std::vector<std::int64_t>& ordinals) -> bool {
    return std::ranges::all_of(ordinals, [&](std::int64_t nth) {
        const Arm arm{nth};
        try {
            // The call answers with what it decoded, which the sweep does not read.
            static_cast<void>(call());
        } catch (...) { // NOLINT(bugprone-empty-catch): the failure is the point
        }
        return arm.fired();
    });
}

// Runs `call` once per allocation of its own it makes, failing a different
// one each time, and returns how many it covered. The allocations are found
// by one recorded run and the faults land on those alone, so a library's own
// allocations, which may not be failed, never cost a walk of the stack at the
// fault. Returns -1 when the recording could not hold the call's allocations,
// when they are more than `cap`, or when a fault was not reached.
template<typename Call>
auto sweep(Call call, std::int64_t cap = 4000) -> std::int64_t {
    auto const ordinals = own_allocations(call);
    if (ordinals.empty() || std::cmp_greater(ordinals.size(), cap)) {
        return ordinals.empty() ? 0 : -1;
    }
    return fault_each(call, ordinals) ? static_cast<std::int64_t>(ordinals.size()) : -1;
}

// Sweeps `call` twice and reports the allocation points it covered and what
// the block count did over the second sweep. The first settles whatever the
// call reaches for once and keeps, which a single sweep would read as a block
// the call lost; anything a cleanup path drops is dropped again on the second.
struct SweepResult {
    std::int64_t points;
    std::int64_t held;
};

[[nodiscard]] auto measure(auto call) -> SweepResult {
    // Recorded again for the second sweep, since what the first settled is
    // allocated no more.
    static_cast<void>(sweep(call));
    auto const before = live_blocks();
    auto const points = sweep(call);
    return {.points = points, .held = live_blocks() - before};
}

// Fails each allocation of `call` in turn and asserts it released everything.
void expect_balanced(auto call) {
    auto const result = measure(call);
    CHECK(result.points > 0);
    CHECK(result.held == 0);
}

} // namespace aletheia::test::alloc_fault

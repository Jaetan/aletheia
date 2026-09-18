// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Fails a chosen heap allocation, so a test can reach the cleanup path a
// throwing container leaves behind, and counts the blocks the program holds,
// so anything that path forgets to release is visible as an imbalance.
// The replacement of the global allocation functions lives in alloc_fault.cpp.
#pragma once

#include <cstdint>

namespace aletheia::test::alloc_fault {

// Blocks the program holds: one per allocation, less one per release.
[[nodiscard]] auto live_blocks() -> std::int64_t;

// Arms the nth allocation made by this thread, from here on, to fail with
// std::bad_alloc, once. An allocation the JSON library makes for itself does
// not count and is never failed: that library's document destructor allocates
// to flatten what it is freeing, and a destructor is noexcept, so a failure
// there ends the program instead of unwinding. The code under test is reached
// by failing its own allocations, which this leaves alone.
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

// Runs `call` once per allocation it makes, failing a later one each time,
// and returns the number of allocations it covered. Every exception is
// swallowed: the call is expected to fail, and what the test reads afterwards
// is the block count. Returns -1 when `cap` runs out, which says the call
// allocates more than the sweep was meant to cover rather than that it leaks.
template<typename Call>
auto sweep(Call call, std::int64_t cap = 4000) -> std::int64_t {
    for (std::int64_t nth = 1; nth <= cap; ++nth) {
        const Arm arm{nth};
        try {
            // The call answers with what it decoded, which the sweep does not read.
            static_cast<void>(call());
        } catch (...) { // NOLINT(bugprone-empty-catch): the failure is the point
        }
        if (!arm.fired()) {
            return nth - 1;
        }
    }
    return -1;
}

} // namespace aletheia::test::alloc_fault

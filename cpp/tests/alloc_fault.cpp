// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Replaces the global allocation functions for the test binary: every block is
// counted, and one allocation per armed scope fails. The array and sized forms
// are left to the standard's defaults, which call the two replaced here, so
// every block this program allocates is one this file counted.
#include "alloc_fault.hpp"

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <dlfcn.h>
#include <new>
#include <string_view>

namespace {

// What this thread's innermost arming is waiting for. Trivial and
// constant-initialised, so reading it from an allocation function neither
// allocates nor runs a guard.
struct Fault {
    std::int64_t countdown = 0;
    bool* fired = nullptr;
};

} // namespace

// The arming is per thread, so a sweep leaves every other thread allocating.
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below reads it
static thread_local Fault t_fault;

// The count is not per thread, because a block allocated on one thread is
// released on another.
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below writes it
static std::atomic<std::int64_t> g_live_blocks{0};

// The JSON library allocates while it destroys a document, to hold what it is
// flattening, and the destructor it does that from is noexcept: a failure
// there ends the program rather than unwinding, and nothing the library does
// with it is this project's code under test. An allocation is attributed by
// the address it returns to, which names the function that asked for it.
[[nodiscard]] static auto belongs_to_the_json_library(const void* site) -> bool {
    Dl_info info{};
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-const-cast): dladdr takes a mutable pointer
    if (dladdr(const_cast<void*>(site), &info) == 0 || info.dli_sname == nullptr) {
        return false;
    }
    return std::string_view{info.dli_sname}.contains("nlohmann");
}

namespace aletheia::test::alloc_fault {

auto live_blocks() -> std::int64_t {
    return g_live_blocks.load(std::memory_order_relaxed);
}

Arm::Arm(std::int64_t nth) {
    t_fault.countdown = nth;
    t_fault.fired = &fired_;
}

Arm::~Arm() {
    t_fault.countdown = 0;
    t_fault.fired = nullptr;
}

} // namespace aletheia::test::alloc_fault

auto operator new(std::size_t size) -> void* {
    if (t_fault.countdown > 0) {
        --t_fault.countdown;
        if (t_fault.countdown == 0) {
            if (belongs_to_the_json_library(__builtin_return_address(0))) {
                t_fault.countdown = 1; // the next allocation that is this project's
            } else {
                *t_fault.fired = true;
                throw std::bad_alloc{};
            }
        }
    }
    // A zero-sized request still answers with a distinct address.
    void* block = std::malloc(size != 0 ? size : 1); // NOLINT(cppcoreguidelines-no-malloc)
    if (block == nullptr) {
        throw std::bad_alloc{};
    }
    g_live_blocks.fetch_add(1, std::memory_order_relaxed);
    return block;
}

void operator delete(void* block) noexcept {
    if (block != nullptr) {
        g_live_blocks.fetch_sub(1, std::memory_order_relaxed);
    }
    std::free(block); // NOLINT(cppcoreguidelines-no-malloc)
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Replaces the global allocation functions for the test binary: every block is
// counted, and one allocation per armed scope fails. The array and sized forms
// are left to the standard's defaults, which call the two replaced here, so
// every block this program allocates is one this file counted.
#include "alloc_fault.hpp"

#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <dlfcn.h>
#include <execinfo.h>
#include <new>
#include <ranges>
#include <string_view>
#include <vector>

namespace {

// What this thread's innermost arming is waiting for. Trivial and
// constant-initialised, so reading it from an allocation function neither
// allocates nor runs a guard.
struct Fault {
    std::int64_t countdown = 0;
    bool* fired = nullptr;
};

// A recording in progress on this thread: every allocation is counted, and
// the ordinals of the ones that are this project's are kept. The buffer is
// reserved before the recording starts, so keeping an ordinal allocates
// nothing; a recording that would outgrow it stops and says so.
struct Recording {
    bool active = false;
    bool in_hook = false;
    bool overflowed = false;
    std::int64_t seen = 0;
    std::vector<std::int64_t>* ordinals = nullptr;
};

} // namespace

// The arming is per thread, so a sweep leaves every other thread allocating.
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below reads it
static thread_local Fault t_fault;
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below writes it
static thread_local Recording t_recording;

// The count is not per thread, because a block allocated on one thread is
// released on another.
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below writes it
static std::atomic<std::int64_t> g_live_blocks{0};
// Every allocation the program has made, whoever made it.
// NOLINTNEXTLINE(cppcoreguidelines-avoid-non-const-global-variables): the hook below writes it
static std::atomic<std::int64_t> g_allocations{0};

// Ordinals a recording keeps at most; a call allocating more of its own than
// this is beyond what a sweep was meant to cover.
constexpr std::size_t k_recording_capacity = 1U << 16U;

// The JSON library allocates while it destroys a document, to hold what it is
// flattening, and the destructor it does that from is noexcept: a failure
// there ends the program rather than unwinding. The spreadsheet library ends
// the program the same way on an allocation that fails inside it. None of the
// vendored libraries is this project's code under test, so an allocation any
// of them makes for itself is never failed, and the YAML library is spared on
// the same ground. A library is known by a frame of its own on the stack,
// since what it allocates it allocates through the standard library's own
// functions, whose frames name no owner.
[[nodiscard]] static auto symbol_at(const void* site) -> std::string_view {
    Dl_info info{};
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-const-cast): dladdr takes a mutable pointer
    if (dladdr(const_cast<void*>(site), &info) == 0 || info.dli_sname == nullptr) {
        return {};
    }
    return info.dli_sname;
}

// The stack above an allocation, to the depth a vendored library's frame is
// found at: the allocation function, the standard-library template that
// asked, and the library function that called it are the first few frames.
constexpr std::size_t k_stack_depth = 8;

[[nodiscard]] static auto vendored_frame_among(const std::array<void*, k_stack_depth>& frames,
                                               int depth) -> bool {
    // take clamps, so a depth the capture never filled reads nothing rather
    // than past the array.
    return std::ranges::any_of(frames | std::views::take(depth), [](auto const* const frame) {
        auto const name = symbol_at(frame);
        return name.contains("nlohmann") || name.contains("OpenXLSX") || name.contains("4YAML");
    });
}

// Whether the allocation the hook is answering is a vendored library's own,
// decided from the stack. A stack seen before answers from a table keyed on
// its frames, since a recording sees the same few stacks thousands of times
// and naming a frame is the cost. The table is fixed in size and allocates
// nothing, so the hook never re-enters itself; a full table only costs the
// walk again.
[[nodiscard]] static auto belongs_to_a_vendored_library() -> bool {
    struct Seen {
        std::array<void*, k_stack_depth> frames{};
        bool filled = false;
        bool vendored = false;
    };
    constexpr std::size_t k_slots = 1U << 13U;
    static thread_local std::array<Seen, k_slots> table;
    std::array<void*, k_stack_depth> frames{};
    auto const depth = backtrace(frames.data(), static_cast<int>(frames.size()));
    std::size_t hash = 0;
    for (auto const* frame : frames) {
        hash = (hash * 1099511628211ULL) ^ std::bit_cast<std::uintptr_t>(frame);
    }
    for (auto const probe : std::views::iota(std::size_t{0}, std::size_t{8})) {
        auto& slot = table[(hash + probe) & (k_slots - 1)];
        if (!slot.filled) {
            slot.frames = frames;
            slot.filled = true;
            slot.vendored = vendored_frame_among(frames, depth);
            return slot.vendored;
        }
        if (slot.frames == frames) {
            return slot.vendored;
        }
    }
    return vendored_frame_among(frames, depth);
}

namespace aletheia::test::alloc_fault {

auto live_blocks() -> std::int64_t {
    return g_live_blocks.load(std::memory_order_relaxed);
}

auto allocations() -> std::int64_t {
    return g_allocations.load(std::memory_order_relaxed);
}

void begin_recording(std::vector<std::int64_t>& ordinals) {
    ordinals.clear();
    ordinals.reserve(k_recording_capacity);
    t_recording = Recording{.active = true, .ordinals = &ordinals};
}

auto end_recording() -> bool {
    auto const overflowed = t_recording.overflowed;
    t_recording = Recording{};
    return !overflowed;
}

auto recording_capacity() -> std::size_t {
    return k_recording_capacity;
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
    if (t_recording.active && !t_recording.in_hook) {
        t_recording.in_hook = true;
        ++t_recording.seen;
        if (!belongs_to_a_vendored_library()) {
            if (t_recording.ordinals->size() < t_recording.ordinals->capacity()) {
                t_recording.ordinals->push_back(t_recording.seen);
            } else {
                t_recording.overflowed = true;
            }
        }
        t_recording.in_hook = false;
    }
    if (t_fault.countdown > 0) {
        --t_fault.countdown;
        if (t_fault.countdown == 0) {
            if (belongs_to_a_vendored_library()) {
                t_fault.countdown = 1; // the next allocation that is this project's
            } else {
                *t_fault.fired = true;
                throw std::bad_alloc{};
            }
        }
    }
    // A zero-sized request still answers with a distinct address.
    auto* block = std::malloc(size != 0 ? size : 1); // NOLINT(cppcoreguidelines-no-malloc)
    if (block == nullptr) {
        throw std::bad_alloc{};
    }
    g_live_blocks.fetch_add(1, std::memory_order_relaxed);
    g_allocations.fetch_add(1, std::memory_order_relaxed);
    return block;
}

void operator delete(void* block) noexcept {
    if (block != nullptr) {
        g_live_blocks.fetch_sub(1, std::memory_order_relaxed);
    }
    std::free(block); // NOLINT(cppcoreguidelines-no-malloc)
}

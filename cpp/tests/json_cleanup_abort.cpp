// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shows why the allocation-fault sweeps (alloc_fault.cpp) leave the JSON
// library's own allocations alone: the library destroys a document by
// flattening it onto a vector it allocates, from a destructor, which is
// noexcept, so an allocation failing there ends the program through
// std::terminate instead of unwinding. tools/check_json_cleanup_abort.py
// builds and runs it when the library's release moves.
//
// It fails each allocation of a parse in turn, sparing the library's own the
// way the sweeps do, and must reach the end; then fails each in turn sparing
// none, and must end in std::terminate, whose handler is the one way it exits
// 0. It replaces the allocation functions with a bump arena it never frees,
// since the two sweeps allocate a few kilobytes in all.
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <dlfcn.h>
#include <exception>
#include <execinfo.h>
#include <iterator>
#include <memory>
#include <new>
#include <ranges>
#include <string_view>

#include <nlohmann/json.hpp>

namespace {

enum class Sweep : std::uint8_t { Settling, Sparing, Failing };

// The allocation the current sweep fails, counted down, and which sweep runs.
// Trivial and constant-initialised, so the allocation function reads it without
// allocating or running a guard.
struct Fault {
    std::int64_t countdown = 0;
    Sweep sweep = Sweep::Settling;
};

constexpr std::size_t k_arena_bytes = std::size_t{1} << 22U;

// The library is known by a frame of its own among the few above the
// allocation, as the sweeps know it: what it allocates it allocates through
// the standard library's functions, whose frames name no owner.
constexpr std::size_t k_stack_depth = 8;

// A document of the shape the decoders read, nested, so its destruction
// flattens it onto the library's own vector.
constexpr std::string_view k_document =
    R"({"messages":[{"name":"a name long enough to be on the heap","signals":[1,2,3]}]})";

// More allocations than one parse of the document makes.
constexpr std::int64_t k_most_allocations = 4000;

} // namespace

static auto fault() -> Fault& {
    static Fault state;
    return state;
}

static auto take_block(std::size_t size) -> void* {
    alignas(std::max_align_t) static std::array<std::byte, k_arena_bytes> arena{};
    static std::size_t used = 0;
    constexpr auto k_alignment = alignof(std::max_align_t);
    auto const start = (used + k_alignment - 1) / k_alignment * k_alignment;
    auto const end = start + std::max(size, std::size_t{1});
    if (end > arena.size()) {
        throw std::bad_alloc{};
    }
    used = end;
    return std::to_address(std::next(arena.begin(), static_cast<std::ptrdiff_t>(start)));
}

static auto library_frame_on_stack() -> bool {
    std::array<void*, k_stack_depth> frames{};
    auto const depth = backtrace(frames.data(), static_cast<int>(frames.size()));
    return std::ranges::any_of(frames | std::views::take(depth), [](void* const frame) {
        Dl_info info{};
        return dladdr(frame, &info) != 0 && info.dli_sname != nullptr &&
               std::string_view{info.dli_sname}.contains("nlohmann");
    });
}

static void say(std::string_view const line) {
    static_cast<void>(std::fwrite(line.data(), 1, line.size(), stderr));
}

[[noreturn]] static void on_terminate() {
    auto& state = fault();
    state.countdown = 0;
    if (state.sweep == Sweep::Failing) {
        say("a failed allocation in a document's destruction ended the program\n");
        std::_Exit(EXIT_SUCCESS);
    }
    say("the program ended while the library's own allocations were spared\n");
    std::_Exit(EXIT_FAILURE);
}

// Fails the nth allocation of a parse of the document, for every n until a
// parse fails none, having made fewer than n or had every one spared; false if
// the bound came first.
static auto sweep_allocations(Sweep const sweep) -> bool {
    auto& state = fault();
    state.sweep = sweep;
    for (auto const nth : std::views::iota(std::int64_t{1}, k_most_allocations)) {
        state.countdown = nth;
        auto failed = false;
        try {
            auto const document = nlohmann::json::parse(k_document);
            static_cast<void>(document.size());
        } catch (std::bad_alloc const&) {
            failed = true;
        }
        state.countdown = 0;
        if (!failed) {
            return true;
        }
    }
    return false;
}

auto operator new(std::size_t size) -> void* {
    auto& state = fault();
    if (state.countdown > 0) {
        --state.countdown;
        if (state.countdown == 0) {
            if (state.sweep == Sweep::Sparing && library_frame_on_stack()) {
                state.countdown = 1;
            } else {
                throw std::bad_alloc{};
            }
        }
    }
    return take_block(size);
}

void operator delete(void* /*block*/) noexcept {
}

auto main() -> int {
    try {
        std::set_terminate(on_terminate);
        {
            auto const settled = nlohmann::json::parse(k_document);
            static_cast<void>(settled.size());
        }
        if (!sweep_allocations(Sweep::Sparing)) {
            say("sparing the library, a parse never ran out of allocations to fail\n");
            return EXIT_FAILURE;
        }
        static_cast<void>(sweep_allocations(Sweep::Failing));
        say("every failed allocation unwound, so the library's own need no sparing\n");
        return EXIT_FAILURE;
    } catch (std::exception const& error) {
        say("the program could not run its sweeps: ");
        say(error.what());
        say("\n");
        return 2;
    }
}

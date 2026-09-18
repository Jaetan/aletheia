#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/alloc_fault.cpp.
# Claim: the allocation-fault harness leaves the JSON library's own
# allocations alone because it must. That library destroys a document by
# flattening it onto a heap-allocated stack, from a destructor, which is
# noexcept: an allocation that fails there ends the program instead of
# unwinding, and no cleanup a test wants to reach is behind it. Shown with a
# program of its own, which replaces the allocation functions the way the
# harness does, and fails one allocation of a document's destruction: it dies
# on SIGABRT. Sparing the library's own sites, the same program runs to the
# end. Non-zero exit: the failure unwinds, so the harness is sparing sites it
# no longer needs to. Exits 0 with a note when the toolchain or the JSON
# headers are not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
json_include=cpp/build/_deps/json-src/include
[ -d "$json_include" ] || { echo "no JSON headers in the build tree, claim untestable"; exit 0; }
scratch=cpp/build/probe-scratch/json-cleanup
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
// Fails the nth allocation this thread makes, optionally sparing the ones the
// JSON library asks for, then parses a document and destroys it.
#include <cstddef>
#include <cstdlib>
#include <cstdio>
#include <dlfcn.h>
#include <new>
#include <string_view>
#include <nlohmann/json.hpp>

namespace {
struct Fault {
    long long countdown = 0;
    bool spare_the_library = false;
};
} // namespace
static thread_local Fault t_fault;

static auto belongs_to_the_json_library(const void* site) -> bool {
    Dl_info info{};
    if (dladdr(const_cast<void*>(site), &info) == 0 || info.dli_sname == nullptr)
        return false;
    return std::string_view{info.dli_sname}.contains("nlohmann");
}

auto operator new(std::size_t size) -> void* {
    if (t_fault.countdown > 0) {
        --t_fault.countdown;
        if (t_fault.countdown == 0) {
            if (t_fault.spare_the_library && belongs_to_the_json_library(__builtin_return_address(0)))
                t_fault.countdown = 1;
            else
                throw std::bad_alloc{};
        }
    }
    void* block = std::malloc(size != 0 ? size : 1);
    if (block == nullptr)
        throw std::bad_alloc{};
    return block;
}

void operator delete(void* block) noexcept { std::free(block); }

// A document with a nested array and object, which is what the decoders read
// and what the library flattens through a heap-allocated stack.
constexpr std::string_view k_document =
    R"({"messages":[{"name":"a name long enough to be on the heap","signals":[1,2,3]}]})";

auto main(int argc, char** argv) -> int {
    t_fault.spare_the_library = std::string_view{argv[1]} == "spare";
    // Settle whatever parsing reaches for once, so the sweep below covers the
    // document's own allocations rather than one-time state.
    { auto settle = nlohmann::json::parse(k_document); static_cast<void>(settle.size()); }
    for (long long nth = 1; nth <= 4000; ++nth) {
        t_fault.countdown = nth;
        bool reached = true;
        try {
            auto doc = nlohmann::json::parse(k_document);
            static_cast<void>(doc.size());
        } catch (...) {
        }
        reached = t_fault.countdown == 0;
        t_fault.countdown = 0;
        if (!reached) {
            std::printf("%lld\n", nth - 1);
            return 0;
        }
    }
    return 1;
}
CPP
clang++-23 -std=c++23 -O0 -rdynamic -I "$json_include" "$scratch/t.cpp" -o "$scratch/t" > "$scratch/compile.log" 2>&1 \
    || { tail -5 "$scratch/compile.log"; exit 1; }
# A shell reports the abort of a child it waits for on its own stderr, so the
# run is handed to one whose stderr is the file, and the exit code read back
# is the same 128 plus the signal.
sh -c '"$0" fail' "$scratch/t" > "$scratch/fail.txt" 2>&1
failing=$?
"$scratch/t" spare > "$scratch/spare.txt" 2>&1
sparing=$?
# 134 is the shell's report of a process killed by SIGABRT, which is how an
# exception leaving a noexcept destructor ends a program.
if [ "$failing" -ne 134 ]; then
    echo "failing the library's own allocation exited $failing, not on SIGABRT"
    exit 1
fi
if [ "$sparing" -ne 0 ]; then
    echo "sparing the library still ended the run: exit $sparing, $(cat "$scratch/spare.txt")"
    exit 1
fi
echo "the document cleanup aborts on a failed allocation; sparing it covers $(cat "$scratch/spare.txt") of its own"

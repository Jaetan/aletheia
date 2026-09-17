#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/ffi_backend.cpp.
# Claim: a construction the backend refuses loads no library. An empty path
# is refused as a Validation error rather than handed to dlopen (which opens
# the calling program and fails later at the first symbol), and a core count
# below one is refused before the kernel is mapped, so the process's mappings
# stay free of libaletheia-ffi.so. Non-zero exit: either refusal carries the
# wrong kind, or the kernel is mapped after a refused construction. Exits 2
# when the archive or the kernel is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
kernel=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] && [ -f "$kernel" ] || exit 2
scratch=cpp/build/probe-scratch/ffi-refusal
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>
#include <cstdio>
#include <fstream>
#include <string>
using namespace aletheia;
static auto kernel_is_mapped() -> bool {
    std::ifstream maps("/proc/self/maps");
    for (std::string line; std::getline(maps, line);)
        if (line.find("libaletheia-ffi.so") != std::string::npos)
            return true;
    return false;
}
template <typename F> static auto refusal_kind(F make) -> int {
    try { auto b = make(); } catch (const AletheiaException& e) { return static_cast<int>(e.kind()); }
    catch (...) { return -2; }
    return -1; // constructed, which is itself a failure here
}
int main(int, char** argv) {
    int failures = 0;
    const auto want = static_cast<int>(ErrorKind::Validation);
    const int empty_path = refusal_kind([] { return make_ffi_backend(""); });
    if (empty_path != want) { std::printf("empty path refused with kind %d, want %d\n", empty_path, want); ++failures; }
    const int bad_cores = refusal_kind([&] { return make_ffi_backend(argv[1], 0); });
    if (bad_cores != want) { std::printf("cores 0 refused with kind %d, want %d\n", bad_cores, want); ++failures; }
    if (kernel_is_mapped()) { std::printf("the kernel is mapped after two refused constructions\n"); ++failures; }
    std::printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-23 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
env -u ALETHEIA_LIB "$scratch/t" "$kernel"

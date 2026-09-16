#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/detail/rational_renderer.hpp.
# Claim: the renderer loads the first existing candidate in the order
# ALETHEIA_LIB, the path registered by make_ffi_backend, then the relative
# heuristic. Shown two ways with a backend already up: ALETHEIA_LIB naming an
# existing file that is not the kernel makes the renderer fail with an Ffi
# error even though a valid path is registered (the variable wins when it
# exists); ALETHEIA_LIB naming a path that does not exist is skipped and the
# registered kernel renders (a wrong variable falls through). Non-zero exit:
# either run behaves otherwise. Exits 2 when the archive or kernel is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
kernel=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] && [ -f "$kernel" ] || exit 2
scratch=cpp/build/probe-scratch/renderer-order
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/backend.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <cstdio>
#include <cstdlib>
int main(int, char** argv) {
    auto backend = aletheia::make_ffi_backend(argv[1]); // registers argv[1], brings the RTS up
    try {
        auto s = aletheia::detail::format_rational_ffi(1, 2);
        std::printf("%s\n", s.c_str());
        return 0;
    } catch (const aletheia::AletheiaException& e) {
        return e.kind() == aletheia::ErrorKind::Ffi ? 3 : 4;
    }
}
CPP
clang++-22 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
ALETHEIA_LIB=/dev/null "$scratch/t" "$kernel" > /dev/null 2>&1; existing_wrong=$?
ALETHEIA_LIB=/nonexistent/libaletheia-ffi.so "$scratch/t" "$kernel" > "$scratch/out.txt" 2>&1; missing=$?
[ "$existing_wrong" -eq 3 ] && [ "$missing" -eq 0 ] && grep -q '^0\.5$\|^1/2$' "$scratch/out.txt" || { echo "existing-wrong=$existing_wrong missing=$missing out=$(cat "$scratch/out.txt")"; exit 1; }

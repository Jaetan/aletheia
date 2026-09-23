#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/stability_bench.cpp.
# Claim: the harness has teeth on its hard-zero file-descriptor gate: a
# variant of the same source that leaks one descriptor per cycle fails with
# fd_count marked not passed, while the unmodified harness passes the same
# short run. Both variants are compiled here from the tracked source against
# the built binding, with the harness's own directory on the include path,
# because the harness includes the shared timed-loop header by a quoted name
# that the build resolves from the source directory and the scratch copy
# cannot. Non-zero exit: the leaking variant passes, or the clean one fails.
# Exits 2 when cpp/build or the kernel is not built.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
[ -f "$lib" ] && [ -f build/libaletheia-ffi.so ] || exit 2
scratch=cpp/build/probe-scratch/stability-teeth
mkdir -p "$scratch" || exit 2
src=cpp/benchmarks/stability_bench.cpp
sed -e 's|^#include <malloc.h>|#include <malloc.h>\n#include <fcntl.h>|' \
    -e 's|^    require(client.end_stream(std::stop_token{}), "end_stream");|    require(client.end_stream(std::stop_token{}), "end_stream");\n    (void)open("/dev/null", O_RDONLY); // injected leak|' \
    "$src" > "$scratch/leaky.cpp"
grep -q 'injected leak' "$scratch/leaky.cpp" || { echo "injection point not found"; exit 1; }
link="$lib $rpath -ldl -lpthread"
clang++-23 -std=c++23 -O2 -DNDEBUG -Icpp/include -Icpp/benchmarks "$scratch/leaky.cpp" $link -o "$scratch/leaky" > "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
clang++-23 -std=c++23 -O2 -DNDEBUG -Icpp/include -Icpp/benchmarks "$src" $link -o "$scratch/clean" >> "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
export ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so ALETHEIA_STABILITY_CYCLES=2 ALETHEIA_STABILITY_FRAMES=500
"$scratch/clean" > "$scratch/clean.json" 2>/dev/null || { echo "clean harness failed"; exit 1; }
if "$scratch/leaky" > "$scratch/leaky.json" 2>/dev/null; then echo "leaking harness passed"; exit 1; fi
grep -A6 '"name": "fd_count"' "$scratch/leaky.json" | grep -q '"passed": false'

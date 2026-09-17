#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/excel.cpp.
# Claim: a failure that is not a property of a cell keeps its kind. Loading a
# workbook with numeric cells before any backend exists makes the kernel
# decimal parser refuse (the runtime is down), and the loader must return an
# Ffi-kinded error, not a Validation one, while a genuinely malformed cell
# still returns Validation. Non-zero exit: either kind is wrong, or a load
# throws instead of returning. Exits 2 when the archive or the fixture is
# missing.
set -u
cd "$(dirname "$0")/.." || exit 2
lib=cpp/build/libaletheia-cpp.so
# The library is shared and carries its own dependencies, so a scratch binary
# links it alone; -Wl,-rpath gives the loader the directory the linker already has.
rpath="-Wl,-rpath,$(cd cpp/build && pwd)"
fixture=examples/demo/demo_workbook.xlsx
[ -f "$lib" ] && [ -f "$fixture" ] || exit 2
scratch=cpp/build/probe-scratch/excel-kind
mkdir -p "$scratch" || exit 2
cat > "$scratch/t.cpp" <<'CPP'
#include <aletheia/excel.hpp>
#include <cstdio>
using namespace aletheia;
int main(int, char** argv) {
    int failures = 0;
    // No backend exists in this process, so the kernel decimal parser is down.
    auto checks = load_checks_from_excel(argv[1]);
    if (checks) { std::printf("expected a refusal with the runtime down\n"); return 1; }
    if (checks.error().kind() != ErrorKind::Ffi) {
        std::printf("kind was %d, expected Ffi\n", static_cast<int>(checks.error().kind()));
        ++failures;
    }
    // A path that does not exist is the loader's own refusal, still Validation.
    auto missing = load_checks_from_excel("does-not-exist.xlsx");
    if (missing || missing.error().kind() != ErrorKind::Validation) ++failures;
    std::printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
CPP
clang++-23 -std=c++23 -Icpp/include "$scratch/t.cpp" "$lib" $rpath -ldl -lpthread -o "$scratch/t" > "$scratch/compile.log" 2>&1 || { tail -5 "$scratch/compile.log"; exit 1; }
env -u ALETHEIA_LIB "$scratch/t" "$fixture"

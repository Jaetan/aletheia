#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/measure.hpp and cpp/tests/unit_tests_benchmark_measure.cpp.
# Claim: an operation that fails inside a timed loop leaves the loop as an
# exception, so the lane aborts with the operation's error instead of timing
# the failure as a success, and the test that guards it dies when the check
# is taken out. The check is replaced by a discard of the operation's result,
# the unit tests rebuilt and the benchmark cases run, which must fail; the
# header is restored and rebuilt by the same step, whichever way it went. No
# real kernel can be made to fail mid-loop from outside, which is why the test
# drives the loops with a clock and an operation of its own and this probe
# proves the test is not vacuous.
# Non-zero exit: the benchmark cases pass with the check gone, or they do not
# pass with it in place. Exits 2 when cpp/build is not configured or a build
# fails.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
header=cpp/benchmarks/measure.hpp
tests=cpp/build/unit_tests

build() { cmake --build cpp/build --target unit_tests > /dev/null 2>&1; }
original=$(cat "$header") || exit 2
restore() { printf '%s\n' "$original" > "$header" && build; }
trap restore EXIT

build || exit 2
"$tests" "[benchmark]" > /dev/null 2>&1 || { echo "the benchmark cases fail before the mutation"; exit 1; }

# The three loops, the throughput one and the latency warmup and measured
# ones, check through the same line; a discard in any one is the defect, so
# all three are mutated and one surviving test is a pass.
grep -c 'require(op(.*), step);' "$header" | grep -qx 3 || {
    echo "the check is not written where this probe mutates it"
    exit 1
}
sed -i 's/require(op(\(.*\)), step);/std::ignore = op(\1);/' "$header"
sed -i 's/#include <vector>/#include <tuple>\n#include <vector>/' "$header"
build || { echo "the mutated header does not build"; exit 2; }
if "$tests" "[benchmark]" > /dev/null 2>&1; then
    echo "the benchmark cases pass with the check discarded"
    exit 1
fi
exit 0

#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/benchmark.cpp.
# Claim: --frames, --runs, --warmup and --ops accept only a non-negative whole
# number and refuse anything else with a message and a non-zero exit, instead
# of reading it as zero and benchmarking nothing. Builds the benchmark target
# first so a stale binary is never measured. Non-zero exit: a bad value was
# accepted, a good value was refused, or a refused value ran instead. Exits 2
# when cpp/build is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
cmake --build cpp/build --target benchmark > /dev/null 2>&1 || exit 2
bench=cpp/build/benchmark

# Every invocation is bounded, because what this probe looks for does not
# always show as an exit. The harness runs its fixed counts over
# std::views::repeat, whose bound is a precondition rather than a condition:
# measured, a negative one iterates without end, where the counting loop it
# replaced ran zero times. Unbounded, the probe would hang on exactly the
# regression it exists to report, and a timeout read as a non-zero exit would
# report that hang as the refusal working.
refuses() { # refuses <what> <argv...>: the run must exit non-zero, and end
    what=$1
    shift
    timeout 30 "$bench" "$@" > /dev/null 2>&1
    case $? in
        0) echo "accepted $what" && exit 1 ;;
        124) echo "ran without end on $what" && exit 1 ;;
    esac
}
accepts() { # accepts <what> <argv...>: the run must exit zero, and end
    what=$1
    shift
    timeout 60 "$bench" "$@" > /dev/null 2>&1 || { echo "refused $what" && exit 1; }
}

for bad in abc -1 12x 1.5 ""; do
    refuses "--frames '$bad'" throughput --frames "$bad" --runs 1 --warmup 0
done
# A word and a negative are refused on every one of the four, not only on the
# option the loop above carries.
for opt in --frames --runs --warmup --ops; do
    refuses "$opt abc" latency "$opt" abc
    refuses "$opt -1" latency "$opt" -1
done

accepts "zero counts" throughput --frames 0 --runs 0 --warmup 0
"$bench" throughput --frames abc --runs 1 2>&1 | grep -q 'whole number'

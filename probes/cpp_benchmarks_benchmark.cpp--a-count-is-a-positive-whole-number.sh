#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/benchmark.cpp.
# Claim: --frames, --runs and --ops accept only a positive whole number, and
# --warmup only a non-negative one; a word, a sign, trailing characters, a
# negative and, for the first three, a zero are each refused with a message
# naming the option and a non-zero exit, before anything is measured. A lane
# measured over nothing publishes a rate of zero with every other field
# filled in, which is conformant with benchmarks/SCHEMA.yaml and reads as a
# slow binding rather than as a failure; benchmarks/run_all.sh refuses the
# same counts of its own, and this is the refusal in the binary, which the
# schema gate and a person at a terminal run directly. Builds the benchmark
# target first so a stale binary is never measured.
# Non-zero exit: a bad value was accepted, a good value was refused, a refusal
# came without its message, or a refused value ran instead. Exits 2 when
# cpp/build is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
cmake --build cpp/build --target benchmark > /dev/null 2>&1 || exit 2
bench=cpp/build/benchmark
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

# Every invocation is bounded, because what this probe looks for does not
# always show as an exit. The harness runs its fixed counts over
# std::views::repeat, whose bound is a precondition rather than a condition:
# measured, a negative one iterates without end, where the counting loop it
# replaced ran zero times. Unbounded, the probe would hang on exactly the
# regression it exists to report, and a timeout read as a non-zero exit would
# report that hang as the refusal working.
status=0
refuses() { # refuses <message> <argv...>: exits non-zero, ends, and says why
    message=$1
    shift
    timeout 30 "$bench" "$@" > /dev/null 2> "$work/stderr"
    case $? in
        0) echo "accepted: $*" && status=1 ;;
        124) echo "ran without end: $*" && status=1 ;;
    esac
    grep -q -- "$message" "$work/stderr" || {
        echo "refused without '$message': $*"
        head -1 "$work/stderr" | sed 's/^/    /'
        status=1
    }
}
accepts() { # accepts <argv...>: exits zero, and ends
    timeout 60 "$bench" "$@" > /dev/null 2>&1 || { echo "refused: $*" && status=1; }
}

for bad in abc -1 12x 1.5 ""; do
    refuses "whole number" throughput --frames "$bad" --runs 1 --warmup 0
done
# A word and a negative are refused on every one of the four, not only on the
# option the loop above carries.
for opt in --frames --runs --warmup --ops; do
    refuses "$opt expects" latency "$opt" abc
    refuses "$opt expects" latency "$opt" -1
done
# A zero is refused wherever it would measure nothing, whichever mode runs.
refuses "--frames must be at least 1" throughput --frames 0 --runs 1 --warmup 0
refuses "--runs must be at least 1" throughput --frames 100 --runs 0 --warmup 0
refuses "--ops must be at least 1" latency --ops 0 --warmup 0
refuses "--runs must be at least 1" scaling --quick --runs 0
# A zero warmup is a measurement with no warmup.
accepts throughput --frames 100 --runs 1 --warmup 0
accepts latency --ops 50 --warmup 0

exit "$status"

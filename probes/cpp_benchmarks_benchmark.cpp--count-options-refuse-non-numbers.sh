#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/benchmark.cpp.
# Claim: --frames, --runs, --warmup and --ops accept only a non-negative whole
# number and refuse anything else with a message and a non-zero exit, instead
# of reading it as zero and benchmarking nothing. Builds the benchmark target
# first so a stale binary is never measured. Non-zero exit: a bad value was
# accepted, or a good value was refused. Exits 2 when cpp/build is not
# configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
cmake --build cpp/build --target benchmark > /dev/null 2>&1 || exit 2
bench=cpp/build/benchmark
for bad in abc -1 12x 1.5 ""; do
    if "$bench" throughput --frames "$bad" --runs 1 --warmup 0 > /dev/null 2>&1; then
        echo "accepted --frames '$bad'"; exit 1
    fi
done
for opt in --runs --warmup --ops; do
    if "$bench" latency $opt abc > /dev/null 2>&1; then echo "accepted $opt abc"; exit 1; fi
done
"$bench" throughput --frames 0 --runs 0 --warmup 0 > /dev/null 2>&1 || { echo "refused zero counts"; exit 1; }
"$bench" throughput --frames abc --runs 1 2>&1 | grep -q 'whole number'

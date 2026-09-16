#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: when the C++ tree is configured, or go or cargo is on PATH, and the
# build fails, the lane is reported as FAIL and the run exits non-zero,
# instead of the lane being skipped as if the toolchain were missing. Runs the
# harness at one frame into a scratch results directory with a cmake, a go and
# a cargo that refuse to build. Non-zero exit: a broken build was skipped, or
# the run exited zero. Exits 2 when the kernel library, the venv or cpp/build
# is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
[ -f python/.venv/bin/activate ] || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
mkdir -p "$dir/bin"
printf '#!/bin/sh\necho "probe: build refused" >&2\nexit 1\n' > "$dir/bin/go"
cp "$dir/bin/go" "$dir/bin/cargo"
cp "$dir/bin/go" "$dir/bin/cmake"
chmod +x "$dir/bin/go" "$dir/bin/cargo" "$dir/bin/cmake"
out=$(PATH="$dir/bin:$PATH" ALETHEIA_BENCH_RESULTS_DIR="$dir/results" \
    bash benchmarks/run_all.sh --frames 1 --runs 1 --bench throughput 2>&1)
rc=$?
status=0
[ "$rc" -ne 0 ] || { echo "the run exited zero with three broken builds"; status=1; }
for lane in C++ Go Rust; do
    grep -q "FAIL: $lane benchmark failed to build" <<< "$out" || { echo "$lane broken build not reported as FAIL"; status=1; }
    grep -q "SKIP: $lane" <<< "$out" && { echo "$lane broken build reported as SKIP"; status=1; }
done
grep -q "Failed benchmarks: C++ Go Rust" <<< "$out" || { echo "the summary does not name all three lanes"; status=1; }
[ -f "$dir/results/cpp_throughput.json" ] && { echo "a failed C++ lane wrote a result"; status=1; }
[ -f "$dir/results/go_throughput.json" ] && { echo "a failed Go lane wrote a result"; status=1; }
[ -f "$dir/results/rust_throughput.json" ] && { echo "a failed Rust lane wrote a result"; status=1; }
exit $status

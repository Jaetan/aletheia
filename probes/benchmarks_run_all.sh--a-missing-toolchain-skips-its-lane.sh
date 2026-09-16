#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: when go or cargo is not on PATH at all, its lane is a SKIP and the
# run still exits zero with the lanes that could run. Runs the harness at one
# frame into a scratch results directory under a PATH holding only the tools
# the script and the C++ build need, with no go and no cargo. Non-zero exit:
# a missing toolchain was reported as a failure, or the run exited non-zero.
# Exits 2 when the kernel library, the venv, cpp/build or a needed tool is
# missing.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f build/libaletheia-ffi.so ] || exit 2
[ -f python/.venv/bin/activate ] || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
mkdir -p "$dir/bin"
for tool in bash sh python3 sed awk mktemp mv rm mkdir dirname basename cat \
            cmake ninja make env uname ls cp grep sort head tail tr; do
    src=$(command -v "$tool") || { echo "needed tool not found: $tool"; exit 2; }
    ln -s "$src" "$dir/bin/$tool"
done
out=$(PATH="$dir/bin" ALETHEIA_BENCH_RESULTS_DIR="$dir/results" \
    bash benchmarks/run_all.sh --frames 1 --runs 1 --bench throughput 2>&1)
rc=$?
status=0
[ "$rc" -eq 0 ] || { echo "the run exited $rc with the toolchains absent"; status=1; }
for lane in Go Rust; do
    grep -q "SKIP: $lane benchmark not built" <<< "$out" || { echo "$lane absent toolchain not reported as SKIP"; status=1; }
    grep -q "FAIL: $lane" <<< "$out" && { echo "$lane absent toolchain reported as FAIL"; status=1; }
done
[ -f "$dir/results/python_throughput.json" ] || { echo "the Python lane did not run"; status=1; }
[ -f "$dir/results/cpp_throughput.json" ] || { echo "the C++ lane did not run"; status=1; }
exit $status

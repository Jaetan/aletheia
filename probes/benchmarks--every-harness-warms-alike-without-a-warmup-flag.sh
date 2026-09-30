#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the four benchmark harnesses: python/benchmarks/throughput.py and
# latency.py, cpp/benchmarks/benchmark.cpp, go/benchmarks/main.go and
# rust/examples/benchmark.rs.
# Claim: run without --warmup, the four warm a mode alike, as the warmup each
# report records in its parameters object says: one count of untimed passes
# for throughput and one count of untimed operations for latency, the same in
# every binding. benchmarks/run_all.sh passes the latency warmup, so a harness
# whose own default differed would measure differently only when run by hand.
# The compiled harnesses are built, never found.
# Non-zero exit: two harnesses record different warmups for one mode. Exits 2
# without a toolchain, the built kernel or a configured cpp/build.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v go > /dev/null || exit 2
command -v cargo > /dev/null || exit 2
lib=$PWD/build/libaletheia-ffi.so
[ -f "$lib" ] || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && go build -o "$work/go" ./benchmarks) > /dev/null 2>&1 || exit 2
cargo build --release --example benchmark --manifest-path rust/Cargo.toml > /dev/null 2>&1 || exit 2
cmake --build cpp/build --target benchmark > /dev/null 2>&1 || exit 2

export ALETHEIA_LIB=$lib LD_LIBRARY_PATH=$PWD/build
run() { # binding mode -- the harness's JSON report for that mode, no --warmup given
    case $1 in
        python) (cd python && ".venv/bin/python" -m "benchmarks.$2" "${@:3}" --json) ;;
        go) "$work/go" "$2" "${@:3}" --json ;;
        rust) rust/target/release/examples/benchmark "$2" "${@:3}" --json ;;
        cpp) cpp/build/benchmark "$2" "${@:3}" --json ;;
    esac
}
for b in python cpp go rust; do
    run "$b" throughput --frames 10 --runs 1 > "$work/$b-throughput.json" 2> /dev/null || exit 1
    run "$b" latency --ops 10 > "$work/$b-latency.json" 2> /dev/null || exit 1
done

"$py" - "$work" <<'PY'
import json
import sys

work = sys.argv[1]
bad = []
for mode in ("throughput", "latency"):
    warmups = {
        b: json.load(open(f"{work}/{b}-{mode}.json", encoding="utf-8"))["parameters"]["warmup"]
        for b in ("python", "cpp", "go", "rust")
    }
    if len(set(warmups.values())) != 1:
        bad.append(f"{mode} warms differently: {warmups}")
    else:
        print(f"{mode}: every harness warms {next(iter(warmups.values()))}")
if bad:
    print("run without --warmup, the harnesses do not warm alike:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: run without --warmup, the four harnesses warm each mode alike")
PY

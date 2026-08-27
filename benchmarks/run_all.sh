#!/bin/bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
# Cross-Language Benchmark Runner
#
# Builds the C++/Go/Rust benchmark binaries and runs the selected benchmark
# (--bench throughput|latency|scaling) for Python, C++, Go and Rust.  The Python
# binding is interpreted and runs from the venv, so nothing is built for it.
# Results are saved as JSON in benchmarks/results/.
#
# Usage:
#     ./benchmarks/run_all.sh [--frames N] [--runs N] [--bench throughput|latency|scaling]
#
# Prerequisites:
#     - libaletheia-ffi.so built (cabal run shake -- build)
#     - Python venv activated with aletheia installed
#     - C++ tree configured (cd cpp && cmake -B build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22)
#     - Go (go) and Rust (cargo) toolchains on PATH
#
# The C++, Go, and Rust benchmark binaries are BUILT by this script, never
# consumed pre-built: a stale binary measures a wire format the current kernel
# may no longer speak, and its numbers are void rather than merely old.  Each
# build is incremental; a missing toolchain is a graceful per-lane SKIP.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"

# Defaults
FRAMES=10000
RUNS=5
BENCH=throughput

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --frames) FRAMES="$2"; shift 2 ;;
        --runs)   RUNS="$2";   shift 2 ;;
        --bench)  BENCH="$2";  shift 2 ;;
        *)        echo "Unknown arg: $1" >&2; exit 1 ;;
    esac
done

# Validate the mode before anything derives a path from it.  BENCH feeds a
# destructive glob below, and an unchecked value is a data-loss hazard, not just a
# usage error: `--bench throughput_baseline` would expand to
# results/*_throughput_baseline.json and delete the committed baselines.
case "$BENCH" in
    throughput|latency|scaling) ;;
    *) echo "ERROR: unknown --bench '$BENCH' (expected throughput, latency or scaling)" >&2; exit 1 ;;
esac

mkdir -p "$RESULTS_DIR"

export ALETHEIA_LIB="$PROJECT_DIR/build/libaletheia-ffi.so"

if [[ ! -f "$ALETHEIA_LIB" ]]; then
    echo "ERROR: $ALETHEIA_LIB not found. Run: cabal run shake -- build" >&2
    exit 1
fi

# Refuse to run a Debug-mode C++ tree — an -O0 benchmark silently looks like a
# 20%+ regression.  CMakeLists.txt defaults to Release when the cache is empty,
# but an explicit -DCMAKE_BUILD_TYPE=Debug from a prior session persists in it.
# This is a PREFLIGHT: it only reads the cache, and it aborts — so it must run
# before the destructive clear below, or a Debug tree would delete the previous
# run's results and exit without producing replacements.
CPP_CACHE="$PROJECT_DIR/cpp/build/CMakeCache.txt"
if [[ -f "$CPP_CACHE" ]]; then
    CPP_BUILD_TYPE="$(awk -F= '/^CMAKE_BUILD_TYPE:/{print $2}' "$CPP_CACHE")"
    if [[ "$CPP_BUILD_TYPE" == "Debug" ]]; then
        echo "ERROR: cpp/build is configured with CMAKE_BUILD_TYPE=Debug." >&2
        echo "       Debug builds produce unoptimized benchmarks." >&2
        echo "       Reconfigure with:" >&2
        echo "         rm -rf cpp/build && cmake -S cpp -B cpp/build -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 && cmake --build cpp/build" >&2
        exit 1
    fi
fi

# Clear this mode's results, AFTER the preflight checks above: an abort must not
# destroy the previous run's results without producing replacements.  A lane that
# SKIPs (missing toolchain) or FAILs writes no file, so without this its PREVIOUS
# run's JSON survives and the comparison below — which globs the directory —
# would present a stale measurement as current under a banner that excludes it.
# The committed `*_baseline.json` are a different artifact and are never matched by
# this glob (BENCH is enum-checked above).
rm -f "$RESULTS_DIR"/*_"${BENCH}".json

echo "=== Aletheia Cross-Language Benchmark ==="
echo "Benchmark: $BENCH"
echo "Frames:    $FRAMES"
echo "Runs:      $RUNS"
echo "Library:   $ALETHEIA_LIB"
echo ""

# run_benchmark LANG OUTFILE COMMAND...
#
# Runs a benchmark command, captures stdout to a temp file, validates the JSON,
# then atomically moves it to the final output path.  A non-JSON PREAMBLE on
# stdout (e.g. GHC RTS warnings, cgo diagnostics) is dropped; trailing output is
# not, and fails the validation rather than being silently trimmed (see the
# extraction note in the body).
run_benchmark() {
    local lang="$1"
    local outfile="$2"
    shift 2
    local cmd=("$@")

    local tmpfile errfile
    tmpfile="$(mktemp "$RESULTS_DIR/.tmp.${lang}.XXXXXX")"
    errfile="$(mktemp "$RESULTS_DIR/.err.${lang}.XXXXXX")"
    trap "rm -f '$tmpfile' '$errfile'" RETURN

    echo ">>> Running $lang $BENCH benchmark..."

    # Run benchmark. stdout → tmpfile (the JSON payload), stderr → errfile (the
    # human-readable progress, which carries the per-run error lines).  stderr is
    # CAPTURED and replayed on failure, never discarded: it is the only place a
    # per-run error appears, so discarding it makes a dead lane look like an
    # absent one.
    # Some runtimes (GHC RTS, cgo) print warnings to stdout, so the JSON is taken
    # from the first '{' to END OF FILE — a non-JSON PREAMBLE is dropped, trailing
    # output is NOT.  Trailing junk therefore fails the parse below rather than
    # being silently trimmed, and that branch replays the captured stderr.
    if ! "${cmd[@]}" > "$tmpfile" 2>"$errfile"; then
        echo "    FAIL: $lang benchmark exited with error" >&2
        sed 's/^/      | /' "$errfile" >&2
        rm -f "$tmpfile"
        return 1
    fi

    # Extract JSON: find first '{' through end of file, validate with python.
    # This strips any non-JSON preamble (RTS warnings, cgo messages).
    local json_out
    json_out="$(mktemp "$RESULTS_DIR/.json.${lang}.XXXXXX")"

    if ! sed -n '/^{/,$ p' "$tmpfile" | python3 -c "
import sys, json
try:
    data = json.load(sys.stdin)
    json.dump(data, sys.stdout, indent=2)
except (json.JSONDecodeError, ValueError) as e:
    print(f'Invalid JSON: {e}', file=sys.stderr)
    sys.exit(1)
" > "$json_out"; then
        echo "    FAIL: $lang benchmark produced invalid JSON" >&2
        # Replay stderr here too: a benchmark that prints its per-run errors and
        # then exits 0 with a truncated payload lands in THIS branch, and its
        # stderr is the whole diagnosis.
        sed 's/^/      | /' "$errfile" >&2
        sed 's/^/      > /' "$tmpfile" >&2
        rm -f "$tmpfile" "$json_out"
        return 1
    fi

    # Atomic move to final location
    mv "$json_out" "$outfile"
    rm -f "$tmpfile"
    echo "    Saved: $(basename "$outfile")"
    return 0
}

SUCCEEDED=()
FAILED=()

# --- Python ---
PYTHON_ARGS=(--json)
case $BENCH in
    throughput) PYTHON_ARGS=(--frames "$FRAMES" --runs "$RUNS" "${PYTHON_ARGS[@]}") ;;
    latency)    PYTHON_ARGS=(--ops "$FRAMES" "${PYTHON_ARGS[@]}") ;;
    scaling)    PYTHON_ARGS=(--runs "$RUNS" "${PYTHON_ARGS[@]}") ;;
esac

cd "$PROJECT_DIR/python"
if [[ -f "$PROJECT_DIR/python/.venv/bin/activate" ]]; then
    source "$PROJECT_DIR/python/.venv/bin/activate"
fi

# ``python3 -m benchmarks.<name>`` — matches how an installed-package user
# would run the benchmark (post ``pip install -e .[dev]``).  Dropping the
# previous ``sys.path.insert`` trick folds wheel / setuptools shim overhead
# back into the measurement, see PY-31-2.
if run_benchmark "Python" "$RESULTS_DIR/python_${BENCH}.json" \
    python3 -m "benchmarks.$BENCH" "${PYTHON_ARGS[@]}"; then
    SUCCEEDED+=(Python)
else
    FAILED+=(Python)
fi

cd "$PROJECT_DIR"

# --- C++ ---
# Rebuilt here whenever the tree is configured, for the same reason as Go below:
# a pre-built binary can predate a kernel wire change and measure a format it
# cannot decode.  `cmake --build` is incremental, so a warm tree is fast.  An
# unconfigured tree is a graceful SKIP (configuring needs clang-22 + the
# FetchContent deps), matching the other optional-binding lanes.
CPP_DIR="$PROJECT_DIR/cpp"
CPP_BIN="$CPP_DIR/build/benchmark"
if [[ -f "$CPP_CACHE" ]]; then
    if CPP_BUILD_LOG="$(cmake --build "$CPP_DIR/build" --target benchmark 2>&1)"; then
        CPP_ARGS=("$BENCH" --json)
        case $BENCH in
            throughput) CPP_ARGS+=(--frames "$FRAMES" --runs "$RUNS") ;;
            latency)    CPP_ARGS+=(--ops "$FRAMES") ;;
            scaling)    CPP_ARGS+=(--runs "$RUNS") ;;
        esac

        if run_benchmark "C++" "$RESULTS_DIR/cpp_${BENCH}.json" \
            "$CPP_BIN" "${CPP_ARGS[@]}"; then
            SUCCEEDED+=(C++)
        else
            FAILED+=(C++)
        fi
    else
        echo ">>> SKIP: C++ benchmark failed to build" >&2
        printf '%s\n' "$CPP_BUILD_LOG" >&2
    fi
else
    echo ">>> SKIP: C++ benchmark tree not configured ($CPP_CACHE)" >&2
fi

# --- Go ---
# Built here, never consumed pre-built: an on-disk binary can predate a kernel
# wire change and then measure a format it cannot decode.  That is not
# hypothetical — a binary predating the detailed-extraction-reason wire format
# failed every extraction call, and because the failures were silent the two
# Signal Extraction lanes were simply absent from the results.  `go build` is
# incremental, so a warm tree is near-instant.  A build failure — e.g. Go not
# installed — is a graceful SKIP, matching the other optional-binding lanes.
GO_DIR="$PROJECT_DIR/go"
GO_BIN="$GO_DIR/benchmarks/benchmark"
if GO_BUILD_LOG="$(cd "$GO_DIR" && go build -o benchmarks/benchmark ./benchmarks/ 2>&1)"; then
    GO_ARGS=("$BENCH" --json)
    case $BENCH in
        throughput) GO_ARGS+=(--frames "$FRAMES" --runs "$RUNS") ;;
        latency)    GO_ARGS+=(--ops "$FRAMES") ;;
        scaling)    GO_ARGS+=(--runs "$RUNS") ;;
    esac

    if run_benchmark "Go" "$RESULTS_DIR/go_${BENCH}.json" \
        "$GO_BIN" "${GO_ARGS[@]}"; then
        SUCCEEDED+=(Go)
    else
        FAILED+=(Go)
    fi
else
    echo ">>> SKIP: Go benchmark failed to build (is go installed?)" >&2
    printf '%s\n' "$GO_BUILD_LOG" >&2
fi

# --- Rust ---
# Built here like the C++ and Go lanes above (a release example target;
# incremental, so a warm tree is near-instant). A build failure — e.g. cargo not
# installed — is a graceful SKIP, matching the optional-binding behaviour of the
# other lanes; the Rust source itself is gated by run_ci's cargo lanes, not this
# script.
RUST_DIR="$PROJECT_DIR/rust"
RUST_BIN="$RUST_DIR/target/release/examples/benchmark"
if RUST_BUILD_LOG="$(cd "$RUST_DIR" && cargo build --release --example benchmark 2>&1)"; then
    RUST_ARGS=("$BENCH" --json)
    case $BENCH in
        throughput) RUST_ARGS+=(--frames "$FRAMES" --runs "$RUNS") ;;
        latency)    RUST_ARGS+=(--ops "$FRAMES") ;;
        scaling)    RUST_ARGS+=(--runs "$RUNS") ;;
    esac

    if run_benchmark "Rust" "$RESULTS_DIR/rust_${BENCH}.json" \
        "$RUST_BIN" "${RUST_ARGS[@]}"; then
        SUCCEEDED+=(Rust)
    else
        FAILED+=(Rust)
    fi
else
    echo ">>> SKIP: Rust benchmark failed to build (is cargo installed?)" >&2
    printf '%s\n' "$RUST_BUILD_LOG" >&2
fi

# --- Compare ---
echo ""
if [[ ${#SUCCEEDED[@]} -gt 0 ]]; then
    echo ">>> Comparison (${SUCCEEDED[*]}):"
    echo ""
    # Only files written by THIS run: the directory was cleared for this mode
    # above, so every match is fresh — a skipped or failed lane contributes
    # nothing rather than its previous numbers.
    COMPARE_FILES=()
    for f in "$RESULTS_DIR"/*_${BENCH}.json; do
        [[ -f "$f" ]] && COMPARE_FILES+=("$f")
    done
    if [[ ${#COMPARE_FILES[@]} -gt 0 ]]; then
        python3 benchmarks/compare.py "${COMPARE_FILES[@]}"
    fi
fi

if [[ ${#FAILED[@]} -gt 0 ]]; then
    echo "WARNING: Failed benchmarks: ${FAILED[*]}" >&2
    exit 1
fi

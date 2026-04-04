#!/bin/bash
# Cross-Language Benchmark Runner
#
# Builds all bindings and runs throughput benchmarks for Python, C++, and Go.
# Results are saved as JSON in benchmarks/results/.
#
# Usage:
#     ./benchmarks/run_all.sh [--frames N] [--runs N] [--bench throughput|latency|scaling]
#
# Prerequisites:
#     - libaletheia-ffi.so built (cabal run shake -- build)
#     - Python venv activated with aletheia installed
#     - C++ benchmark built (cd cpp && cmake -B build && cmake --build build)
#     - Go benchmark built (cd go && go build -o benchmarks/benchmark ./benchmarks/)

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

mkdir -p "$RESULTS_DIR"

export ALETHEIA_LIB="$PROJECT_DIR/build/libaletheia-ffi.so"

if [[ ! -f "$ALETHEIA_LIB" ]]; then
    echo "ERROR: $ALETHEIA_LIB not found. Run: cabal run shake -- build" >&2
    exit 1
fi

echo "=== Aletheia Cross-Language Benchmark ==="
echo "Benchmark: $BENCH"
echo "Frames:    $FRAMES"
echo "Runs:      $RUNS"
echo "Library:   $ALETHEIA_LIB"
echo ""

# run_benchmark LANG COMMAND OUTFILE
#
# Runs a benchmark command, captures stdout to a temp file, validates the JSON,
# then atomically moves it to the final output path. Non-JSON lines on stdout
# (e.g., GHC RTS warnings, cgo diagnostics) are stripped.
run_benchmark() {
    local lang="$1"
    local outfile="$2"
    shift 2
    local cmd=("$@")

    local tmpfile
    tmpfile="$(mktemp "$RESULTS_DIR/.tmp.${lang}.XXXXXX")"
    trap "rm -f '$tmpfile'" RETURN

    echo ">>> Running $lang $BENCH benchmark..."

    # Run benchmark. stdout → tmpfile, stderr → /dev/null (progress output).
    # Some runtimes (GHC RTS, cgo) print warnings to stdout; we filter to
    # only the JSON object by extracting from the first '{' to the last '}'.
    if ! "${cmd[@]}" > "$tmpfile" 2>/dev/null; then
        echo "    FAIL: $lang benchmark exited with error" >&2
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
        cat "$tmpfile" >&2
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
    latency)   PYTHON_ARGS=(--ops "$FRAMES" "${PYTHON_ARGS[@]}") ;;
    scaling)   PYTHON_ARGS=(--quick "${PYTHON_ARGS[@]}") ;;
esac

cd "$PROJECT_DIR/python"
if [[ -f "$PROJECT_DIR/.venv/bin/activate" ]]; then
    source "$PROJECT_DIR/.venv/bin/activate"
fi

if run_benchmark "Python" "$RESULTS_DIR/python_${BENCH}.json" \
    python3 "benchmarks/$BENCH.py" "${PYTHON_ARGS[@]}"; then
    SUCCEEDED+=(Python)
else
    FAILED+=(Python)
fi

cd "$PROJECT_DIR"

# --- C++ ---
CPP_BIN="$PROJECT_DIR/cpp/build/benchmark"
if [[ -f "$CPP_BIN" ]]; then
    CPP_ARGS=("$BENCH" --json)
    case $BENCH in
        throughput|latency) CPP_ARGS+=( --frames "$FRAMES" --runs "$RUNS") ;;
        scaling) CPP_ARGS+=(--frames 5000) ;;
    esac

    if run_benchmark "C++" "$RESULTS_DIR/cpp_${BENCH}.json" \
        "$CPP_BIN" "${CPP_ARGS[@]}"; then
        SUCCEEDED+=(C++)
    else
        FAILED+=(C++)
    fi
else
    echo ">>> SKIP: C++ benchmark not built ($CPP_BIN)"
fi

# --- Go ---
GO_BIN="$PROJECT_DIR/go/benchmarks/benchmark"
if [[ -f "$GO_BIN" ]]; then
    GO_ARGS=("$BENCH" --json)
    case $BENCH in
        throughput|latency) GO_ARGS+=(--frames "$FRAMES" --runs "$RUNS") ;;
        scaling) GO_ARGS+=(--frames 5000) ;;
    esac

    if run_benchmark "Go" "$RESULTS_DIR/go_${BENCH}.json" \
        "$GO_BIN" "${GO_ARGS[@]}"; then
        SUCCEEDED+=(Go)
    else
        FAILED+=(Go)
    fi
else
    echo ">>> SKIP: Go benchmark not built ($GO_BIN)"
fi

# --- Compare ---
echo ""
if [[ ${#SUCCEEDED[@]} -gt 0 ]]; then
    echo ">>> Comparison (${SUCCEEDED[*]}):"
    echo ""
    # Only pass files that exist and were successfully written
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

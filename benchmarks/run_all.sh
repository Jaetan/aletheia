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

# --- Python ---
echo ">>> Running Python $BENCH benchmark..."
PYTHON_ARGS="--json"
case $BENCH in
    throughput) PYTHON_ARGS="--frames $FRAMES --runs $RUNS $PYTHON_ARGS" ;;
    latency)   PYTHON_ARGS="--ops $FRAMES $PYTHON_ARGS" ;;
    scaling)   PYTHON_ARGS="--quick $PYTHON_ARGS" ;;
esac

cd "$PROJECT_DIR/python"
if [[ -f "$PROJECT_DIR/.venv/bin/activate" ]]; then
    source "$PROJECT_DIR/.venv/bin/activate"
fi
python3 "benchmarks/$BENCH.py" $PYTHON_ARGS > "$RESULTS_DIR/python_${BENCH}.json" 2>/dev/null
echo "    Saved: results/python_${BENCH}.json"

# --- C++ ---
CPP_BIN="$PROJECT_DIR/cpp/build/benchmark"
if [[ -f "$CPP_BIN" ]]; then
    echo ">>> Running C++ $BENCH benchmark..."
    CPP_ARGS="$BENCH --json"
    case $BENCH in
        throughput|latency) CPP_ARGS="$CPP_ARGS --frames $FRAMES --runs $RUNS" ;;
        scaling) CPP_ARGS="$CPP_ARGS --frames 5000" ;;
    esac
    "$CPP_BIN" $CPP_ARGS > "$RESULTS_DIR/cpp_${BENCH}.json" 2>/dev/null
    echo "    Saved: results/cpp_${BENCH}.json"
else
    echo "    SKIP: C++ benchmark not built ($CPP_BIN)"
fi

# --- Go ---
GO_BIN="$PROJECT_DIR/go/benchmarks/benchmark"
if [[ -f "$GO_BIN" ]]; then
    echo ">>> Running Go $BENCH benchmark..."
    GO_ARGS="$BENCH --json"
    case $BENCH in
        throughput|latency) GO_ARGS="$GO_ARGS --frames $FRAMES --runs $RUNS" ;;
        scaling) GO_ARGS="$GO_ARGS --frames 5000" ;;
    esac
    "$GO_BIN" $GO_ARGS > "$RESULTS_DIR/go_${BENCH}.json" 2>/dev/null
    echo "    Saved: results/go_${BENCH}.json"
else
    echo "    SKIP: Go benchmark not built ($GO_BIN)"
fi

# --- Compare ---
echo ""
echo ">>> Comparison:"
echo ""
cd "$PROJECT_DIR"
python3 benchmarks/compare.py "$RESULTS_DIR"/*_${BENCH}.json

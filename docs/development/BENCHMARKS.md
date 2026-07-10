# Aletheia Performance Benchmarks

Benchmarks across the Python, C++, and Go bindings (the Rust binding is not yet
wired into the cross-language runner). This document describes what the benchmarks
measure, how to run them, and the canonical results.

## Canonical Results

Per-binding throughput (frames/sec), best of two clean back-to-back batches on the
current host (Intel Core Ultra 9 285K), re-measured 2026-06-11 under Clang 22
(per-lane intra-batch stdev ≤ 2.6%, one Python lane 6.3%):

| Benchmark | C++ (fps) | Go (fps) | Python (fps) |
|---|---:|---:|---:|
| CAN 2.0B: Stream LTL (2 props) | **249,945** | 223,855 | 143,227 |
| CAN 2.0B: Signal Extraction   | **401,897** | 337,441 | 138,843 |
| CAN 2.0B: Frame Building       | **133,308** | 125,573 | 88,609 |
| CAN-FD: Stream LTL (3 props)   | **108,679** | 106,670 | 79,078 |
| CAN-FD: Signal Extraction      | **27,697**  | 26,477  | 19,498 |
| CAN-FD: Frame Building         | **32,252**  | 31,836  | 27,147 |

Per-frame latency is ~4 µs (CAN 2.0B streaming, C++); memory is O(1) (verified
1.08× growth across a 100× longer trace); every hot-path operation uses the binary
FFI (no JSON on the streaming path). Moving Clang 19 → 22 was performance-neutral
(every lane within run-to-run noise). The slowest lane — Python CAN-FD extraction
at 19,498 fps — still clears the ~6,000 fps a 5 Mbit/s CAN-FD bus needs by ~3×.
Frame Building is the narrowest C++/Go margin (it does the least Agda work and the
most binding-side allocation per call); Stream LTL and Signal Extraction are clearly
C++-dominant.

---

## Cross-Language Runner

The primary entry point is [`benchmarks/run_all.sh`](../../benchmarks/run_all.sh). It
builds nothing on its own — `libaletheia-ffi.so`, the Python package, the C++
binary, and the Go binary must already be built — and produces one JSON file
per binding in `benchmarks/results/`, followed by a side-by-side comparison
printed by `benchmarks/compare.py`.

```bash
# Prerequisites (one-time)
cabal run shake -- build                                                # libaletheia-ffi.so
source python/.venv/bin/activate && (cd python && pip install -e '.[dev]')  # Python binding
cmake -B cpp/build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22 && cmake --build cpp/build  # C++ binary (Clang 22)
(cd go && go build -o benchmarks/benchmark ./benchmarks/)                # Go binary

# Run throughput across the Python, C++, and Go bindings, 10,000 frames × 5 runs
./benchmarks/run_all.sh

# Other lanes / scales
./benchmarks/run_all.sh --frames 50000 --runs 3
./benchmarks/run_all.sh --bench latency
./benchmarks/run_all.sh --bench scaling
```

The runner refuses to run against a Debug-mode C++ build (`CMAKE_BUILD_TYPE=Debug`
in `cpp/build/CMakeCache.txt`) — an unoptimized tree silently looks like a
20%+ regression, as an earlier investigation documented. Reconfigure with
`-DCMAKE_BUILD_TYPE=Release` if the guard trips.

---

## Per-Binding Benchmarks

### Python — `python/benchmarks/`

Runs `python3 -m benchmarks.<name>` from the `python/` directory (matches the
`pip install -e .[dev]` layout):

| Script | Measures | Typical arguments |
|---|---|---|
| `throughput.py` | Frames per second through the full pipeline | `--frames 10000 --runs 5` |
| `latency.py` | Per-operation latency distribution (p50, p90, p99, p99.9) | `--ops 5000` |
| `violations.py` | Enrichment overhead on the `send_frame` and `_run_checks` paths with a 256-entry extraction cache | `--frames 10000 --runs 5` |
| `scaling.py` | Scaling across trace size (1K–100K frames), property count (1–10), property complexity | `--quick` for a reduced iteration count |
| `simplification.py` | FPS vs trace length across 11 LTL formula shapes — detects Rosu simplification tree growth (FPS degradation = unbounded tree) | `--quick` for a reduced iteration count |
| `sysinfo.py` | 5-second quick benchmark + memory / Docker sizing report | — |

### C++ — `cpp/benchmarks/benchmark.cpp`

Single binary (`cpp/build/benchmark`) that accepts a subcommand:

```bash
./cpp/build/benchmark throughput --frames 10000 --runs 5 --json
./cpp/build/benchmark latency    --frames 5000  --runs 5 --json
./cpp/build/benchmark scaling    --frames 5000                --json
```

The binary aborts at startup unless compiled with `NDEBUG` (Release mode);
the JSON output carries `system.build_type` so downstream tools can verify.

### Go — `go/benchmarks/main.go`

Single binary (`go/benchmarks/benchmark`) with the same subcommand surface as
the C++ benchmark:

```bash
./go/benchmarks/benchmark throughput --frames 10000 --runs 5 --json
./go/benchmarks/benchmark latency    --frames 5000  --runs 5 --json
./go/benchmarks/benchmark scaling    --frames 5000                --json
```

### Shared micro-benchmarks — `benchmarks/`

Narrow-scope tools used when investigating a specific overhead, not part of
the regular cross-language run:

- `response_overhead.{py,cpp,go}` + `response_overhead_ffi.c` — cost of the
  JSON response encode/decode boundary, isolated from Agda work.
- `vec_construction.c` — `std::vector<std::byte>` construction cost in the
  C++ binding hot path.
- `profile_extraction.py` — per-frame signal-extraction profile on the Python
  side.
- `compare.py` — invoked by `run_all.sh` to diff the per-binding JSON outputs.

---

## Methodology and Variance

Benchmarks are measured on an Intel Core Ultra 9 285K (24 cores), Linux 6.6
(WSL2), with C++ clang++-22 `-O3`, Go 1.26.3, Python 3.14.5 (exact versions
printed in each JSON output under `system`).

The ±10% inter-run variance gate and the ~2–4% steady-state noise floor are
codified in [AGENTS.md § Step 4: Implement and verify](../../AGENTS.md#step-4-implement-and-verify).
On an apparent regression, the two-batch protocol (run the same binary
twice, compare the second batch against the baseline) distinguishes
WSL2/thermal noise from a real change.

Always rebuild `libaletheia-ffi.so` before a measurement if the Agda or
Haskell layer has changed (`stat build/libaletheia-ffi.so` vs. the latest
commit touching `src/` or `haskell-shim/`). A stale `.so` measures the
previous Agda core, not the current one.

---

## CI regression gate

`.github/workflows/benchmark.yml` runs the throughput suite on every pull
request (and on demand via `workflow_dispatch`). On a PR it then runs
`tools/benchmark_gate.py`, which **fails the check if any lane is more than 30%
slower** than the committed GitHub-runner baseline (`benchmarks/gha_baseline.json`).

The 30% threshold is deliberately generous: the GitHub-hosted runner is shared
and noisy, so the gate is meant to catch a *noticeable* regression, not
run-to-run jitter (the 5-run mean already damps within-run noise). The baseline
is measured **on the runner**, not on the local host — the two machines differ
several-fold, so local numbers must never be used as the gate baseline.

To refresh the baseline after an intentional performance change, take the
numbers from a known-good PR run (the gate prints them, and they are uploaded as
the `benchmark-throughput-results` artifact) and commit them to
`benchmarks/gha_baseline.json`. When that file is absent the gate is in
bootstrap mode: it reports the numbers and passes.

---

## Profiling

For deeper analysis, enable GHC profiling in `haskell-shim/aletheia.cabal`:

```cabal
ghc-options: -prof -fprof-auto
```

Rebuild, run any throughput benchmark, and inspect the generated `.prof` /
`profiles/` output. The same approach works with Linux `perf` on the Python
or C++ front-ends for system-level profiling.

# Aletheia Performance Benchmarks

Benchmarks across the three bindings (Python, C++, Go). The canonical
per-binding / per-lane / per-property-shape throughput table — dated
measurements on fixed hardware — lives in
[PROJECT_STATUS.md § Key Metrics](../../PROJECT_STATUS.md#key-metrics). This
document describes what the benchmarks measure and how to run them; it does
not duplicate the numbers.

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
source .venv/bin/activate && pip install -e python/[dev]                # Python binding
cmake -B cpp/build && cmake --build cpp/build                            # C++ binary
(cd go && go build -o benchmarks/benchmark ./benchmarks/)                # Go binary

# Run throughput across all three bindings, 10,000 frames × 5 runs
./benchmarks/run_all.sh

# Other lanes / scales
./benchmarks/run_all.sh --frames 50000 --runs 3
./benchmarks/run_all.sh --bench latency
./benchmarks/run_all.sh --bench scaling
```

The runner refuses to run against a Debug-mode C++ build (`CMAKE_BUILD_TYPE=Debug`
in `cpp/build/CMakeCache.txt`) — an unoptimized tree silently looks like a
20%+ regression, as the R15 investigation documented. Reconfigure with
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

Benchmarks are measured on an AMD Ryzen 9 5950X, Linux 6.6 (WSL2), with C++
g++-15 `-O3`, Go 1.26.1, Python 3.13.12 (exact versions printed in each JSON
output under `system`).

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

## Profiling

For deeper analysis, enable GHC profiling in `haskell-shim/aletheia.cabal`:

```cabal
ghc-options: -prof -fprof-auto
```

Rebuild, run any throughput benchmark, and inspect the generated `.prof` /
`profiles/` output. The same approach works with Linux `perf` on the Python
or C++ front-ends for system-level profiling.

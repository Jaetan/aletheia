# Aletheia Performance Benchmarks

Benchmarks across the Python, C++, Go and Rust bindings. This document describes what the benchmarks measure, how to run them, and the canonical results.

## Canonical Results

Per-binding throughput in frames a second: the committed baseline set, `benchmarks/results/*_throughput_baseline.json`, measured 2026-07-26 on the host below. No lane's standard deviation exceeds 5.1% of its mean.

| Benchmark | C++ (fps) | Rust (fps) | Go (fps) | Python (fps) |
|---|---:|---:|---:|---:|
| CAN 2.0B: Stream LTL (2 props) | 287,620 | 277,317 | 265,605 | 155,586 |
| CAN 2.0B: Signal Extraction | 398,927 | 399,433 | 343,640 | 136,192 |
| CAN 2.0B: Frame Building | 127,827 | 128,376 | 119,633 | 83,431 |
| CAN-FD:   Stream LTL (3 props) | 165,215 | 164,458 | 156,353 | 106,411 |
| CAN-FD:   Signal Extraction | 28,685 | 28,802 | 27,755 | 20,150 |
| CAN-FD:   Frame Building | 31,778 | 32,074 | 31,334 | 26,149 |

Rust is within 3.6% of C++ on every lane. Go's gap runs from 14% on CAN 2.0B signal extraction to 1.4% on CAN-FD frame building.

Per-frame C++ latency on CAN 2.0B streaming has a median of 3.1 µs and a mean of 3.5 µs, from the committed latency baseline. Memory is flat in the trace length: the suite refuses a run whose peak resident set grows by 32 MiB.

---

## Cross-Language Runner

The primary entry point is [`benchmarks/run_all.sh`](../../benchmarks/run_all.sh). It **builds the C++, Go and Rust benchmark binaries itself**, incrementally, then produces one JSON file per binding that ran, in `benchmarks/results/`, followed by a side-by-side comparison printed by `benchmarks/compare.py`.

A benchmark binary is never taken as found on disk: one that predates a kernel wire change does not measure an older system, it fails to measure the current one, so its numbers are void rather than merely old. What the runner needs from you is `libaletheia-ffi.so`, the Python package, and a *configured* `cpp/build` tree.

The runner also clears the selected mode's results before running, so a lane that skips or fails contributes nothing rather than its previous numbers. It refuses a zero or non-numeric `--frames` or `--runs` before touching anything, since a zero count makes every lane publish an all-zero report. A lane is skipped when what it needs is absent, which for Go and Rust is the toolchain and for C++ is a configured `cpp/build`; a lane whose build breaks with everything present is a failure. `ALETHEIA_BENCH_RESULTS_DIR` redirects the results directory, which is how the probes exercise the runner without touching the last measurements.

```bash
# Prerequisites (one-time)
cabal run shake -- build                                                # libaletheia-ffi.so
source python/.venv/bin/activate && (cd python && pip install -e '.[dev]')  # Python binding
cmake -S cpp -B cpp/build -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22  # configure C++ (Clang 22)
# `go` and `cargo` on PATH; the runner builds those benchmarks itself.

# Run throughput across all four bindings, 10,000 frames × 5 runs
./benchmarks/run_all.sh

# Other lanes / scales
./benchmarks/run_all.sh --frames 50000 --runs 3
./benchmarks/run_all.sh --bench latency
./benchmarks/run_all.sh --bench scaling
```

The runner refuses a Debug-mode C++ build, reading `CMAKE_BUILD_TYPE` from `cpp/build/CMakeCache.txt`, because an unoptimized tree reads as a regression of twenty per cent or more. Reconfigure with `-DCMAKE_BUILD_TYPE=Release` if it trips.

---

## Per-Binding Benchmarks

### Python, in `python/benchmarks/`

Run as `python3 -m benchmarks.<name>` from `python/`.

| Script | Measures | Typical arguments |
|---|---|---|
| `throughput.py` | Frames per second through the full pipeline | `--frames 10000 --runs 5` |
| `latency.py` | Per-operation latency distribution (p50, p90, p99, p99.9) | `--ops 5000` |
| `violations.py` | Enrichment overhead on `send_frame` and `_run_checks`, against a 256-entry extraction cache | `--frames 10000 --runs 5` |
| `scaling.py` | Scaling across trace size (1K–100K frames), property count (1–10), property complexity | `--quick` for a reduced iteration count |
| `simplification.py` | Throughput against trace length per LTL formula shape; a rate that falls away is an unbounded Rosu simplification tree | `--quick` for a reduced iteration count |
| `sysinfo.py` | A short run, with peak memory and Docker sizing | none |

### One binary each, for C++, Go and Rust

`cpp/build/benchmark`, `go/benchmarks/benchmark` and `rust/target/release/examples/benchmark` take a mode and the flags `benchmarks/SCHEMA.yaml` pins for it. `tools/check_bench_schema.py` drives all four bindings through all three modes with those flags on every CI run, so a renamed or dropped flag fails instead of falling back on a default.

```bash
./cpp/build/benchmark throughput --frames 10000 --runs 5 --json
./cpp/build/benchmark latency    --ops 5000 --json
./cpp/build/benchmark scaling    --runs 5 --quick --json
```

Latency counts operations and scaling picks its own trace sizes, so a frame count reaches throughput alone: all three binaries take `--frames` on either without reading it, and the run measures the default and reports it. The C++ binary also aborts unless compiled with `NDEBUG`, and its reports carry `system.build_type`.

### Shared micro-benchmarks, in `benchmarks/`

Narrow-scope tools, outside the cross-language run. The long-run stability harnesses are their own lane, [STABILITY.md](../operations/STABILITY.md).

- `response_overhead.{py,cpp,go}` with `response_overhead_ffi.c`, the JSON response boundary isolated from Agda work.
- `vec_construction.c`, constructing a `std::vector<std::byte>` on the C++ hot path.
- `profile_extraction.py`, a per-frame signal-extraction profile in Python.
- `compare.py`, which `run_all.sh` invokes to diff the per-binding outputs.

---

## Methodology and Variance

Measured on an Intel Core Ultra 9 285K of 24 cores under WSL2, with `clang++-22` at `-O3`, Go 1.26.3, Python 3.14.5 and rustc 1.97.1. Each report's `system` object carries the host, plus the runtime version for Go, Python and Rust and `build_type` for C++.

The inter-run variance gate of ±10% and the noise floor of 2% to 4% are codified in [AGENTS.md § Step 4: Implement and verify](../../AGENTS.md#step-4-implement-and-verify). On an apparent regression, run the binary twice and read the second batch against the baseline: that separates WSL2 and thermal noise from a real change.

Run `cabal run shake -- build` before every measurement. Shake tracks the Agda sources by content, so it costs nothing when nothing changed; a stale library measures the previous Agda core.

---

## CI regression gate

`.github/workflows/benchmark.yml` runs the throughput suite on every pull request touching something other than Markdown or `docs/`, and on demand through `workflow_dispatch`. On a pull request it then runs `tools/benchmark_gate.py`, which **fails the check if any lane is more than 30% slower** than the GitHub-runner baseline in `benchmarks/gha_baseline.json`.

The threshold is generous: the hosted runner is shared and noisy, so the gate catches a *noticeable* regression rather than jitter, the five-run mean having damped the noise within a run. A failing gate re-measures once and gates again, a slow runner slowing every lane at once where a real regression slows only what changed. The baseline is measured **on the runner**, never locally, the two machines differing several-fold.

To refresh it after an intentional change, commit a known-good run's numbers, which the gate prints and the workflow uploads as the `benchmark-throughput-results` artifact. With that file absent the gate is in bootstrap mode: it reports and passes.

---

## Profiling

Profiling the Agda kernel belongs to the stability lane, whose recipe is in [STABILITY.md](../operations/STABILITY.md): that runner asks the GHC runtime for a heap profile itself, while a time profile needs a rebuild with `--enable-profiling`, every transitive Haskell dependency included. Linux `perf` covers the binding front-ends.

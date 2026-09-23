# Aletheia Performance Benchmarks

Benchmarks across the Python, C++, Go and Rust bindings: what they measure, how to run them, the committed baselines and the canonical results.

## Canonical Results

Per-binding throughput in frames a second: the committed baseline set, `benchmarks/results/*_throughput_baseline.json`, measured 2026-07-26 on the host [Local baselines](#local-baselines) names. No lane's standard deviation exceeds 5.1% of its mean.

| Benchmark | C++ (fps) | Rust (fps) | Go (fps) | Python (fps) |
|---|---:|---:|---:|---:|
| CAN 2.0B: Stream LTL (2 props) | 287,620 | 277,317 | 265,605 | 155,586 |
| CAN 2.0B: Signal Extraction | 398,927 | 399,433 | 343,640 | 136,192 |
| CAN 2.0B: Frame Building | 127,827 | 128,376 | 119,633 | 83,431 |
| CAN-FD:   Stream LTL (3 props) | 165,215 | 164,458 | 156,353 | 106,411 |
| CAN-FD:   Signal Extraction | 28,685 | 28,802 | 27,755 | 20,150 |
| CAN-FD:   Frame Building | 31,778 | 32,074 | 31,334 | 26,149 |

Per-frame C++ latency on CAN 2.0B streaming has a median of 3.2 µs and a mean of 3.6 µs, from the committed latency baseline. Streaming does not retain what it accepts: the Python suite fails a session of 100,000 frames whose peak resident set grows by 32 MiB.

---

## Cross-Language Runner

[`benchmarks/run_all.sh`](../../benchmarks/run_all.sh) builds the C++, Go and Rust benchmark binaries itself, incrementally, runs one mode across the four bindings, writes `benchmarks/results/<binding>_<mode>.json` for each binding that ran, and prints the comparison from `benchmarks/compare.py`. A binary is never taken as found on disk: one that predates a kernel wire change fails to measure the current system.

Throughput reads `--frames` and `--runs`, latency reads `--frames` as its operation count and `--warmup`, and scaling reads `--runs` alone. The runner clears the mode's previous results, so a lane that skips or fails contributes nothing rather than its previous numbers, and before clearing them it refuses a zero or non-numeric count, a negative warmup, a mode it does not have, a flag the chosen mode does not read, and a Debug-configured `cpp/build`, for which it prints the reconfigure. A lane is skipped when what it needs is absent, the toolchain for Go and Rust and a configured `cpp/build` for C++; a lane whose build breaks with everything present is a failure. `ALETHEIA_BENCH_RESULTS_DIR` redirects the results directory.

```bash
# Prerequisites (one-time)
cabal run shake -- build                                                # libaletheia-ffi.so
source python/.venv/bin/activate && (cd python && pip install -e '.[dev]')  # Python binding
cmake -S cpp -B cpp/build -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23  # configure C++ (Clang 23)
# `go` and `cargo` on PATH; the runner builds those benchmarks itself.

# Run throughput across all four bindings, 10,000 frames × 5 runs
./benchmarks/run_all.sh

# Other modes
./benchmarks/run_all.sh --bench latency --warmup 500
./benchmarks/run_all.sh --bench scaling
```

---

## Local baselines

`benchmarks/results/<binding>_<mode>_baseline.json`, one per binding and mode, is the committed measurement; the runner's own `<binding>_<mode>.json` beside it is ignored by git.

Measured on an Intel Core Ultra 9 285K of 24 cores under WSL2, with `clang++-22` at `-O3`; each file's `system` object records the runtime that measured it, and no file records the C++ compiler. A throughput baseline is 10 runs of 10,000 frames per lane, a latency baseline 10,000 timed operations per lane, and a scaling baseline the full sweep, five trace sizes where `--quick` runs four; the warmup and the scaling run count are not recorded in the files.

To read a fresh run against its baseline, run `cabal run shake -- build`, since a stale library measures the previous Agda core; run the mode with the counts the baseline records; and give `compare.py` the binding's fresh file and its baseline:

```bash
./benchmarks/run_all.sh --frames 10000 --runs 10
python/.venv/bin/python benchmarks/compare.py benchmarks/results/cpp_throughput*.json
```

Given a binding's fresh file and its baseline, `compare.py` prints per lane the current mean, the baseline mean, the delta and the current standard deviation, the report shape AGENTS.md asks for; given several bindings it prints them side by side, given several modes a table per mode, and two files that would share a column are refused rather than one replacing the other.

The delta is not a verdict on its own: the host runs the same lane at its baseline speed or at about half of it from one batch to the next with no code cause, so a fresh run is repeated and the faster batch read against the baseline, beside its standard deviation and the ±10% variance gate and 2% to 4% noise floor [AGENTS.md § Step 4](../../AGENTS.md#step-4-implement-and-verify) codifies.

---

## Per-Binding Benchmarks

### Python, in `python/benchmarks/`

Run as `python3 -m benchmarks.<name>` from `python/`. `throughput`, `latency` and `scaling` take the flags `benchmarks/SCHEMA.yaml` pins for their mode, as the binaries below do; scaling sweeps trace size, property count and property complexity. The other three are Python-only:

- `violations.py`, the enrichment overhead on `send_frame` and `_run_checks`, against a 256-entry extraction cache.
- `simplification.py`, throughput against trace length per LTL formula shape; a rate that falls away is an unbounded Rosu simplification tree. `--quick` reduces the iteration count.
- `sysinfo.py`, a short run with peak memory and Docker sizing.

### One binary each, for C++, Go and Rust

`cpp/build/benchmark`, `go/benchmarks/benchmark` and `rust/target/release/examples/benchmark` take a mode and the flags `benchmarks/SCHEMA.yaml` pins for it. `tools/check_bench_schema.py` drives all four bindings through all three modes with those flags on every CI run, so a renamed or dropped flag fails instead of falling back on a default.

```bash
./cpp/build/benchmark throughput --frames 10000 --runs 5 --json
./cpp/build/benchmark latency    --ops 5000 --json
./cpp/build/benchmark scaling    --runs 5 --quick --json
```

`--frames` reaches throughput alone: the binaries accept it on the other two modes, ignore it, and report the default they ran. The C++ binary also aborts unless compiled with `NDEBUG`, and its reports carry `system.build_type`.

### Shared micro-benchmarks, in `benchmarks/`

Narrow-scope tools, outside the cross-language run. The long-run stability harnesses are their own lane, [STABILITY.md](../operations/STABILITY.md).

- `response_overhead.{py,cpp,go}` with `response_overhead_ffi.c`, the JSON response boundary isolated from Agda work.
- `vec_construction.c`, constructing a `std::vector<std::byte>` on the C++ hot path.
- `profile_extraction.py`, a per-frame signal-extraction profile in Python.

---

## CI regression gate

`.github/workflows/benchmark.yml` runs the throughput suite on every pull request touching something other than Markdown or `docs/`, and on demand through `workflow_dispatch`. On a pull request it then runs `tools/benchmark_gate.py`, which **fails the check if any lane is more than 30% slower** than the GitHub-runner baseline in `benchmarks/gha_baseline.json`. A binding with no result file is skipped, its build failure being `pr-full-ci`'s to report; a binding whose file is present but lacks a lane the baseline names fails the gate with the lane named.

The threshold is generous: the hosted runner is shared and noisy, so the gate catches a *noticeable* regression rather than jitter, the five-run mean having damped the noise within a run. A failing gate re-measures once and gates again, a slow runner slowing every lane at once where a real regression slows only what changed. The baseline is measured **on the runner**, never locally, the two machines differing several-fold. The hosted runners come in more than one CPU class, and the classes differ by up to twofold, so the baseline is taken from the most common class, which the C++ report's `system.cpu` names: a run on a faster class passes with a wide margin, and a run on the common class is the one the gate measures.

To refresh it after an intentional change, take a known-good pull-request run's `benchmark-throughput-results` artifact, check that its C++ report names the common class, and write the baseline with the gate's own bootstrap mode, `python3 -m tools.benchmark_gate --results-dir <artifact> --baseline /nonexistent`, which prints the run in baseline shape. With the baseline file absent on a pull request the gate is in that mode: it reports and passes.

---

## Profiling

Profiling the Agda kernel belongs to the stability lane, whose recipe is in [STABILITY.md](../operations/STABILITY.md): that runner asks the GHC runtime for a heap profile itself, while a time profile needs a rebuild with `--enable-profiling`, every transitive Haskell dependency included. Linux `perf` covers the binding front-ends.

# Long-Run Stability Bench

Procedure for running the per-binding long-run resource-leakage harnesses.
AGENTS.md cat 16 / 25 / 26 / 27 mandate that a stability
bench of ≥ 1M frames must run with no per-iteration drift on RSS / FD count /
binding-specific resource accounting (`StablePtr` for Go, `RTSState` for
Python, `std::thread` for C++) and emit a GHC RTS heap-typed profile so
allocation behavior is recorded across the long-run window.

## Quick start

```bash
cabal run shake -- build
cmake --build cpp/build --target stability_bench  # C++ harness binary

# Default: 10 cycles × 100K frames per binding (= 1M total each), ~5-10 min.
ALETHEIA_STABILITY_CHECK=1 python3 tools/stability_run.py
```

Artifacts land at `benchmarks/stability/<short-sha>/`:

```
python.json      Python harness verdict + delta per sub-check
go.json          Go harness verdict + delta per sub-check
cpp.json         C++ harness verdict + delta per sub-check
aletheia-ffi.hp  GHC RTS heap-typed profile (Agda cat 16)
summary.json     Aggregated verdict
```

`benchmarks/stability/` is gitignored — these are volatile per-run
artifacts.  The spec defining what each binding's harness MUST measure
lives at `docs/STABILITY_BENCH.yaml`; the static gate
`tools/check_stability_bench.py` (Shake target `check-stability-bench`,
an always-on offline enforcer in `tools/run_ci.py`) verifies every
(binding, sub_check) pair's `source_marker` is present in the harness source.

## Tuning the run

| Env var                       | Default | Effect                              |
| ----------------------------- | ------- | ----------------------------------- |
| `ALETHEIA_STABILITY_CYCLES`   | 10      | Outer cycles (Init/Close pairs)     |
| `ALETHEIA_STABILITY_FRAMES`   | 100000  | Inner frames per cycle              |
| `ALETHEIA_LIB`                | auto    | Override `libaletheia-ffi.so` path  |
| `ALETHEIA_RTS_OPTS` (Python)  | unset   | Extra RTS flags appended to argv at `hs_init_with_rtsopts` time; the runner sets `-hT` for the heap profile |

Smoke run for harness development (~30s):

```bash
ALETHEIA_STABILITY_CYCLES=2 ALETHEIA_STABILITY_FRAMES=1000 \
  python3 tools/stability_run.py
```

> **Note on smoke-run heap profile.**  GHC's `-hT` heap profiler samples at
> 0.1s wall by default.  Smoke runs that finish under ~10s produce a
> nearly-empty `aletheia-ffi.hp` (≤ 100 samples) — useful only as a
> file-existence smoke test for the env-var path, not for retention
> analysis.  Meaningful heap-shape inference needs ≥ 30s wall (≥ 300
> samples).  The default 10 cycles × 100K frames clears
> this comfortably; tune `ALETHEIA_STABILITY_FRAMES` upward when running
> short cycles to compensate (e.g. `CYCLES=2 FRAMES=200000` for a quick
> heap-profile capture).  Sample interval can be tightened via
> `ALETHEIA_RTS_OPTS="-hT -i0.01"` when you genuinely need finer grain.

## Per-binding sub-checks

Spec is authoritative — see `docs/STABILITY_BENCH.yaml`.

### Python (cat 25)

| Sub-check         | Gate           | Source                                          |
| ----------------- | -------------- | ----------------------------------------------- |
| `rss`             | soft 50 MiB    | `psutil.Process().memory_info().rss`            |
| `fd_count`        | hard zero      | `/proc/self/fd` (anon_inode filtered)           |
| `ctypes_handles`  | hard zero      | `RTSState.refcount` post-final-close            |
| `logger_handlers` | hard zero      | `len(logging.getLogger("aletheia").handlers)`   |

Harness: `python/benchmarks/stability.py`.

### Go (cat 27)

| Sub-check     | Gate           | Source                                                |
| ------------- | -------------- | ----------------------------------------------------- |
| `rss`         | soft 50 MiB    | `runtime/metrics /memory/classes/heap/objects:bytes`  |
| `fd_count`    | hard zero      | `/proc/self/fd` (anon_inode filtered)                 |
| `goroutines`  | hard zero      | `runtime.NumGoroutine`                                |
| `stableptr`   | hard zero      | `aletheia.StablePtrCount()` (Init++ / Close--)         |

Harness: `go/benchmarks/stability/main.go`.

### C++ (cat 26)

| Sub-check              | Gate           | Source                                            |
| ---------------------- | -------------- | ------------------------------------------------- |
| `rss`                  | soft 50 MiB    | `/proc/self/status` `VmRSS:`                      |
| `fd_count`             | hard zero      | `/proc/self/fd` (anon_inode filtered)             |
| `active_thread_count`  | hard zero      | `/proc/self/status` `Threads:`                    |
| `malloc_info`          | soft 50 MiB    | glibc `malloc_info()` aggregate `<total size=…/>` |

Harness: `cpp/benchmarks/stability_bench.cpp`.

### Agda (cat 16 — GHC RTS heap profile)

The Python lane drives the RTS profile capture.  When invoked from
`tools/stability_run.py`, the runner sets `ALETHEIA_RTS_OPTS=-hT`; the
Python binding's `RTSState.acquire` extends the argv passed to
`hs_init_with_rtsopts` with those flags.  The GHC RTS emits
`aletheia.hp` in the runner's cwd; the runner renames it to
`benchmarks/stability/<short-sha>/aletheia-ffi.hp`.

Time profiling (`-p`) requires a profiling-enabled `.so` rebuild (every
transitive Haskell dep compiled `-prof`); not enabled by default.  When
needed: rebuild with `--enable-profiling` and re-run with
`ALETHEIA_RTS_OPTS="-p -hT"`.

## Threshold model

Two-tier per advisor 2026-05-08:

* **Hard zero** — exact equality after `Close()` + GC.  Any drift is a
  finding regardless of magnitude.  These are the genuine leak detectors.
* **Soft threshold** — empirically-tuned cap that lives next to the
  assertion in the harness source (search for `RssDeltaBytesCap`,
  `kMallocDeltaBytesCap`, `rssDeltaBytesCap` etc.).  GC and arena
  fragmentation create real noise — these gates ride that noise and only
  fire on outliers.

Soft thresholds are intentionally NOT in `STABILITY_BENCH.yaml`: the spec
declares "the check must exist," the harness declares "the check passes at
threshold X."  When threshold X must change, `git diff` makes that visible.

### Why anon_inode FDs are excluded from `fd_count`

`/proc/self/fd` includes runtime-infrastructure FDs (eventfd, eventpoll,
timerfd, signalfd) the GHC RTS netpoller / Go scheduler / Python asyncio
loop allocate lazily based on workload.  Counting them defeats hard-zero
gating — the Go cgo runtime grows the eventpoll set during the measurement
window even when every Client is properly Closed.  Per AGENTS.md cat 25 /
26 / 27, the FD sub-check targets "a forgotten Close somewhere on the
FFI/file-loader path"; that means real resources (regular files, pipes,
sockets), not multiplexer machinery.  All three bindings filter
identically.

## Forward-revert verification

Each harness is forward-revert-verified.  To re-verify after a refactor:

1. **Static gate** — comment out one sub-check call in any harness
   (e.g., delete the `RTSState.refcount` line in
   `python/benchmarks/stability.py`).  Run
   `python3 tools/check_stability_bench.py` — expect exit 1 with a
   precise diagnostic naming the missing marker.  Restore the line; rerun;
   expect exit 0.
2. **Drift gate per binding** — introduce an intentional resource leak
   (e.g., open a file in setup, never close it).  Run the harness — expect
   exit 1 with `passed: false` on the `fd_count` sub-check showing the
   delta.  Remove the leak; rerun; expect exit 0.

## Where this fits in CI

The static grep gate (`tools/check_stability_bench.py`) is always-on:
* Shake `phony "check-stability-bench"`.
* `tools/run_ci.py` always-on offline enforcer (`check-stability-bench`).

The dynamic run (`tools/stability_run.py`) is opt-in:
* `tools/run_ci.py` opt-in `--stability` lane — set `ALETHEIA_STABILITY_CHECK=1` (or pass `--stability`).

A 1M-frame full run is ~5-10 min on a quiet host; the static gate is
sub-second.  Default-on the cheap one, default-off the expensive one.

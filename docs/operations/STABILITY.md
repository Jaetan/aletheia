# Long-Run Stability Bench

Procedure for running the per-binding long-run resource-leakage harnesses. AGENTS.md cat 16 / 25 / 26 / 27 mandate that a stability bench of ≥ 1M frames must run with no per-iteration drift on RSS / FD count / binding-specific resource accounting (`StablePtr` for Go, `RTSState` for Python, the process's thread count for C++) and emit a GHC RTS heap-typed profile so allocation behavior is recorded across the long-run window.

## Quick start

~~~bash
cabal run shake -- build
cmake --build cpp/build --target stability_bench  # C++ harness binary

# Default: 10 cycles × 100K frames per binding (= 1M total each), ~5-10 min.
ALETHEIA_STABILITY_CHECK=1 python/.venv/bin/python -m tools.stability_run
~~~

Artifacts land at `benchmarks/stability/<short-sha>/`:

~~~
python.json      Python harness verdict + delta per sub-check
go.json          Go harness verdict + delta per sub-check
cpp.json         C++ harness verdict + delta per sub-check
aletheia-ffi.hp  GHC RTS heap-typed profile (Agda cat 16)
summary.json     Aggregated verdict
~~~

`benchmarks/stability/` is gitignored: these are volatile per-run
artifacts.  The spec defining what each binding's harness MUST measure
lives at `docs/STABILITY_BENCH.yaml`; the static gate
`tools/check_stability_bench.py` (Shake target `check-stability-bench`,
an always-on offline enforcer in `tools/run_ci.py`) verifies every
(binding, sub_check) pair's `source_marker` is present in the file the row
reads: its `source_file`, or the binding's harness when it names none.

## Tuning the run

| Env var                       | Default | Effect                              |
| ----------------------------- | ------- | ----------------------------------- |
| `ALETHEIA_STABILITY_CYCLES`   | 10      | Outer cycles (Init/Close pairs)     |
| `ALETHEIA_STABILITY_FRAMES`   | 100000  | Inner frames per cycle              |
| `ALETHEIA_LIB`                | auto    | Override `libaletheia-ffi.so` path  |
| `ALETHEIA_RTS_OPTS` (Python)  | unset   | Extra RTS flags appended to argv at `hs_init_with_rtsopts` time; the runner sets `-hT` for the heap profile |

Every harness takes `ALETHEIA_STABILITY_CYCLES` and `ALETHEIA_STABILITY_FRAMES` as a whole number each from 1 to 2147483647, written in ASCII digits alone. Any other value, a sign, zero, an empty one and 2147483648 included, is refused with exit 2 and `<NAME> must be a whole number from 1 to 2147483647, got <value>` on stderr, never replaced by the default.

Smoke run for harness development (~30s):

~~~bash
ALETHEIA_STABILITY_CYCLES=2 ALETHEIA_STABILITY_FRAMES=1000 \
  python/.venv/bin/python -m tools.stability_run
~~~

> **Note on smoke-run heap profile.**  GHC's `-hT` heap profiler samples at
> 0.1s wall by default.  Smoke runs that finish under ~10s produce a
> nearly-empty `aletheia-ffi.hp` (≤ 100 samples), useful only as a
> file-existence smoke test for the env-var path, not for retention
> analysis.  Meaningful heap-shape inference needs ≥ 30s wall (≥ 300
> samples).  The default 10 cycles × 100K frames clears
> this comfortably; tune `ALETHEIA_STABILITY_FRAMES` upward when running
> short cycles to compensate (e.g. `CYCLES=2 FRAMES=200000` for a quick
> heap-profile capture).  Sample interval can be tightened via
> `ALETHEIA_RTS_OPTS="-hT -i0.01"` when you genuinely need finer grain.

## Exit codes

`tools/stability_run.py` archives each harness's stdout and reads its exit code: 0 and 1 are a verdict, read from the report, and any other code is a run with no verdict, whose stderr the summary quotes. Every harness exits with these codes:

| Code | Meaning |
| ---- | ------- |
| 0    | Every gate passed; the report is on stdout |
| 1    | A gate failed, as it does on a leak; the verdict is in the report on stdout |
| 2    | No verdict: a count variable is refused, a load or a cycle fails, a snapshot fails or the report cannot be written. stderr names the refused variable, carries the failed load's or cycle's error, or carries `the opening snapshot failed: <reason>`, `the closing snapshot failed: <reason>` or `writing the report failed: <message>` |

## Per-binding sub-checks

Spec is authoritative: see `docs/STABILITY_BENCH.yaml`.

### Python (cat 25)

| Sub-check         | Gate           | Source                                          |
| ----------------- | -------------- | ----------------------------------------------- |
| `rss`             | soft 50 MiB    | `psutil.Process().memory_info().rss`            |
| `fd_count`        | hard zero      | `/proc/self/fd` (anon_inode filtered)           |
| `ctypes_handles`  | hard zero      | `RTSState.refcount` after the final close, against its value after the warm-up |
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

Harness: `cpp/benchmarks/stability_bench.cpp`, its reads in `cpp/benchmarks/stability_snapshot.hpp` and its gates and report in `cpp/benchmarks/stability_report.hpp`.

### Agda (cat 16, GHC RTS heap profile)

The Python lane drives the RTS profile capture.  When invoked from
`tools/stability_run.py`, the runner sets `ALETHEIA_RTS_OPTS=-hT`; the
Python binding's runtime start, the first backend's `RTSState.acquire`,
extends the argv passed to `hs_init_with_rtsopts` with those flags.  The GHC RTS emits
`aletheia.hp` in the runner's cwd; the runner renames it to
`benchmarks/stability/<short-sha>/aletheia-ffi.hp`.

Time profiling (`-p`) requires a profiling-enabled `.so` rebuild (every
transitive Haskell dep compiled `-prof`); not enabled by default.  When
needed: rebuild with `--enable-profiling` and re-run with
`ALETHEIA_RTS_OPTS="-p -hT"`.

## Threshold model

Two tiers:

* **Hard zero**: exact equality after `Close()` + GC.  Any drift is a
  finding regardless of magnitude.  These are the genuine leak detectors.
* **Soft threshold**: empirically-tuned cap that lives next to the
  assertion in the harness source (search for `RSS_DELTA_BYTES_CAP`,
  `rssDeltaBytesCap`, `k_rss_delta_bytes_cap`, `k_malloc_delta_bytes_cap`).  GC and arena
  fragmentation create real noise; these gates ride that noise and only
  fire on outliers.

Soft thresholds are intentionally NOT in `STABILITY_BENCH.yaml`: the spec
declares "the check must exist," the harness declares "the check passes at
threshold X."  When threshold X must change, `git diff` makes that visible.

### Why anon_inode FDs are excluded from `fd_count`

`/proc/self/fd` includes runtime-infrastructure FDs (eventfd, eventpoll,
timerfd, signalfd) the GHC RTS netpoller / Go scheduler / Python asyncio
loop allocate lazily based on workload.  Counting them defeats hard-zero
gating: the Go cgo runtime grows the eventpoll set during the measurement
window even when every Client is properly Closed.  Per AGENTS.md cat 25 /
26 / 27, the FD sub-check targets "a forgotten Close somewhere on the
FFI/file-loader path"; that means real resources (regular files, pipes,
sockets), not multiplexer machinery.  All three bindings filter
identically.

## Forward-revert verification

Each harness is forward-revert-verified.  To re-verify after a refactor:

1. **Static gate**: delete one sub-check's read from the file its row reads (e.g., the `status_field(status, "VmRSS:")` call in `cpp/benchmarks/stability_snapshot.hpp`). Run `python/.venv/bin/python -m tools.check_stability_bench` from the repository root: expect exit 1 with a diagnostic naming the row and the file. Restore the line; rerun; expect exit 0. A marker is a substring, so a comment that carries it would pass the gate as the code does; every row's marker is spelled once in its file, as the code spells the read, held by `python/tests/test_check_stability_bench.py`.
2. **Drift gate per binding**: introduce an intentional resource leak
   (e.g., open a file in setup, never close it).  Run the harness: expect
   exit 1 with `passed: false` on the `fd_count` sub-check showing the
   delta.  Remove the leak; rerun; expect exit 0.

## Where this fits in CI

The static grep gate (`tools/check_stability_bench.py`) is always-on:
* Shake `phony "check-stability-bench"`.
* `tools/run_ci.py` always-on offline enforcer (`check-stability-bench`).

The dynamic run (`tools/stability_run.py`) is opt-in:
* `tools/run_ci.py` opt-in `--stability` lane: set `ALETHEIA_STABILITY_CHECK=1` (or pass `--stability`).

A 1M-frame full run is ~5-10 min on a quiet host; the static gate is
sub-second.  Default-on the cheap one, default-off the expensive one.

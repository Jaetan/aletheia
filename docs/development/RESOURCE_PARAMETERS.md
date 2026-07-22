<!--
SPDX-FileCopyrightText: 2025 Nicolas Pelletier
SPDX-License-Identifier: BSD-2-Clause
-->

# Runtime resource parameters — method & rationale

This is the method note behind [`docs/RESOURCE_BUDGETS.yaml`](../RESOURCE_BUDGETS.yaml),
the cross-binding single source of truth for the GHC RTS parameters every
binding passes to the loaded kernel's runtime. It explains what the numbers are
*for*, why the runtime cap is a fixed constant rather than a tuned figure, how to
re-measure the kernel's working set, and how to choose a new cap if a legitimate
workload ever outgrows the current one.

## The containment-by-abort contract (read this first)

The loaded kernel is compiled Agda running under the GHC runtime system. That
runtime has **no heap limit by default**, so a runaway allocation inside kernel
code is *not* a failed call — it keeps allocating until the host is out of
memory and the OS OOM killer takes the whole machine down. That happened twice
on this project while probing a kernel defect whose cost grew with a value's
magnitude.

The fix is a default heap cap (`-M3G`) passed to the RTS at startup in every
binding. When a computation exceeds the cap, GHC's heap-overflow check trips and
the foreign-export wrapper's `rts_checkSchedStatus` calls `stg_exit` on the
non-Success return. The consequence is precise, and it is the whole point:

> **The process TERMINATES. The host survives. There is no recoverable error.**

The terminating process prints a diagnostic
(`aletheia: aletheia_process: Return code (4) not ok` — GHC's HeapExhausted) and
exits non-zero. No catchable exception is raised, no partial result is returned,
and no binding installs a handler that could turn the abort into a value. Every
comment, doc, and test around this cap states it this way; describing the cap as
"returning an error" is wrong.

This is *containment*, not graceful degradation. It converts an
unbounded-blast-radius host failure into a bounded single-process failure — the
correct trade for a library embedded in someone else's process on a machine we
do not control.

## Containment bound vs. working-set budget

The two are different in kind, and the distinction governs how the number is
chosen:

* A **working-set budget** is tuned to a measured workload on a known machine:
  set it near the real peak plus a margin, and revisit it when the workload or
  the host changes. It is a *performance/capacity* knob.

* A **containment bound** is deliberately set *far above* any legitimate working
  set, low only relative to the host's total memory. Its only job is to catch a
  pathological runaway before it reaches the host. It is a *safety* backstop, not
  a capacity knob, so it does **not** track the workload.

`runtime.heap_cap` in the SSOT is a containment bound. `-M3G` sits far above the
heaviest kernel working set measured on this project (see below) and far below
any developer or CI host's RAM. Setting it *lower* (near the working set) would
be a mistake: it would abort legitimate heavy work. Setting it to track the
building host would be a worse mistake — the `.so` ships to machines we have
never seen, so the cap must be a fixed constant valid on all of them, not a
figure derived from whoever built it.

## Why the runtime cap is fixed, not host-derived

The runtime parameters ship to end users. A bundled binding on an unknown
machine cannot read `docs/`, and the cap must protect a 4 GiB embedded target and
a 512 GiB workstation identically. So the runtime tier is a **fixed containment
constant**, mirrored verbatim into each binding and pinned by
`tools/check_rts_runtime.py`. (Host-*tuned* knobs — the developer Agda
type-check heap, CI lane budgets — are a different category; a future `build:`
tier of the SSOT will hold those, and those *are* allowed to track the host.)

A process that genuinely needs a different cap overrides it per invocation with
the `ALETHEIA_RTS_OPTS` environment variable, whose flags are appended after the
default; the RTS honours the last occurrence of `-M`, so a caller-supplied cap
wins. That is the escape hatch — the shipped default stays fixed.

## Re-measuring the kernel working set

Choose a new cap from *measured* working sets, never a guess. The measurement is
the peak resident set of a child process that boots the kernel and runs the
workload in question. `/usr/bin/time -v` (which reports "Maximum resident set
size") is **not installed** in this environment, so measure with
`resource.getrusage(RUSAGE_CHILDREN)` around a subprocess instead — its
`ru_maxrss` is the child's peak RSS in KiB on Linux (illustrative — the
`text` tag keeps it out of the doc-example harness, which would try to run it):

```text
import resource
import subprocess
import sys

# Run the workload as a CHILD so RUSAGE_CHILDREN captures its peak, not the
# harness's.  Give the child a generous cap so it completes (we are measuring
# the working set, not tripping the containment bound).
subprocess.run(
    [sys.executable, "-m", "your_workload_module"],
    env={**__import__("os").environ, "ALETHEIA_RTS_OPTS": "-M8G"},
    check=True,
)
peak_kib = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
print(f"child peak RSS: {peak_kib / 1024:.1f} MiB")
```

For a GHC-specific figure, run the workload once under `ALETHEIA_RTS_OPTS=-s`
(the RTS statistics summary prints "maximum residency" and "total memory in
use") — that isolates the RTS heap from the interpreter/loader RSS that
`ru_maxrss` also counts.

Reference envelope measured on this project (a containment bound must sit
comfortably above the largest of these):

| Workload | Peak |
|---|---|
| Ordinary client use (parse a small DBC, stream frames) | ~0.1 GiB |
| Heaviest proof gate (`check-properties`) | ~1.5 GiB |
| `Main.agda` type-check | ~0.9 GiB |

`-M3G` leaves roughly a 2× margin over the heaviest observed working set while
remaining a small fraction of any host's RAM.

## Choosing a new cap

Only if a *legitimate* workload is shown to exceed the working sets above:

1. Reproduce the workload and measure its peak with the method above.
2. Confirm it is legitimate — a genuinely large DBC or long stream — and not a
   runaway the cap is *meant* to catch. A cost that grows without bound in the
   input's *magnitude* (rather than its size) is a kernel defect; fix that,
   don't raise the cap.
3. Pick a new cap at roughly 2× the measured legitimate peak, still far below a
   plausible host's RAM.
4. Edit `runtime.heap_cap` (`flag` and `bytes`) in
   [`docs/RESOURCE_BUDGETS.yaml`](../RESOURCE_BUDGETS.yaml), update the mirrored
   constant in all four bindings, and add a CHANGELOG entry (a runtime behaviour
   change is user-visible). `tools/check_rts_runtime.py` fails until the mirrors
   agree with the SSOT.

## Verifying the cap still has teeth

The behavioural tests (`python/tests/test_rts_runtime_parity.py`,
`go/aletheia/rts_heap_cap_test.go`, `cpp/tests/test_rts_heap_cap.cpp`,
`rust/tests/rts_heap_cap.rs`) each boot a real FFI client twice: once on the
default cap (which must boot and parse), and once under a tight
`ALETHEIA_RTS_OPTS=-M12M` cap over a large DBC, which must abort the process
(non-zero exit, no success sentinel). The abort is process-terminating, so those
tests run the workload out-of-process. If you change the cap or the init path,
those tests are the proof the containment still fires.

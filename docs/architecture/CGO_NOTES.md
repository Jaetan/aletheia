# CGO + GHC RTS interaction notes

This document covers what `libaletheia-ffi.so` does to a host process — the
constraints it imposes on Go's cgo toolchain and on C++/Python sanitizer
lanes — and the AGENTS.md cat 33a / 34a sanitizer scope decisions that
follow from those constraints.

This is a primary-source sanity check: the gaps described here are real
in the current codebase, not deferrals dressed as documentation. Each
gap names the binding-side correctness gate that compensates so the
overall coverage is preserved.

## What the .so contains

`libaletheia-ffi.so` is a Haskell shared library produced by GHC:

- The Glasgow Haskell Compiler runtime system (RTS) lives inside the .so.
  It owns its own thread pool, its own copying garbage collector, and a
  set of signal handlers (notably `SIGSEGV` for stack overflow and
  `SIGUSR1` / `SIGUSR2` for in-RTS messaging).
- One-time `hs_init` call sets up the RTS and registers the signal
  handlers; one-time `hs_exit` tears them down. The Aletheia bindings
  manage this through their `AletheiaClient` lifecycle (`__enter__` /
  `NewClient` / `make_ffi_backend`) and refcount across multiple clients
  in a single process.
- All FFI entry points (`aletheia_send_frame`, `aletheia_process_json`,
  etc.) marshal arguments into Haskell heap representations, run the
  Agda-compiled Haskell code, marshal the result back to a C-callable
  encoding, and return.

Once `hs_init` runs, the host process has both:

1. A foreign runtime owning its own threads and GC.
2. Foreign signal handlers that are not aware of the host's setup.

## Sanitizer interactions

### AddressSanitizer (ASan)

ASan instruments every load and store with shadow-memory checks. It assumes
exclusive control of:

- The signal handler set (it overrides `SIGSEGV` / `SIGBUS` / `SIGABRT`).
- Memory allocation (it interposes `malloc`/`free` and friends).
- Thread-local storage layout for the shadow map.

The GHC RTS clashes on each axis:

- **Signal handlers**: GHC's stack-overflow detector installs a `SIGSEGV`
  handler that ASan unconditionally replaces. A genuine RTS stack overflow
  (rare in our parsers, but possible on adversarial input) becomes an ASan
  crash with a misleading "use-after-poison" trace instead of a controlled
  RTS exception.
- **Memory allocator**: GHC uses its own block allocator (the "megablock"
  layout, `mmap` directly), so ASan does not see most heap traffic. False
  negatives on RTS-side bugs.
- **Shadow memory**: The RTS reserves large virtual address ranges for
  the heap's generational layout. On systems with restrictive `mmap`
  policies this can collide with ASan's shadow-memory map. We have not
  observed this in practice on Linux x86_64 6.x kernels but it has been
  reported in the wider ecosystem.

The resulting practical answer is: **ASan against test executables that
load `libaletheia-ffi.so` is unreliable**. It can be made to work by
rebuilding the `.so` with sanitizer instrumentation across the GHC
toolchain (a `bignum`-style rebuild project), but the engineering cost
exceeds the marginal coverage value.

### UndefinedBehaviorSanitizer (UBSan)

UBSan instruments arithmetic, conversions, and pointer derefs without
overriding the global allocator or signal handlers. It tolerates
foreign runtimes well — the GHC RTS can run inside a UBSan-instrumented
process without false positives.

UBSan therefore IS run against the full C++ test surface, including
the `integration_tests` and `cross_binding_integration_tests` targets
that load the .so. Coverage gap closure: signed-overflow / shift /
nullable-deref / misaligned-load UB on the C++ side is caught even when
the runtime path crosses the FFI boundary.

### ThreadSanitizer (TSan)

TSan instruments memory access for race detection. It conflicts with
GHC's RTS on similar grounds to ASan (its shadow-memory layout assumes
ownership of the entire address space). We do not run TSan against
test executables that load the .so. The C++-side concurrency primitives
(`std::mutex` on `Client::cache_`, `std::atomic` on `Logger::min_`) are
exercised by `unit_tests_concurrent`-style tests that are MockBackend-only
and CAN be TSan-instrumented; the `ALETHEIA_SANITIZER=thread` lane covers
them. The GHC RTS is internally race-free (it is single-threaded for our
single-N-cores RTS configuration), so the RTS-side coverage gap is not
load-bearing.

## Compiler requirement for the sanitizer lane

`-fsanitize-ignorelist=` is a clang-only feature; g++ has no equivalent
flag.  The sanitizer ignorelist at `cpp/sanitizer-ignorelist.txt`
filters out vendored third-party UB (notably `OpenXLSX/external/zippy/zippy.hpp`,
which performs unaligned `mz_uint32` loads on byte buffers — UB by the
C++ standard but harmless on x86_64).  Without the ignorelist, the
sanitizer lane reports OpenXLSX/zippy errors that aren't actionable on
the Aletheia side.

The canonical sanitizer-lane invocation therefore uses clang:

```
cmake -B build-ubsan -DALETHEIA_SANITIZER=undefined \
    -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
cmake --build build-ubsan
ctest --test-dir build-ubsan
```

`tools/run_ci.py`'s `ALETHEIA_SAN_CHECK=1` opt-in lane wires this
exactly.  When clang is unavailable, the sanitizer lane is unsupported
(documented here, not silently degraded) — the project's primary
compiler is g++ (per `project_cpp_compilers.md`); the sanitizer build
is a separate clang-driven artifact.

## Sanitizer lane decisions (R18 cluster 5, advisor option (d))

| Lane | Scope | Catches | Blind spot |
|---|---|---|---|
| ASan | `unit_tests_*` only (no `.so` load) | use-after-free, double-free, out-of-bounds, leak | C++ → FFI marshal path, GHC RTS internals |
| UBSan | every test target including `integration_tests` | signed overflow, shift UB, nullable deref, misaligned load | none on the C++ side |
| TSan | `unit_tests_*` only (no `.so` load) | data races on `Client::cache_`, `Logger::min_`, `RtsMismatchInfo` | RTS internals |

The blind spots are covered by:

- **C++ → FFI marshal path**: the Track D doc-example harness exercises
  every documented call path end-to-end against the real FFI. Coverage is
  behavioral (the documented example must produce the documented response)
  rather than memory-safety, but combined with the binding's per-method
  unit tests (which exercise the marshal layer with a mock backend that
  catches malformed inputs at the boundary), the closure on memory-safety
  bugs in the marshal code is reasonable.
- **GHC RTS internals**: GHC has its own test suite. Aletheia inherits
  RTS correctness from GHC's release process and pins the GHC version in
  `Shakefile.hs` for reproducibility (R18 cluster 3 reproducible-build).

## Go cgo specifics

Go's cgo extends the above concerns:

- Cgo calls run on a thread that is locked to the OS thread (`runtime.
  LockOSThread`); the Aletheia Go binding pins the construction thread
  via `lockOSThreadForRTSInit`.
- Cgo's calling convention copies arguments to C-compatible memory
  (Go strings → C strings, Go slices → C arrays). The slice copies are
  the natural defense against memory-safety bugs in the cgo boundary.
- ASan against cgo binaries is supported by the Go toolchain via
  `CGO_CFLAGS=-fsanitize=address GOFLAGS=-asan`, but the same RTS
  conflicts apply. The Go cat 33a decision is: ASan against the Go
  binding's `_test.go` files that use MockBackend only, not against
  tests that import the FFI backend.

The Go test runner does not currently expose a per-test ASan lane —
this is the cat 33a CI surface that cluster 5 has scoped explicitly.
The `tools/run_ci.py` orchestrator runs the C++ sanitizer lanes; the
Go counterpart is a build-tag-gated rebuild of the binding's test
binary, opt-in via `go test -tags=asan ./aletheia/`.

## Operator runbook reference

Sanitizer-discovered failures are catalogued in
[docs/operations/RUNBOOK.md](../operations/RUNBOOK.md) under
"Sanitizer-detected failures" — symptom + cause + action per lane,
mirroring the per-event entries from `docs/LOG_EVENTS.yaml`.

## When to revisit

- A new GHC release that changes RTS signal-handling or block-allocator
  layout. Re-test the ASan + .so combination if upstream advertises
  sanitizer-friendliness.
- A GHC bignum migration that produces a sanitizer-ready RTS as a
  byproduct (tracked under Phase 6's `--bignum=native` rebuild goal in
  PROJECT_STATUS.md). At that point the ASan-against-.so blind spot
  closes for free.
- A new C++ standard library / clang version that ships sanitizer
  improvements changing the cost calculus.

This document records the state as of R18 cluster 5 (2026-05-08). The
gaps named here are real and the compensating coverage is real; if
either drifts, update this document in the same commit as the change.

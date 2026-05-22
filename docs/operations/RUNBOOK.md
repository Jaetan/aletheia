# Aletheia Operations Runbook

Operator-facing reference for diagnosing log events and failure modes
emitted by Aletheia's Python / Go / C++ bindings against the verified
Agda kernel. Each entry is keyed on what an on-call operator actually
sees (a structured log line, an exception class, a build error) and
gives the likely cause plus the suggested next step.

This file is the canonical home for operational guidance per
[AGENTS.md § Universal Rules / cat 22](../../AGENTS.md). The structured
log-event taxonomy lives in [LOG_EVENTS.yaml](../LOG_EVENTS.yaml); the
protocol error codes live in
[PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference);
build / install troubleshooting lives in
[BUILDING.md § Troubleshooting](../development/BUILDING.md#troubleshooting);
cancellation semantics live in
[CANCELLATION.md](../architecture/CANCELLATION.md). The runbook
cross-references these — it does not duplicate them.

## Audience

On-call operators and integrators who deploy `libaletheia-ffi.so`
behind a Python / Go / C++ application. If you are debugging a build
or developing the kernel, prefer
[BUILDING.md](../development/BUILDING.md) and
[DESIGN.md](../architecture/DESIGN.md).

## How to use this runbook

1. Find your symptom — a log event name in § Log Events, or a build /
   runtime symptom in § Failure Modes.
2. Read the **Cause** entry to understand why it fired.
3. Run the **Action** entry. If the action does not resolve the
   symptom, escalate with the log line and the bound / error code.

Every event listed here is emitted by the Python / Go / C++ bindings
with the same name (the per-binding parity tests in
`python/tests/test_log_events_parity.py`,
`go/aletheia/log_events_test.go`, and
`cpp/tests/test_log_events_parity.cpp` enforce this). A regression
that drops or renames an event fails the build before reaching
production.

## Log Events

Sixteen structured log events are emitted by the bindings. Levels
(info / debug / warn) are the same in all three bindings; severity is
informational below and authoritative in
[LOG_EVENTS.yaml](../LOG_EVENTS.yaml).

### Lifecycle

#### `dbc.parsed`

**Symptom:** info-level log line at `parse_dbc` / `parse_dbc_text`
completion, carrying the parsed message / signal counts.

**Cause:** A DBC definition (Python `DBCDefinition` / Go `DBCDefinition` /
C++ `DbcDefinition`) was successfully loaded — either from the JSON-shape
command (`parseDBC`) or the DBC-text path (`parseDBCText`). Both paths emit
the same canonical event name.

**Action:** None. This is a normal lifecycle marker. If you expected
a higher message count, check for `extraction.parse_failed` or
`handler_validation_failed` lower in the log.

#### `properties.set`

**Symptom:** info-level log line at `set_properties` completion.

**Cause:** LTL properties were registered with the client. The client
is now ready for `start_stream`.

**Action:** None — normal. If properties are registered but never
fire on streaming frames, check the property's signal predicates
against the loaded DBC's signal names.

#### `stream.started`

**Symptom:** info-level log line at `start_stream` completion.

**Cause:** A streaming session was opened. The client is now in
streaming mode and accepts `aletheia_send_frame` calls until
`end_stream`.

**Action:** None — normal. If `frame.processed` events do not
follow, frames are not reaching the FFI; check the binding-side
producer.

#### `stream.ended`

**Symptom:** info-level log line at `end_stream` completion, carrying
the final result counts (acks, violations, errors).

**Cause:** The streaming session closed normally.

**Action:** None — normal. Compare the result counts against
expectations; investigate any `extraction.process_failed` /
`enrichment.*` warnings emitted during the session.

#### `rts.cores_mismatch`

**Symptom:** warn-level log line at `make_ffi_backend(path, rts_cores)`
(C++) / `WithRTSCores(N)` (Go) / RTS-init equivalent (Python),
emitted once per subsequent mismatching call.

**Cause:** GHC RTS init was requested with a core count that
disagrees with an earlier process-wide init. The first call wins —
the GHC RTS can only be initialised once per process.

**Action:** Audit the process for multiple Aletheia clients with
different `rts_cores`. The fix is to standardise on one value at the
process entry point and pass the same value to every subsequent
client. If the warning fires from a third-party library that also
uses GHC, this is a host-application coordination issue and the
warning is informational only.

### Frame processing

#### `frame.processed`

**Symptom:** debug-level log line per frame inside a streaming
session, carrying the response classification (ack, violation, etc.).

**Cause:** The Agda kernel processed a frame submitted via
`aletheia_send_frame`.

**Action:** None — normal. Volume can be high; consider raising the
binding logger level above DEBUG in production. Use this signal to
correlate per-frame outcomes when investigating a violation cluster.

#### `error_event.sent`

**Symptom:** debug-level log line per CAN error frame submitted via
`send_error`.

**Cause:** The host application reported a bus-error event via the
binary entry point. Aletheia records the timestamp; LTL properties
that consume error events advance their coalgebras.

**Action:** None — normal in any session that monitors bus errors.

#### `remote_event.sent`

**Symptom:** debug-level log line per CAN remote frame submitted via
`send_remote`.

**Cause:** The host application forwarded a CAN remote (RTR) frame.
Aletheia records the (timestamp, can_id, extended) triple.

**Action:** None — normal.

### Enrichment diagnostics

#### `enrichment.property_index_oob`

**Symptom:** warn-level log line, no associated `frame.processed` ack.

**Cause:** A violation referenced a property index outside the
registered set. The property registry has shrunk between
`set_properties` and `start_stream`, or the binding emitted a stale
violation against a now-gone property. The violation record is
dropped; the stream continues.

**Action:** Audit `set_properties` calls in the host application
— properties should be registered once before `start_stream` and not
rotated mid-stream. If this fires repeatedly, the property registry
is being mutated concurrently with streaming.

#### `enrichment.extraction_failed`

**Symptom:** warn-level log line, no enrichment data on the
violation.

**Cause:** Signal extraction for violation enrichment did not return
a result for the frame. Common causes: the violating frame's CAN ID
is not in the loaded DBC, or the signal referenced by the predicate
exists in the DBC but its bits do not fit the frame's payload (DLC
mismatch).

**Action:** Cross-check the violating predicate against the DBC's
message and signal definitions for the violating CAN ID. If the
predicate is correct, the frame is malformed; if the predicate is
wrong, fix the property.

### Extraction cache

#### `cache.hit`

**Symptom:** debug-level log line during signal extraction.

**Cause:** Extraction served a cached signal value (the same
(can_id, signal_name) pair was seen recently and the result is
cached).

**Action:** None — normal and desirable. High `cache.hit` /
`cache.miss` ratio is the steady-state on a typical CAN log.

#### `cache.miss`

**Symptom:** debug-level log line during signal extraction.

**Cause:** Extraction missed the LRU cache and called through to the
Agda core for the (can_id, signal_name) lookup.

**Action:** None — normal. Sustained high miss rate suggests the
working set exceeds the cache capacity; consider whether the host
application is iterating over many distinct messages or whether the
cache is being thrashed.

#### `cache.full`

**Symptom:** warn-level log line during signal extraction; the
record carries the current cache size in the `size` field.

**Cause:** The signal-extraction cache reached its capacity bound
(`MAX_EXTRACT_CACHE = 256` in Python `_types.py`, `maxExtractCache`
in Go `enrich.go`, `max_cache_size` in C++ `client.hpp`). The
extraction itself succeeded; the warning is purely informational
about cache pressure.

**Action:** None for correctness. Once full the cache stops
admitting new (can_id, signal_name) pairs — it does not evict —
which means each fresh signal extraction past the cap pays the full
kernel-call cost. If the warning fires on every frame, the working
set legitimately exceeds 256 distinct (can_id, signal_name) pairs;
the cap is a compile-time constant in each binding and would need a
binding-side patch to lift.

### Extraction errors

#### `extraction.process_failed`

**Symptom:** warn-level log line, no extraction result for the frame.

**Cause:** An extraction request failed at the FFI process boundary
— the kernel call returned an error response. This is most often a
transient FFI marshaling fault rather than a kernel bug.

**Action:** Inspect the structured `reason` field. If it is a
`route_*` or `handler_*` error code, see
[PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference).
If it persists across many frames, restart the host process — the
GHC RTS may have entered a degraded state.

#### `extraction.parse_failed`

**Symptom:** warn-level log line, no extraction result for the frame.

**Cause:** An extraction response could not be parsed by the binding
(malformed JSON or schema violation). The kernel produced output the
binding does not recognise.

**Action:** This indicates a binding / kernel version mismatch.
Verify `python -m aletheia --version` (or equivalent) matches the
loaded `libaletheia-ffi.so` build. The fix is usually a clean
rebuild: `cabal run shake -- clean && cabal run shake -- build`,
followed by a binding reinstall (`pip install -e python` for Python).

### End-of-stream diagnostics

#### `endstream.uncached_atom`

**Symptom:** warn-level log line emitted from `end_stream` /
`EndStream` / `end_stream`, one per warning the kernel carried on the
`Complete` response; the structured record fields are
`property_index` (integer) and `detail` (string — usually the
unobserved signal name). The aggregate `stream.ended` event's
`numWarnings` attribute equals the number of these per-warning records.

**Cause:** The verified kernel walked every registered property's
atoms at end-of-stream and found at least one atom whose target
signal was never observed by the cache during the stream. The
property's verdict is `Unresolved` — the kernel correctly refuses to
satisfy or refute an `Always (atom)` it never had data for. The
warning ratifies the verdict with diagnostic context (which property,
which signal) so operators can grep for specific properties.

**Action:** Investigate why the signal was absent. Common causes:
- The property's predicate references a signal name that exists in
  the DBC but is on a message the stream never carried (mux-only,
  filtered upstream, or producer ECU silent for the session).
- The signal is on a multiplexed branch that never won the mux
  selector during the stream.
- The stream is shorter than the warm-up window for a slow-cadence
  message.

If the absence is expected for the workload (e.g., the property
guards a fault path the test session deliberately avoided), the
`Unresolved` verdict is the correct outcome and the warning is
informational. If the absence is a surprise, cross-check the
property's signal name against the DBC (`dbc_queries`
`signal_by_name` returns the message that hosts a given signal) and
the producer side of the bus.

## Failure Modes

These are operator-visible failures that may or may not carry a
log-event entry above. Each is keyed on the symptom rather than an
event name.

### Build / deployment

#### `hs_init` failure / `aletheia_init() returned null`

**Symptom:** Process startup fails with an `hs_init` error or the
client constructor returns a null backend.

**Cause:** The loaded `libaletheia-ffi.so` was built against a
different GHC version than the one currently linked into the
process, or a stale copy is shadowing the intended one in
`$LD_LIBRARY_PATH`.

**Action:** Rebuild against the canonical toolchain
(`cabal run shake -- build`) and confirm only one `libaletheia-ffi.so`
exists on the loader path. The Python loader checks
`_install_config.LIBRARY_PATH` first, then `LD_LIBRARY_PATH`, then
`/usr/local/lib`; override with `ALETHEIA_FFI_PATH=/abs/path/to/...`.

#### `.so` load failure

**Symptom:** `FileNotFoundError: libaletheia-ffi.so not found`
(Python) / `dlopen` failure (Go) / `make_ffi_backend(...)` throws
(C++) at client construction.

**Cause:** The binding loader could not resolve `libaletheia-ffi.so`
on its search path.

**Action:** Either run `cabal run shake -- install` to copy the `.so`
into the configured library path, or set `ALETHEIA_FFI_PATH` /
`LD_LIBRARY_PATH` to the directory containing the build artifact.
See [BUILDING.md § Python Can't Find Shared Library](../development/BUILDING.md#python-cant-find-shared-library).

#### ctypes signature mismatch (Python)

**Symptom:** Segfault or `OSError` on the first FFI call against an
otherwise-loadable `.so`.

**Cause:** The Python `aletheia` package and the loaded
`libaletheia-ffi.so` were built from different commits — function
signatures (argtypes / restype) drifted relative to the kernel
exports.

**Action:** Compare `python -m aletheia --version` against
`strings libaletheia-ffi.so | grep aletheia-ffi-`. Reinstall the
matching pair: `cabal run shake -- build && pip install -e python`.

#### MAlonzo symbol not found at FFI load time

**Symptom:** The library loads, but the first call crashes with
`Prelude.undefined` or a missing symbol like `_d_processJSONLine_*`.

**Cause:** MAlonzo (Agda's Haskell backend) mangles top-level
definition names with a numeric suffix that depends on declaration
order in `Main.agda`. Adding or removing a top-level definition
shifts the suffix.

**Action:** Rebuild — `cabal run shake -- build` prints the exact
`sed` command to update `haskell-shim/src/AletheiaFFI.hs` whenever
mangling drifts. Apply it, rebuild, and the FFI surface converges.

#### `ld: cannot find -lgmp` at link time

**Symptom:** `cabal build` fails at link time on a fresh machine.

**Cause:** Haskell uses GMP for arbitrary-precision integers. The
system `libgmp-dev` is missing.

**Action:** Install `libgmp-dev` (Debian/Ubuntu) / `gmp-devel`
(Fedora) / `gmp` (Arch / brew) and rebuild. See
[BUILDING.md § Missing libgmp](../development/BUILDING.md#missing-libgmp-ld-cannot-find--lgmp).

#### Go build with `CGO_ENABLED=0`

**Symptom:** Distroless or static-binary build fails with
`undefined: C.dlopen`.

**Cause:** The Go binding's `FFIBackend` requires cgo — there is no
pure-Go fallback for `dlopen`/`dlsym` on `libaletheia-ffi.so`.

**Action:** Build with `CGO_ENABLED=1` (the default) and ship
`libaletheia-ffi.so` alongside the binary. For tests that do not
need the FFI backend, `MockBackend` is pure Go and works under
`CGO_ENABLED=0`.

### Runtime — input bounds (`input_bound_exceeded`)

#### `input_bound_exceeded`

Post R19 cluster 14 / AGDA-C-6.2 consolidation 2026-05-11: the three
previously-split codes (`parse_input_bound_exceeded` /
`dbc_text_input_bound_exceeded` / `frame_input_bound_exceeded`) merged
into a single `input_bound_exceeded` code; discriminate by the
`bound_kind` field on the structured payload.

**Symptom:** Any command (JSON-shape `parseDBC` / `setProperties` /
binary `aletheia_send_frame` / `parse_dbc_text`) returns
`{"status": "error", "code": "input_bound_exceeded", "bound_kind": "...", ...}`,
or the binding raises `aletheia.InputBoundExceededError` (Python) /
`*aletheia.InputBoundExceededError` (Go) / throws
`aletheia::InputBoundExceededError` (C++).

**Cause:** An input exceeded one of the limits in
[PROTOCOL.md § Limits](../architecture/PROTOCOL.md#limits).  The
`bound_kind` field names which bound:
- `input_length_bytes` — JSON or DBC-text input exceeded `max_json_bytes`
  / `max_dbc_text_bytes` (64 MiB) at the FFI entry.
- `nesting_depth` — JSON nesting exceeded `max_nesting_depth` (64).
- `array_cardinality` — a list exceeded its per-section cardinality
  cap (`max_messages_per_file`, `max_signals_per_message`,
  `max_attributes_per_file`, `max_value_descriptions_per_file`).
- `identifier_length` — a DBC identifier exceeded
  `max_identifier_length` (128 chars).
- `string_length` — a quoted-string body exceeded
  `max_string_length_bytes` (64 KiB).
- `atom_count` — an LTL property exceeded
  `max_atom_count_per_property` (1024 atoms).
- `frame_byte_count` — a frame payload exceeded
  `max_frame_byte_count` (64 — CAN-FD maximum).  Structurally
  impossible for a valid CAN / CAN-FD frame; indicates a
  binding-side encoding bug (check the producer's DLC-to-bytes
  mapping; valid table is `{0..8, 12, 16, 20, 24, 32, 48, 64}` for
  DLC values `0..15`).

**Action:** Read the `bound_kind` / `observed` / `limit` fields on
the typed error to identify which bound was crossed. If the input is
legitimately oversize, see
[PROTOCOL.md § Updating bounds](../architecture/PROTOCOL.md#updating-bounds)
— bounds are intentionally generous (~6× headroom for commercial
DBCs; commercial automotive DBCs are typically 1-10 MiB) and
adjustments are a kernel + per-binding mirror change. If the input
is a synthetic stress test or unexpected user data, this is the
correct rejection.

### Runtime — OOM / heap pressure

#### Heap-cap exceeded mid-parse

**Symptom:** Process aborts with `Heap exhausted` or similar GHC RTS
diagnostic during a parse-heavy operation. The kernel was invoked
with a heap cap (e.g., `+RTS -M16G -RTS`) and ran out of room before
producing output.

**Cause:** A pathological input stresses the Agda parser
elaboration. Most commonly seen during type-checking (`agda` invoked
with `-M16G` per CLAUDE.md), not at runtime — the runtime kernel is
size-bounded by the input bounds above.

**Action:** Type-check the offending Agda module by itself with the
canonical `agda +RTS -N32 -M16G -RTS` invocation; raise the cap only
if the module is known to need it. At runtime, an `InputBoundExceeded`
fires before heap exhaustion in normal usage; an OOM signals either
a missing bound check or a pathological internal allocation pattern
that needs investigation rather than a config bump.

#### GHC RTS allocation failure

**Symptom:** Process aborts with `internal error: scavenge_block` or
similar GHC RTS internal diagnostic.

**Cause:** The GHC RTS hit an allocator-internal limit. This is a
runtime defect — Aletheia clients should not see this in normal
operation.

**Action:** Capture the RTS diagnostic plus the input that triggered
it and file a kernel bug. As a workaround, restart the host process;
the RTS state is per-process and a fresh process recovers.

#### Runaway cache growth

**Symptom:** Process RSS grows over a long-running streaming session
without `cache.full` warnings firing at expected cadence.

**Cause:** A binding-side state accumulator (typically a
host-application list of `Violation` records) is growing unbounded.
The kernel's signal-extraction cache is bounded — if `cache.full`
fires repeatedly, the kernel cache is doing its job.

**Action:** Audit binding-side data structures for accumulation. The
kernel is `O(1)` in trace length per
[PROJECT_STATUS.md § Key Metrics](../../PROJECT_STATUS.md#key-metrics);
runaway memory is host-application-side. Re-run the throughput
benchmarks (`benchmarks/run_all.sh --bench throughput`) and watch
RSS — kernel allocations are bounded; host-application leaks are
not.

### Runtime — DBC validation rejection

#### `handler_validation_failed` on `parse_dbc`

**Symptom:** `parse_dbc` returns
`{"status": "error", "code": "handler_validation_failed", ...}`.

**Cause:** The DBC failed validation at parse time. Validation
issues — duplicate message IDs, unknown signal receivers, missing
attribute definitions, unresolved value descriptions, etc. — are
codified in `Aletheia.DBC.Validator`.

**Action:** Run `aletheia validate --dbc <file>` (or the binding
equivalent) to enumerate issues. Each issue carries a stable
`IssueCode` mapped across all three bindings — see the
`IssueCode` enum (`python/aletheia/issue_codes.py`,
`go/aletheia/result.go`, `cpp/include/aletheia/validation.hpp`).
Warnings (e.g., `UnknownSignalReceiver`, `UnknownValueDescriptionTarget`)
do not block parse; errors do.

### Runtime — cancellation

See [CANCELLATION.md](../architecture/CANCELLATION.md) for the full
contract; this section captures the operator-visible symptoms.

#### Mid-stream cancellation produces a partial result

**Symptom:** A streaming or batch operation returns early with the
binding's cancellation type (Python `asyncio.CancelledError`,
Go `ctx.Err()`, C++ `ErrorKind::Cancellation`) plus a committed
prefix of frame results.

**Cause:** The caller cancelled — a context deadline expired, a stop
token was requested, or an asyncio task was cancelled.

**Action:** This is normal cancellation behaviour. The committed
prefix represents real work — every frame in it advanced the
kernel's coalgebras, signal caches, and timestamp registry. If you
need to resume, send the uncommitted suffix to the same client; if
you need to start over, call `end_stream()` + `start_stream()` to
reset state.

#### Mid-batch error wins over concurrent cancellation

**Symptom:** A batch is reported as failed with a real error (e.g.,
non-monotonic timestamp) even though the caller had cancelled before
that error fired.

**Cause:** Per
[CANCELLATION.md § 5.2](../architecture/CANCELLATION.md#52-mid-batch-error-vs-cancellation),
errors are primary signals about data integrity and override
concurrent cancellations. The batch reports the error with the
committed prefix; the cancellation never fires because the loop
terminated first.

**Action:** Check the returned error type — cancellation produces
`ctx.Err()` / `CancelledError` / `ErrorKind::Cancellation`; a real
error produces a binding-specific error type. If you observed both,
the error is the actionable signal; the cancellation was just
pre-empted.

#### Deadline exhaustion on a long-running operation

**Symptom:** A `parseDBC` / `parseDBCText` / `validateDBC` returns
the cancellation error after roughly the deadline you set, without a
committed prefix.

**Cause:** These commands are not frame-by-frame and have no commit
prefix. They cancel only when the underlying FFI call yields, which
happens before each new command but not partway through one. A
strict deadline shorter than a single command's wallclock is
indistinguishable from a hung call.

**Action:** Size the deadline against the largest expected single
command's wallclock — DBC parses on a 10 MiB file run in under a
second; an operation that is consistently overrunning is a kernel
performance issue, not a deadline-too-short issue. Consider whether
the input is legitimately oversize (see § InputBoundExceeded).

#### Cancellation while waiting for the Go Client lock

**Symptom:** A goroutine on a `*Client` operation returns
`ctx.Err()` immediately without ever invoking the FFI.

**Cause:** Go's `Client` is goroutine-safe via a channel-based
ctx-aware lock. A goroutine cancelled while *waiting* for the lock
returns immediately without acquiring it (see
[CANCELLATION.md § 5.3](../architecture/CANCELLATION.md#53-concurrent-cancellation-in-go)).

**Action:** This is normal behaviour and structurally cleaner than
`sync.Mutex.Lock()` would be. The cancelled goroutine never reaches
the kernel — no state was touched.

## See also

- [LOG_EVENTS.yaml](../LOG_EVENTS.yaml) — canonical 16-event vocabulary.
- [PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)
  — every wire-level error code, grouped by domain.
- [PROTOCOL.md § Limits](../architecture/PROTOCOL.md#limits) —
  adversarial-input bound table.
- [BUILDING.md § Troubleshooting](../development/BUILDING.md#troubleshooting)
  — exhaustive build / install error catalogue.
- [CANCELLATION.md](../architecture/CANCELLATION.md) — cooperative
  cancellation contract across the three bindings.
- [DESIGN.md](../architecture/DESIGN.md) — three-layer architecture.

## Versioning

This runbook is the operator-facing surface of the contracts above.
Adding, removing, or renaming a structured log event in
`LOG_EVENTS.yaml` requires updating this file in the same change;
`tools/check_runbook_coverage.py` enforces this mechanically. The
gate fails any commit that emits an event the runbook does not
explain.

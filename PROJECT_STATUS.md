# Aletheia Project Status

**Last Updated**: 2026-03-27

---

## Current Position

**Phase 4 - Production Hardening** ✅

Phases 1-4 complete. Phase 4 made Aletheia usable by non-developers
(automotive technicians, test engineers) and production-ready for deployment.

**Status**: Phase 4 complete

**Latest Release**: v1.0.0 (Phase 4 complete)

---

## Project Phases

### Phase 1: Core Infrastructure ✅ COMPLETE

**Scope**: Build the foundational formally verified components

**Delivered**:
- Parser combinators with structural recursion
- CAN signal encoding/decoding (variable-length frames via CAN-FD, 11-bit IDs)
- DBC parser (JSON format)
- Build pipeline (Agda → Haskell → Python)
- Basic protocol integration (Echo, ParseDBC, ExtractSignal, InjectSignal)
- Python wrapper

**Status**: 100% Complete

---

### Phase 2A: LTL Core + Real-World Support ✅ COMPLETE

**Scope**: Add Linear Temporal Logic verification and extended CAN support

**Delivered**:
- LTL syntax (Always, Eventually, Until, Next, And, Or, Not, Atomic)
- Coinductive and bounded trace semantics
- Signal predicates (Equals, LessThan, GreaterThan, Between, ChangedBy)
- Model checker with decidable comparisons
- Extended 29-bit CAN ID support
- Signal multiplexing (Always | When conditions)
- Python LTL DSL

**Status**: 100% Complete

---

### Phase 2B: Streaming Architecture ✅ COMPLETE

**Scope**: Streaming protocol with O(1) memory and production-ready Python API

**Delivered**:

**Phase 2B.1 - Core Protocol**:
- JSON streaming protocol (line-delimited, bidirectional)
- Message router (command/data routing)
- Command handlers (parseDBC, setProperties, startStream, endStream)
- StreamState validation
- Haskell I/O shim
- Python AletheiaClient (FFI via ctypes)

**Phase 2B.2 - Streaming LTL**:
- Incremental LTL evaluation (O(1) memory)
- Coinductive streaming interface
- Frame modification mid-stream
- Throughput: 9,229 fps (108 us/frame via FFI; improved to 9,704 fps after Rosu simplification)

**Phase 2B.3 - Polish**:
- Counterexample generation with violation details
- Rich error messages
- Python DSL refinement
- Performance tuning (parallel GHC)
- Comprehensive documentation

**Extension - Signal Operations**:
- AletheiaClient: Unified client with streaming + signal operations
- Build/update CAN frames with multiple signals
- Extract all signals with partitioned results
- Rich result objects (values/errors/absent signals)

**Status**: 100% Complete

---

### Phase 3: Verification + Performance ✅ COMPLETE

**Scope**: Formal correctness proofs and performance optimization

**Goals** (6 total):
1. ✅ Parser soundness proofs - COMPLETE
   - `Parser/Properties.agda`: 30 proven properties (monad laws, position tracking, parse determinism)
   - `Protocol/JSON/Properties.agda`: 12 proven properties (schema soundness, lookup correctness)
2. ✅ LTL semantics correctness proofs - COMPLETE
   - `LTL/Adequacy.agda`: Adequacy theorem proving `stepL` correct against denotational LTLf semantics
   - All 13 operators proven sound (four-layer proof structure, 1,061 lines)
   - `LTL/Semantics.agda`: Denotational LTLf semantics (`⟦_⟧`)
   - No postulates, pure coalgebraic reasoning
3. ✅ CAN encoding correctness proofs - COMPLETE
   - `Data/BitVec/Conversion.agda`: bitVec-roundtrip and bitVecToℕ-bounded (no postulates!)
   - `CAN/Endianness.agda`: extractBits-injectBits-roundtrip, injectBits-preserves-disjoint, injectBits-commute
   - `CAN/Encoding.agda`: injectSignal-preserves-disjoint-bits (key structural lemma)
   - `CAN/Batch/Properties.agda`: injectAll-preserves-disjoint (batch operations preserve extraction)
   - Note: Same byte order required for batch proofs; mixed byte order research in Phase 5
4. ✅ DSL translation correctness proofs - COMPLETE
   - `LTL/JSON/Format.agda`: formatSignalPredicate, formatLTL, ltlDepth functions
   - `LTL/JSON/Properties.agda`: Roundtrip and completeness proofs
   - Proven: parseLTL (ltlDepth φ) (formatLTL φ) ≡ just φ
5. ✅ Three-valued signal semantics - COMPLETE
   - `LTL/SignalPredicate.agda`: TruthVal (True/False/Unknown/Pending), Kleene logic, SignalCache
   - `LTL/Incremental.agda`: Inconclusive state, safety vs liveness semantics
   - `LTL/Coalgebra.agda`: Mirrored Inconclusive handling for adequacy proof
   - Key improvement: No frame filtering needed - Unknown signals continue monitoring
6. ✅ Performance optimization - COMPLETE
   - Target: 8,000 fps (125 us/frame for 1 Mbps CAN bus)
   - Achieved: 9,704 fps (103 us/frame) — 3.03x speedup (initially 9,229 fps; improved after Rosu simplification)
   - Steps: GHC compiler flags, Fin→ℕ elimination, FFI shared library (eliminated IPC)

**Status**: Complete (started 2025-12-17)
**Completion**: 100% (6/6 goals complete)

---

### Phase 4: Production Hardening ✅ COMPLETE

**Scope**: Make Aletheia usable by non-developers and production-ready for deployment

**Design principle**: Four tiers of user interface, all compiling to the same
verified core:

| Tier | User | Interface |
|------|------|-----------|
| Excel | Technician | Fill in numbers in spreadsheet templates, press Run |
| YAML | Test engineer | Edit declarative config files (version-controllable, CI/CD) |
| Check API | Scripter | `Check.signal("Speed").never_exceeds(220)` |
| DSL | Developer | `Signal("Speed").less_than(220).always()` (full LTL) |

**Goals** (11 total):

1. ✅ Check API — high-level property library (`python/aletheia/checks.py`) — COMPLETE
   - 6 simple conditions: `never_exceeds`, `never_below`, `stays_between`, `never_equals`, `equals`, `settles_between`
   - 3 when/then trigger/response patterns with `.within(ms)` deadline
   - Fluent API: `Check.signal("Speed").never_exceeds(220)` returns `CheckResult`
   - Metadata: `.named()` and `.severity()` chainable setters
   - Industry vocabulary: no LTL knowledge required

2. ✅ YAML loader (`python/aletheia/yaml_loader.py`) — COMPLETE
   - Declarative check definitions in YAML files
   - Schema: signal + condition + value/min/max + within_ms + severity
   - Supports simple checks and when/then response-time checks
   - `load_checks()` accepts file path or inline YAML string
   - Clear error messages referencing check names

3. ✅ Excel loader (`python/aletheia/excel_loader.py`) — COMPLETE
   - `load_dbc_from_excel()`: DBC definitions from spreadsheet (hex/decimal message IDs, multiplexed signals)
   - `load_checks_from_excel()`: Simple checks + when/then checks from two sheets
   - `create_template()`: Generates blank .xlsx with bold headers and three sheets (DBC, Checks, When-Then)
   - Row-level error messages, openpyxl type stubs for strict type checking
   - Dependency: `openpyxl>=3.1` (added to pyproject.toml)

4. ✅ CLI tool (`python -m aletheia`) — COMPLETE
   - `aletheia check` — run checks from YAML/Excel against a CAN log file
   - `aletheia extract` — extract signals from a single frame
   - `aletheia signals` — list signals in a DBC (or Excel)
   - `aletheia validate` — validate DBC for structural issues
   - Exit codes: 0=pass, 1=violations, 2=error; `--json` flag for structured output
   - 41 tests (pure-Python + FFI integration)

5. ✅ CAN log reader (`python/aletheia/can_log.py`) — COMPLETE
   - `load_can_log()` (eager) and `iter_can_log()` (lazy iterator) via `python-can`
   - Supports ASC, BLF, CSV, candump .log, MF4, TRC with auto-detection
   - Returns `tuple[int, int, int, bytearray]` (timestamp, CAN ID, DLC, data) — feeds directly to `send_frame()`
   - Full public API migrated from `list[int]` to `bytearray`
   - DLC-aware normalization: pads/truncates data to DLC byte count
   - Options: `skip_error_frames`, `skip_remote_frames`, `on_error`

6. ✅ Richer violation diagnostics — COMPLETE
   - `CheckResult` carries `signal_name` and `condition_desc` from all builders
   - `AletheiaClient.send_frame()` auto-enriches violations: extracts signal value, builds human-readable reason
   - Bounded extraction cache (256 unique frames) keeps throughput above 8,000 fps target
   - `PropertyViolationResponse` extended with `signal_name`, `actual_value`, `condition` fields
   - CLI and all consumers get enriched violations for free via client-level enrichment

7. ✅ Deployment guide + install/uninstall — COMPLETE (Shakefile, `cabal run shake -- install`)

8. ✅ Tutorial / cookbook — COMPLETE (`docs/guides/TUTORIAL.md`, `docs/guides/COOKBOOK.md`, `docs/guides/QUICKSTART.md`)

9. ✅ DBC Validator — COMPLETE
   - Agda: `DBC/Validator.agda` (new), `DBC/Types.agda`, `Protocol/Message.agda`, `Protocol/Routing.agda`, `Protocol/StreamState.agda`
   - `validateDBCFull : DBC → List ValidationIssue` — 16 checks (9 error, 7 warning), all issues accumulated
   - `IssueCode` enum: 16 codes covering structural, physical, and authoring issues
   - Decidable types throughout (`_≟-CANId_`, `any?`, `_∈?_`, `signalPairValid?`)
   - Dual-layer validation: `parseDBC` runs both `validateDBC` + `validateDBCFull`
   - **Formally verified**: soundness + completeness proof (1,267 lines, 6 modules)
   - Python: `client.validate_dbc()`, `cli validate` subcommand
   - 372 total tests pass, 0 regressions

10. ✅ Signal staleness bug demo — COMPLETE
    - Engine ECU freeze scenario: FrameCounter counter frozen
    - Demo files: `engine_ecu_sim.py`, `test_engine_naive.py`, `demo_ltl_bug.py`
    - 8 naive unit tests that pass against buggy ECU ✓
    - Aletheia LTL catches 34 frozen alive counter violations ✓

11. ✅ Default properties + `add_checks()` API — COMPLETE
    - `AletheiaClient(default_checks=[...])` constructor param
    - `add_checks()` merges defaults + session checks atomically
    - `--defaults` CLI argument wired in `_cmd_check()` via `_load_defaults()`
    - `_run_checks()` accepts `default_checks` param, uses `add_checks()`
    - 9 FFI integration tests in `test_default_checks.py`, all pass

**End-of-stream property finalization** ✅ COMPLETE
- Added Bool resolved flag to safety operators (Always, Release, MetricAlways, MetricRelease)
- `finalizeEval : LTLEvalState → FinalVerdict` determines Holds/Fails at end-of-stream
- `handleEndStream-State` calls `finalizeEval` on each property
- `Response.Complete` now carries `List PropertyResult` with per-property verdicts
- 7 integration tests verify all finalization behaviors
- Renamed `ThreeVal` → `TruthVal` (now 4 constructors: True, False, Unknown, Pending)

**Documentation**: Interface Guide (`docs/reference/INTERFACES.md`) with Check API, YAML, and Excel
end-to-end workflows. Cross-linked from README, INDEX, and Python API Guide.

**Demos**: 11 demo scripts + data files in `examples/demo/` (see [Documentation Index](docs/INDEX.md#examples) for full listing)

**Presentation**: `docs/presentation/index.html` — 36-slide reveal.js deck for product council (1 hour + Q&A)

**Status**: Complete (2026-02-06 to 2026-02-22)
**Completion**: 100% (11/11 goals complete)

---

### Streaming Verification Gaps 🔍 TRACKED

Comprehensive audit of all bisimilarity and streaming proofs identified 6 gaps.
Ordered by impact descending; within same impact, easiest to hardest.

| # | Gap | Impact | Difficulty | Status |
|---|-----|--------|------------|--------|
| A | `init-relate`: prove `initState φ` relates to initial `LTLProc` | HIGH | EASY | ✅ Complete |
| B | Multi-step composition: N-frame induction over `step-bisim` | MEDIUM | MODERATE | ✅ Complete |
| C | StreamState `handleDataFrame` iteration logic verification | MEDIUM | HARD | ✅ Complete |
| F | Satisfied/Violated terminal state idempotence | LOW | EASY | ✅ Complete |
| E | Signal predicate evaluation trust boundary (documentation) | LOW | BY DESIGN | ✅ Complete |
| D | Semantic grounding against denotational LTL semantics | LOW | RESEARCH | ✅ Complete (adequacy theorem — all 13 operators type-check) |

**Current proof coverage** (zero postulates, zero holes):
- **DBC Validator soundness/completeness** (`DBC/Validity/Theorem.agda`) — ✅ COMPLETE:
  - `ValidDBC`: formal predicate (9 conditions) for when a DBC defines a well-defined partial function
  - `soundness : errorIssues (validateDBCFull dbc) ≡ [] → ValidDBC dbc`
  - `completeness : ValidDBC dbc → errorIssues (validateDBCFull dbc) ≡ []`
  - 1,267 lines across 6 proof modules, all `--safe --without-K`
  - First formally verified CAN database validator
- `iterate-correct`: Property-list iteration ≡ forward specification (spec-equivalence)
- Signal predicate trust boundary documented (parametric by design)
- **Gap D modules** (`LTL/Semantics.agda`, `LTL/Adequacy.agda`, `LTL/Coalgebra.agda`) — ✅ COMPLETE:
  - Denotational LTLf semantics for all 13 operators (`⟦_⟧`) ✅
  - Coalgebra: Rosu formula progression with combineAnd/combineOr ✅
  - `Sound` relation (6-ctor monitoring soundness) ✅
  - **Rosu refactoring (10-step plan)**:
    - ✅ Steps 18a–18h: All Rosu refactoring + adequacy theorem complete
    - ✅ Step 18i: Simplification — removed 429 lines of dead code (1490 → 1061)
    - ✅ Step 18j: Build ✅, 344 tests ✅, benchmarks ✅ (9,704 fps streaming LTL, Rosu tree growth fixed)
    - Deleted: Bisimilarity.agda, CoalgebraBisim.agda, StepResultBisim.agda
  - **Adequacy theorem** (1061 lines): Four-layer proof (Sound compositionality → operational decomposition → soundness transport → non-recursive metric helpers). Zero postulates, zero holes.
- All proof modules use `--safe --without-K`
- All files type-check with zero holes

---

### Phase 5: Optional Extensions ⏳ PLANNED

**Scope**: Features driven by user feedback and real-world needs

**Delivered**:
- ✅ DBC pretty-printer with format→parse roundtrip proofs (7 commits, +1,834/-393 lines)
- ✅ Encode/decode batch roundtrip proofs: `injectAll-roundtrip` proves that after `injectAll`, extracting any injected signal returns its value. Bridge lemmas (`roundtrip-unsigned→IR`, `roundtrip-signed→IR`) connect single-signal roundtrips to the batch predicate. Dead commutativity proofs (~200 lines) removed from `Encoding/Properties.agda`.
- ✅ Decidable precondition helpers for capstone theorem: decidable equality chain (`_≟-SignalPresence_`, `_≟-SignalDef_`, `_≟-DBCSignal_` in `DBC/Properties.agda`) and decidable checkers (`allAlwaysPresent?`, `allFromMessage?`, `pairsDistinct?` in `CAN/Batch/Properties.agda`). Users can now compute the 3 structural preconditions of `validDBC-roundtrip` automatically.
- ✅ Decidable value representability: `Representable` predicate with decidable checker `representable?` and bridge lemma `allRepresentable→allRoundtrip` (~120 lines in `CAN/Batch/Properties.agda`). Decides whether each (signal, value) pair is exactly representable, then derives `AllRoundtrip` from `ValidDBC`. Last non-decidable capstone precondition now decidable.
- ✅ extractAllSignals completeness proof: `extractAll-complete` proves `totalEntries (extractAllSignalsFromMessage dbc frame msg) ≡ length (DBCMessage.signals msg)` (~40 lines in `CAN/Batch/Properties.agda`). Every signal produces exactly one entry across the three result partitions (values, errors, absent). Proof by foldr induction with `with`-decomposition of the recursive accumulator.
- ✅ Mixed byte-order injection commutativity: `injectPayload-commute-mixed` proves disjoint `injectPayload` calls commute for all 4 byte-order combinations (~278 lines in `CAN/Endianness.agda`). 4-layer proof: swap-conjugation converts cross-BO operations to `applyWrites` at physical positions, then existing `applyWrites-comm` handles commutativity. Layered architecture: concrete Vec Byte 8 → single BitWrite → write list → AllDiffPos structural conversion → 4-case dispatch.

- ✅ C++23 binding (`cpp/`): Complete client library wrapping `libaletheia-ffi.so` via `dlopen`. Strong types (`std::byte` frame data, validated newtypes for CAN ID / DLC / BitPosition / etc.), `std::expected` for errors, RAII state lifecycle, dependency injection via `IBackend` interface. Mock backend for testing without Agda core. 53 test cases, 207 assertions across 3 layers (static compile-time, unit with mock, integration with threads). 5 rounds of 18-category code review — all categories pass, 0 clang-tidy warnings. CMake build with `FetchContent` (nlohmann/json, Catch2), `SOVERSION`, install/export for `find_package()`.

- ✅ Go binding (`go/`): Complete client library wrapping `libaletheia-ffi.so` via cgo + dlopen. Strong types (`[]byte` payload with DLC-based validation, sealed interfaces for CanID/Predicate/Formula/SignalPresence/FrameResponse, validated newtypes for CAN ID / DLC). `Backend` interface abstracts FFI; `MockBackend` for testing, `FFIBackend` for production. Goroutine-safe `Client` (`sync.Mutex`), double-close safe (`sync.Once`), GHC RTS init thread-pinned. 12 source files, 56 tests (all pass with `-race`). 3 rounds of 18-category code review + hardening pass.

- ✅ C header (`include/aletheia.h`): Documents the 4 C-callable FFI functions + GHC RTS initialization contract. The contract all language bindings implement against. Shakefile packaging target (`cabal run shake -- dist`) bundles .so + header.

- ✅ Big-endian (Motorola) signal fix: `convertStartBit` at parse time (`DBC/JSONParser.agda`), `unconvertStartBit` at format time (`DBC/Formatter.agda`). Byte-order-aware `BitsInFrame` predicate and `checkSignalExceedsDLC` validator. All soundness/completeness proofs updated (`ErrorChecks.agda`, `Composition.agda`). Verified against cantools for 5 signal types (byte-aligned, non-byte-aligned, single-bit, cross-byte, full-frame). Example DBC updated with BE signals.

- ✅ Violation enrichment (all bindings): Client-side enrichment pipeline — formula description, signal value extraction with bounded cache, human-readable violation reason. Implemented in Python (`_client.py`), C++ (`enrich.hpp`/`enrich.cpp`), and Go (`enrich.go`). 235-line Python enrichment test suite. Type audit across all bindings (removed redundant optionals where types have natural empty states).

- ✅ Docker images: `Dockerfile` (multi-stage from-source build) and `Dockerfile.runtime` (lightweight from pre-built dist). Runtime image is ~200 MB (python:3.13-slim + .so bundle + pip deps). `ALETHEIA_LIB` env var for library discovery. `shake docker` target builds the runtime image. Fat single-file .so investigated and deferred — GHC's static archives lack `-fPIC`, so self-contained `.so` would require rebuilding GHC. Current approach: 15 `.so` files with `RPATH=$ORIGIN` (9.6 MB compressed tarball).

- ✅ Cross-language benchmark suite (2026-03-26): Throughput, latency, and scaling benchmarks for all three language bindings with machine-readable JSON output. Runner script (`benchmarks/run_all.sh`), comparison script (`benchmarks/compare.py`). DLC serialization bug fixed in Go/C++ (was sending DLC code instead of byte count in DBC serialization). Hot-path optimizations: ack fast path (byte-level response check) and direct string serialization (bypass nlohmann/json.Marshal for frame commands) in C++ and Go.

- ✅ Binary FFI for streaming hot path (2026-03-27): `aletheia_send_frame` binary entry point eliminates JSON serialization for CAN data frames. Haskell shim constructs MAlonzo types (`Vec Byte n`, `TimedFrame`, `CANFrame`) directly from raw bytes. `processFrameDirect` in Main.agda calls `handleDataFrame` directly. StreamState.agda promoted from `--sized-types` to `--safe` (60/62 modules now `--safe`). Agda proofs in `Protocol/FrameProcessor/Properties.agda`: state machine guards (`handleDataFrame` preserves state when not streaming) and byte modulus identity (justifies Haskell shim skipping `% 256` for Word8 inputs). All three bindings updated with strong types at API surface (`Timestamp`/`CanId`/`Dlc` — raw C types only inside FFI implementation). CMakeLists.txt fixed to default to Release build. Result: **4.3x CAN 2.0B** (11k→48k fps), **9.1x CAN-FD** (1.9k→17k fps).

- ✅ CAN-FD support (started 2026-03-23, completed 2026-03-25): Variable-length payloads up to 64 bytes, DLC 0-15 with non-linear mapping (9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64). 13-step plan + 7 review fixes fully executed:
  - Steps 1-4: Agda core types (`CANFrame n`, `TimedFrame` dependent record, protocol messages generic, `physicalBitPos` parameterized, validation layer updated)
  - Steps 5-8: Proof generalization (all `CANFrame 8` → `∀ {n}` in Endianness, Encoding/Properties, Batch/Properties, Validity proofs)
  - Step 9: Full Agda build + MAlonzo compilation pass
  - Step 10: Python binding (420 tests pass)
  - Step 11: C++ binding (unit + static tests pass)
  - Step 12: Go binding (56 tests pass with `-race`)
  - Step 13: Documentation updated (PROTOCOL.md, DESIGN.md, PYTHON_API.md, CLI.md, INTERFACES.md, PITCH.md)
  - Review fixes (F1-F7): Stale comments fixed, `TimedFrame.dlcValid` invariant added, DLC bounds check (`≤ 15`) at protocol entry points, `ValidDLC` tightened to exact CAN/CAN-FD byte counts via `bytesToDlc`, `buildFrame` parameterized by DLC, `PhysicallyDisjoint` parameterized by frame byte count, disjointness proofs generalized (`lookupSafe-swapBytes`, `swap-updateSafe-swap` from case-enumeration to induction, `injectSignal-preserves-disjoint-bits-physical` from `CANFrame 8` to `∀ {n}`, capstone `validDBC-roundtrip` uses message DLC directly)
  - Code review round (R1-R5): `WellFormed.agda` uses `max-physical-bits` constant (was hardcoded 512), accurate CAN-FD comments in `Endianness.agda`, explicit `payloadSize = dlcToBytes dlc` in `Routing.agda`, numeric conversions extracted to `Encoding/Arithmetic.agda` (Encoding.agda 391→336 lines), `readBit-updateSafe-same`/`readBit-updateSafe-diff` proof helpers in `Endianness/Properties.agda`

**Planned / Research**:
- CAN format converters (BLF, ASC, MF4)
- Frame injection utilities
- Binary FFI for signal extraction/frame building (currently still JSON; lower priority — batch operations, not per-frame hot path)
- **SOME/IP support**: Investigate SOME/IP (Scalable service-Oriented MiddlewarE over IP) for automotive Ethernet backbones. Analysis (2026-03-22): SOME/IP is fundamentally service-oriented, not signal-based — 16-byte header (Service ID, Method ID, Client/Session ID, Protocol/Interface Version, Message Type, Return Code) + variable structured payload, not bit-packed signals. Requires a different frame model, different extraction logic, and different LTL atomic predicates (service-level: response timing, subscription freshness, method sequencing) vs CAN's signal-value predicates. The LTL engine itself is reusable. Also covers CAN-over-Ethernet encapsulations (DoIP/ISO 13400, gateways). **Prerequisite sequence**: ~~CAN-FD → binary FFI~~ (done) → SOME/IP frame model → SOME/IP properties.

**Status**: In progress

---

## Key Metrics

**Codebase**:
- Agda modules: 62 (60 `--safe`, 1 `--sized-types`, 1 new proof module)
- Python modules: 12
- C++ files: 16 (10 headers + 6 source)
- Go files: 12 source
- Lines of code: ~12,000 Agda + ~4,500 Python + ~1,950 C++ + ~2,000 Go

**Testing**:
- Python tests: 429 passing (via FFI)
- C++ tests: 81 passing (mock backend + Catch2)
- Go tests: 56 passing (mock backend, `-race` clean)
- Total: 566 tests

**Performance** (canonical source — other docs may round or summarize these numbers):

*Benchmarks: 10,000 frames × 5 runs, AMD Ryzen 9 5950X, Linux 6.6 (WSL2). C++ g++-15 -O3, Go 1.26.1, Python 3.13.12. 2026-03-27.*

| Benchmark | C++ (fps) | Go (fps) | Python (fps) |
|---|---:|---:|---:|
| CAN 2.0B: Stream LTL (2 props) | **47,847** | 45,807 | 42,086 |
| CAN 2.0B: Signal Extraction | **8,646** | 6,766 | 6,370 |
| CAN 2.0B: Frame Building | 5,205 | **5,337** | 4,429 |
| CAN-FD: Stream LTL (3 props) | **17,077** | 16,270 | 14,545 |
| CAN-FD: Signal Extraction | **900** | 802 | 716 |
| CAN-FD: Frame Building | 2,611 | **2,662** | 2,250 |

- Build time: 0.26s (no-op), ~11s (incremental)
- Per-frame latency: ~21 us (CAN 2.0B streaming, C++)
- Memory: O(1) verified (1.08x growth across 100x trace increase)
- **Binary FFI gain** (2026-03-27): Streaming LTL uses `aletheia_send_frame` (binary path, no JSON parsing). Compared to JSON-only baseline: **4.3x CAN 2.0B** (11k→48k fps), **9.1x CAN-FD** (1.9k→17k fps). Signal extraction and frame building still use JSON path.
- **Single-threaded runtime**: Deployable to minimal containers (1 vCPU) with headroom over a 500 kbit/s CAN bus (~4,000 frames/sec). CAN-FD at 8 Mbit/s requires ~8,400 fps — binary FFI delivers 17,077 fps (2x headroom).
- **Multi-bus scaling**: Each `AletheiaClient` has independent state (`StablePtr`). Multiple Python threads can monitor separate CAN buses in parallel. ctypes releases the GIL during FFI calls. For N buses on N vCPUs, pass `-N` to `hs_init` for parallel GHC capabilities.

**Verification**:
- Safe modules: 60 of 62 use `--safe` (59 with `--without-K`, 1 with `--without-K --no-main`)
- Coinductive modules: 1 uses `--sized-types` (Main.agda, for infinite trace semantics)
- Zero postulates in production code

---

## Next Steps

**Recent completions**:
- Docker images — **COMPLETE**: `Dockerfile` (from-source) + `Dockerfile.runtime` (pre-built), `shake docker` target
- Big-endian (Motorola) signal fix — **COMPLETE**: conversion at parse/format time, byte-order-aware DLC validation with updated proofs
- Violation enrichment (all bindings) — **COMPLETE**: formula desc + signal values + human-readable reason
- C++23 binding — **COMPLETE**: 5-round review, 81 test cases
- Go binding — **COMPLETE**: 3-round review + hardening, 56 tests
- C header + distribution packaging — **COMPLETE**

**Recent completions**:
- Binary FFI for streaming hot path — **COMPLETE**: `aletheia_send_frame` eliminates JSON on data frames. 4.3x CAN 2.0B, 9.1x CAN-FD. Agda proofs for state guards and byte boundary. C++ CMakeLists.txt defaults to Release.
- CAN-FD support — **COMPLETE**: All 13 steps executed (Agda core generalization, proof updates, Python/C++/Go bindings, documentation)
- Cross-language benchmark suite — **COMPLETE**: Python/C++/Go throughput/latency/scaling with JSON output, comparison script, runner. DLC serialization bug fixed. Hot-path optimized (ack fast path + direct serialization).

**Future**:
- SOME/IP support (automotive Ethernet, service-oriented)

---

**End of Status Report**

# Aletheia Project Status

**Last Updated**: 2026-04-25 (Phase B.3.d pre-gate ✅, layer 1 ✅, layer 2 ✅; layer 3 in_progress — commit 3a `804c584` shipped; commit 3b WIP under Option C, blocked on `Properties/Comments/Comment.agda` heap blowup — see `.session-state.md` + `memory/project_b3d_cm_heap_blowup.md`)

---

## Current Position

**Phase 5.1 - Proof Gaps & Spec Observations** ✅ COMPLETE. **Phase A (matrix + structural gates)** + **Phase B.1 / B.1.x (DBC metadata Tier 1 + Tier 2 + signal receivers + message senders)** + **Phase B.2 (mux query helpers — audit-closed)** + **Phase B.3.a (corpus baseline) / B.3.b (Agda skeletons) / B.3.c (incremental construct implementation)** ✅ COMPLETE, following the [Cross-Binding Parity Plan](docs/development/PARITY_PLAN.md) locked 2026-04-20.

Phases 1-5.1 complete. Phase 5 delivered optional extensions driven by user feedback: CAN-FD, multi-language bindings (C++, Go), binary FFI, formal verification completion, benchmarks. Phase 5.1 closed all 2026-04-07 system-review items. All provable correctness properties are proven.

Post-R17 work now follows the parity plan rather than the generic "Phase 6" label. Active tracks:
- **Phase A** ✅ — `docs/FEATURE_MATRIX.yaml` is the authoritative parity source (35 rows × 3 bindings after B.1.x + B.2); structural gates in Python / C++ / Go fail CI on any unresolved `implemented` entry.
- **Phase B.1 / B.1.x** ✅ — DBC metadata Tier 1 + Tier 2 + signal receivers + message senders (`BO_TX_BU_`) flow end-to-end through Agda core → FFI → bindings with roundtrip proofs.
- **Phase B.2** ✅ — Mux query helpers + DBC lookups, closed via audit (binding surface pre-existed client-side); matrix rows `dbc_queries_mux` + `dbc_lookup` both `implemented` × 3.
- **Phase B.3** — Agda-core DBC text parser (R17-DEF-4). **B.3.a/b/c ✅** (corpus baseline, skeletons, incremental constructs — 13 commits `4a086e8..a7f255e`). **Pre-B.3.d infrastructure ✅** (`check-properties` wiring + three WF fixes, commit `0035a4e`). **B.3.d pre-gate ✅ complete (2026-04-24)** — 6-commit ℚ→DecRat migration (`0b7849b`–`1f175ab`); `mkℚ`-direct `toℚ` runtime optimisation closed a 9–15% CAN-FD Signal Extraction regression and delivered +16% on CAN 2.0B; `NonTerminatingRational` parse error wired cross-binding.  **B.3.d Layer 1 ✅ complete (2026-04-24, `66afc2d`)** — Option 3a (2-axiom `Substrate/Unsafe.agda` + formatter refactor to `List Char` internals).  **B.3.d Layer 2 ✅ complete (2026-04-25)** — three commits: **2a** (`9adbc46`) lifts `Identifier` to `record { name : String; valid : T (validIdentifierᵇ (toList name)) }` (5–10% Signal Extraction regression accepted; revisit angles in `project_identifier_eq_revisit.md`); **2b** (`4559d5c`) ships `parseIdentifier-roundtrip`; **2c** (`f315c6f`) closes Tier A (byte-order/sign/scope/string-type) + Tier B (string-literal/mux marker).  **B.3.d Layer 3 ⏳ in_progress (2026-04-25)** — **3a** (`804c584`) shipped Preamble per-line-construct roundtrips (VERSION + BS_ + NS_); **3b ✅ Option C-broad** (this commit): all four simple-line constructs land together — `BU_` (node list, 611L) + `VAL_TABLE_` (value table, 790L) + `EV_` (env var, 1,581L) + `CM_` (comment, 2,533L; 5-way `CommentTarget` dispatch via 4-fold `<|>`-chain) — wired through `Properties/{Topology,ValueTables,EnvVars,Comments}.agda` facades.  CM_ heap blowup root-caused and fixed: `buildCANId-rawCanIdℕ` Extended clause `rewrite n+ext∸ext≡n` over a goal containing nested `ifᵀ`s replaced with pointwise `subst` per AGENTS.md line 234; type-checks at `-M16G` (was failing at `-M48G`).  **Commits 3c (attributes) / 3d (messages) + Layer 4 (top-level aggregator) pending.**  **B.3.e–j pending**: JSON command, Python feature-flag switch, cantools drop, C++/Go APIs, cross-binding parity.
- **Phase C** — Idiomatic cancellation / async / `send_frames_iter` / Go `context.Context` / C++ cancellation — **design rounds required** before any code (user rejected prior R17 proposals).
- **Phase D** — C++/Go doc-example harness mirror of R17 C6 (R17-DEF-6).

**Status**: Phase 5.1 + Phase A + Phase B.1/B.1.x + Phase B.2 + Phase B.3.a/b/c + **Phase B.3.d pre-gate + layer 1 + layer 2** complete; **Phase B.3.d layer 3 in_progress** (3a `804c584` shipped 2026-04-25; 3b WIP under Option C, CM_ heap blowup blocker); Layer 4 + Phase B.3.e–j → Phase C/D per plan.

---

## Project Phases

### Phase 1: Core Infrastructure ✅ COMPLETE

**Scope**: Build the foundational formally verified components

**Delivered**:
- Parser combinators with structural recursion
- CAN signal encoding/decoding (8-byte frames, 11-bit IDs)
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
- Signal predicates (Equals, LessThan, GreaterThan, LessThanOrEqual, GreaterThanOrEqual, Between, ChangedBy, StableWithin)
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
- JSON streaming protocol (request-response via FFI)
- Message router (command/data routing)
- Command handlers (parseDBC, setProperties, startStream, endStream)
- StreamState validation
- Haskell I/O shim
- Python AletheiaClient (FFI via ctypes)

**Phase 2B.2 - Streaming LTL**:
- Incremental LTL evaluation (O(1) memory)
- Coinductive streaming interface
- Frame modification mid-stream
- Throughput: 9,229 fps (108 us/frame via FFI; improved to 9,704 fps after Roșu simplification — the bottom-up LTLf simplification rules from Roșu's runtime verification work). C++, JSON path, single-threaded, Ryzen 9 5950X baseline

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
   - Mixed byte-order injection commutativity proven in Phase 5
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
   - Achieved: 9,704 fps (103 us/frame, C++ single-threaded JSON path, CAN 2.0B Stream LTL with 2 properties, Ryzen 9 5950X, 10k frames × 5 runs) — 3.03x speedup (initially 9,229 fps; improved after Roșu simplification)
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
   - Supports ASC, BLF, CSV, SQLite .db, candump .log, MF4, TRC with auto-detection
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
   - `validateDBCFull : DBC → List ValidationIssue` — 16 checks (8 error, 8 warning), all issues accumulated
   - `IssueCode` enum: 15 codes covering structural, physical, and authoring issues
   - Decidable types throughout (`_≟-CANId_`, `any?`, `_∈?_`, `signalPairValid?`)
   - Dual-layer validation: `parseDBC` runs both `validateDBC` + `validateDBCFull`
   - **Formally verified**: soundness + completeness proof (1,267 lines, 6 modules)
   - Python: `client.validate_dbc()`, `cli validate` subcommand
   - All tests pass, 0 regressions

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

### Phase 5: Optional Extensions ✅ COMPLETE

**Scope**: Features driven by user feedback and real-world needs

**Delivered**:
- ✅ DBC pretty-printer with format→parse roundtrip proofs (7 commits, +1,834/-393 lines)
- ✅ Encode/decode batch roundtrip proofs: `injectAll-roundtrip` proves that after `injectAll`, extracting any injected signal returns its value. Bridge lemmas (`roundtrip-unsigned→IR`, `roundtrip-signed→IR`) connect single-signal roundtrips to the batch predicate. Dead commutativity proofs (~200 lines) removed from `Encoding/Properties.agda`.
- ✅ Decidable precondition helpers for capstone theorem: decidable equality chain (`_≟-SignalPresence_`, `_≟-SignalDef_`, `_≟-DBCSignal_` in `DBC/Properties.agda`) and decidable checkers (`allAlwaysPresent?`, `allFromMessage?`, `pairsDistinct?` in `CAN/Batch/Properties.agda`). Users can now compute the 3 structural preconditions of `validDBC-roundtrip` automatically.
- ✅ Decidable value representability: `Representable` predicate with decidable checker `representable?` and bridge lemma `allRepresentable→allRoundtrip` (~120 lines in `CAN/Batch/Properties.agda`). Decides whether each (signal, value) pair is exactly representable, then derives `AllRoundtrip` from `ValidDBC`. Last non-decidable capstone precondition now decidable.
- ✅ extractAllSignals completeness proof: `extractAll-complete` proves `totalEntries (extractAllSignalsFromMessage dbc frame msg) ≡ length (DBCMessage.signals msg)` (~40 lines in `CAN/Batch/Properties.agda`). Every signal produces exactly one entry across the three result partitions (values, errors, absent). Proof by foldr induction with `with`-decomposition of the recursive accumulator.
- ✅ Mixed byte-order injection commutativity: `injectPayload-commute-mixed` proves disjoint `injectPayload` calls commute for all 4 byte-order combinations (~278 lines in `CAN/Endianness.agda`). 4-layer proof: swap-conjugation converts cross-BO operations to `applyWrites` at physical positions, then existing `applyWrites-comm` handles commutativity. Layered architecture: concrete Vec Byte 8 → single BitWrite → write list → AllDiffPos structural conversion → 4-case dispatch.

- ✅ C++23 binding (`cpp/`): Complete client library wrapping `libaletheia-ffi.so` via `dlopen`. Strong types (`std::byte` frame data, validated newtypes for CAN ID / DLC / BitPosition / etc., `Rational` for exact signal values), `std::expected` for errors, RAII state lifecycle, dependency injection via `IBackend` interface. Mock backend for testing without Agda core. Hash-map `DbcIndex` for O(1) signal lookups. Formula depth limit (100). 158 unit + 34 integration + 33 YAML + 47 Excel TEST_CASEs (272 total) across 4 runtime test suites + static_asserts in a 5th compile-time suite, `ctest 5/5` PASS (see Key Metrics). 11+ rounds of code review — all categories pass, clang-format and clang-tidy enforced as hard gates (zero violations/warnings). CMake build with `FetchContent` (nlohmann/json, Catch2), `SOVERSION`, install/export for `find_package()`.

- ✅ Go binding (`go/`): Complete client library wrapping `libaletheia-ffi.so` via cgo + dlopen. Strong types (`[]byte` payload with DLC-based validation, sealed interfaces for CanID/Predicate/Formula/SignalPresence/FrameResponse, validated newtypes for CAN ID / DLC, `Rational` for exact signal values). `Backend` interface abstracts FFI; `MockBackend` for testing, `FFIBackend` for production. Goroutine-safe `Client` (`sync.Mutex`), double-close safe (`sync.Once`), GHC RTS init thread-pinned. `slog` structured logging (12 event types, `ClientOption`/`WithLogger`). Hash-map indexes in `Dbc` for O(1) signal lookups. Formula depth limit (100). 16 source files + 14 test files in `go/aletheia/` (218 tests), plus a separate `go/excel/` module (58 tests) — all pass with `-race`. 23 rounds of code review (AGENTS.md). `ffi_nocgo.go` build tag fallback for non-cgo builds.

- ✅ C header (`include/aletheia.h`): Documents the 5 C-callable FFI functions + GHC RTS initialization contract. The contract all language bindings implement against. Shakefile packaging target (`cabal run shake -- dist`) bundles .so + header.

- ✅ Big-endian (Motorola) signal fix: `convertStartBit` at parse time (`DBC/JSONParser.agda`), `unconvertStartBit` at format time (`DBC/Formatter.agda`). Byte-order-aware `BitsInFrame` predicate and `checkSignalExceedsDLC` validator. All soundness/completeness proofs updated (`ErrorChecks.agda`, `Composition.agda`). Verified against cantools for 5 signal types (byte-aligned, non-byte-aligned, single-bit, cross-byte, full-frame). Example DBC updated with BE signals.

- ✅ Violation enrichment (all bindings): Client-side enrichment pipeline — formula description, signal value extraction with bounded cache, human-readable violation reason. Implemented in Python (`_client.py`), C++ (`enrich.hpp`/`enrich.cpp`), and Go (`enrich.go`). 235-line Python enrichment test suite. Type audit across all bindings (removed redundant optionals where types have natural empty states).

- ✅ Docker images: `Dockerfile` (multi-stage from-source build) and `Dockerfile.runtime` (lightweight from pre-built dist). Runtime image is ~200 MB (python:3.13-slim + .so bundle + pip deps). `ALETHEIA_LIB` env var for library discovery. `shake docker` target builds the runtime image. Fat single-file .so investigated and deferred — GHC's static archives lack `-fPIC`, so self-contained `.so` would require rebuilding GHC. Current approach: 15 `.so` files with `RPATH=$ORIGIN` (9.6 MB compressed tarball).

- ✅ Cross-language benchmark suite (2026-03-26): Throughput, latency, and scaling benchmarks for all three language bindings with machine-readable JSON output. Runner script (`benchmarks/run_all.sh`), comparison script (`benchmarks/compare.py`). DLC serialization bug fixed in Go/C++ (was sending DLC code instead of byte count in DBC serialization). Hot-path optimizations: ack fast path (byte-level response check) and direct string serialization (bypass nlohmann/json.Marshal for frame commands) in C++ and Go.

- ✅ Binary FFI for streaming hot path (2026-03-27): `aletheia_send_frame` binary entry point eliminates JSON serialization for CAN data frames. Haskell shim constructs MAlonzo types (`Vec Byte n`, `TimedFrame`, `CANFrame`) directly from raw bytes. `processFrameDirect` in Main.agda calls `handleDataFrame` directly. All 67 modules use `--safe`. Agda proofs in `Protocol/FrameProcessor/Properties.agda`: 15 properties covering state machine guards, streaming decomposition, ack/violation soundness + completeness, predicate table faithfulness, and signal cache correctness. All three bindings updated with strong types at API surface (`Timestamp`/`CanId`/`Dlc` — raw C types only inside FFI implementation). CMakeLists.txt fixed to default to Release build. Result: **4.3x CAN 2.0B** (11k→48k fps), **9.1x CAN-FD** (1.9k→17k fps).

- ✅ Dead code removal + proof completion (2026-03-27): Removed vestigial JSON data frame path (`parseDataFrame`, `Request` type, `DataFrame`, `processStream`, `parseRequest-sound` proof) — all bindings use binary FFI exclusively. Main.agda upgraded from `--sized-types` to `--safe`. New proofs: `initProc-correct` (initial LTL state correctness, `LTL/Coalgebra/Properties.agda`), response formatting correctness (8 refl proofs, `Protocol/ResponseFormat/Properties.agda`). All provable items in the proof assessment are now proven; only the MAlonzo FFI trust boundary remains (outside Agda's type system, mitigated by build-time checks and smoke tests).

- ✅ CAN-FD support (started 2026-03-23, completed 2026-03-25): Variable-length payloads up to 64 bytes, DLC 0-15 with non-linear mapping (see [PROTOCOL.md](docs/architecture/PROTOCOL.md#1-parsedbc) for details). 13-step plan + 7 review fixes fully executed:
  - Steps 1-4: Agda core types (`CANFrame n`, `TimedFrame` dependent record, protocol messages generic, `physicalBitPos` parameterized, validation layer updated)
  - Steps 5-8: Proof generalization (all `CANFrame 8` → `∀ {n}` in Endianness, Encoding/Properties, Batch/Properties, Validity proofs)
  - Step 9: Full Agda build + MAlonzo compilation pass
  - Step 10: Python binding (420 tests pass)
  - Step 11: C++ binding (unit + static tests pass)
  - Step 12: Go binding (56 tests pass with `-race`)
  - Step 13: Documentation updated (PROTOCOL.md, DESIGN.md, PYTHON_API.md, CLI.md, INTERFACES.md, PITCH.md)
  - Review fixes (F1-F7): Stale comments fixed, `TimedFrame.dlcValid` invariant added, DLC bounds check (`≤ 15`) at protocol entry points, `ValidDLC` tightened to exact CAN/CAN-FD byte counts via `bytesToDlc`, `buildFrame` parameterized by DLC, `PhysicallyDisjoint` parameterized by frame byte count, disjointness proofs generalized (`lookupSafe-swapBytes`, `swap-updateSafe-swap` from case-enumeration to induction, `injectSignal-preserves-disjoint-bits-physical` from `CANFrame 8` to `∀ {n}`, capstone `validDBC-roundtrip` uses message DLC directly)
  - Code review round (R1-R5): `WellFormed.agda` uses `max-physical-bits` constant (was hardcoded 512), accurate CAN-FD comments in `Endianness.agda`, explicit `payloadSize = dlcToBytes dlc` in `Routing.agda`, numeric conversions extracted to `Encoding/Arithmetic.agda` (Encoding.agda 391→336 lines), `readBit-updateSafe-same`/`readBit-updateSafe-diff` proof helpers in `Endianness/Properties.agda`

- ✅ Pipeline soundness fix (2026-03-28): Discovered 8 unsound absorption rules in `simplify/absorb` (Coalgebra.agda). Fixed: removed Until/Release rules, added `finalizesHolds` guards to Always/Eventually, added structural idempotency (And-And, Or-Or). Proofs complete: `absorb-runL`, `simplify-runL`, `pipeline-adequate`, `production-adequate` in `Adequacy/Pipeline.agda`.

- ✅ DeltaPredicate split (2026-04-02): `DeltaPredicate` now has two constructors: `ChangedBy` (directional — sign of delta determines direction: positive `curr - prev ≥ delta`, negative `curr - prev ≤ delta`) and `StableWithin` (magnitude tolerance — `|curr - prev| ≤ tolerance`). Previous `ChangedBy` semantics (`|curr - prev| ≤ delta`) were a confused mix. JSON protocol: `"changedBy"` predicate with `"delta"` field, new `"stableWithin"` predicate with `"tolerance"` field. Roundtrip proof updated (`refl`). All three bindings updated with `StableWithin` type + enrichment display. Python: `Signal.stable_within(tol)` method. C++: `StableWithin` struct + `Tolerance` newtype. Go: `StableWithin` struct + `Tolerance` type, negative delta now allowed in `ChangedBy`.

- ✅ AGENTS.md (2026-03-29, rewritten 2026-03-31): Review protocol document for all languages (Agda 16 categories, Go 22, C++ 22, Python, Documentation 19). Origin-blind finding rules: findings have no origin, age, or owner -- they are things that are wrong and get fixed. C++ section adds clang-format and clang-tidy as hard gates (zero violations/warnings required).

- ✅ RTS cores for all bindings (2026-03-31): GHC RTS `-N` flag configurable in all three language bindings. Python: `AletheiaClient(rts_cores=N)`. C++: `make_ffi_backend(path, rts_cores)` with `int rts_cores = 1` default. Go: `NewFFIBackend(path, WithRTSCores(n))` functional option. All: once-per-process, warn on mismatch, never reinitializable. Enables multi-bus monitoring with parallel GHC capabilities.

- ✅ Opt-in structured logging for all bindings (2026-03-31): 12 log events matching Go's slog event set, implemented in all three bindings. C++: custom `Logger` class (`log.hpp`, ~90 lines) — callback-based `LogRecord` with `LogLevel`, event name, `initializer_list<LogField>`, `source_location`; zero-cost when default-constructed. Python: `logging.getLogger("aletheia")` — standard library, no handler = silent. Go: `slog.Logger` via `WithLogger` option (already existed). Events: `properties.set` (Info), `stream.started` (Info), `stream.ended` (Info), `frame.processed` (Debug), `cache.hit`/`miss` (Debug), `cache.full` (Warn), `enrichment.property_index_oob` (Warn), `enrichment.extraction_failed` (Warn), `extraction.serialize_failed`/`process_failed`/`parse_failed` (Warn). Tests: C++ 2 logger tests, Python 5 logger tests.

- ✅ Cross-language code review round 4 (2026-03-31): 27 fixes across all bindings. **Python** (12 fixes): formula depth limit (100), `Rational` type for DBC signals (exact numerator/denominator, no float), hash-map DBC index for O(1) signal lookups, `dbc_queries.py` module, `_types.py` for shared types, enrichment refactored to use index. **C++** (12 fixes + 6 clang-tidy): `Rational` type replacing `double` in `DbcSignal`/`SignalValue`, hash-map indexes (`DbcIndex`) for O(1) lookups, formula depth limit (100), `parse_dbc_string` endpoint, `DbcSignal` index-based lookup in enrichment, clang-format and clang-tidy enforced as hard gates (zero violations/warnings). **Go** (3 fixes): `Rational` type replacing `float64` in `DbcSignal`/`SignalValue`, hash-map indexes in `Dbc` type, formula depth limit (100).

- ✅ YAML and Excel loaders for C++ and Go (2026-04-01): Four-tier check interface (Excel → YAML → Check API → DSL) now complete across all three bindings. C++ uses yaml-cpp + OpenXLSX (FetchContent), Go uses gopkg.in/yaml.v3 + excelize/v2. Both match Python's API: `load_checks_from_yaml`, `load_checks_from_excel`, `load_dbc_from_excel`, `create_excel_template`. Condition dispatch through existing Check DSL builders. Error messages match Python format for cross-language parity. C++: 76 YAML + 120 Excel test assertions. Go: 88 new tests (30 YAML + 58 Excel).

- ✅ Cross-language API review rounds 5-11 (2026-04-01): 30+ fixes across all three bindings (47 files, +1058/-345 lines). Semantic correctness: CAN ID range constants from bit widths, type-derived limits (std::numeric_limits, math.MaxInt64), INT64_MIN overflow guard, Go parseRational truncation check. Safety: [[nodiscard]] on all C++ AletheiaClient methods, static_assert non-copyable, lo>hi validation in Check API (all 3 bindings), .value()→* for known-valid std::expected. Protocol: AGENTS.md origin-blind rules + backward-compat prohibition, OpenXLSX pinned commit, clang-tidy clean. Total review rounds to date: Agda 7 batches, Python 11 rounds (534 tests), C++ 11 rounds (5 test suites), Go 23 rounds (243 tests).

- ✅ extractSignalCoreFast equivalence proof (2026-04-04): Formally verified `extractSignalCoreFast ≡ extractSignalCore` — the byte-at-a-time extraction algorithm produces the same result as the per-bit BitVec algorithm. ~150 lines of proof across 3 files: `bitVecToℕ-bit` lemma (Conversion.agda), `extractCore-extractBits` + `extractRaw-extractBits` (Endianness.agda), final `extractSignalCoreFast-equiv` theorem (Encoding.agda). Key lemma chain: per-bit arithmetic identity → structural induction on bit length → dropVec bridge for byte-skipping optimization.

- ✅ Index-based signal lookup equivalence proof (2026-04-04, superseded 2026-04-19 by R17 C3b): Three equivalence proofs previously in `CAN/BatchFrameBuilding/Properties.agda` (`lookupSignalsByIndex ≡ lookupSignals`, `buildFrameByIndex ≡ buildFrame`, `updateFrameByIndex ≡ updateFrame`) were retired when R17 C3b eliminated the name-based build/update frame path across Agda + all bindings. The index-based path is now the only path, making the equivalence proofs vacuous; `BatchFrameBuilding/Properties.agda` was deleted.

- ✅ Binary API proofs properties 16-22 (2026-04-04): Seven new properties in `Protocol/FrameProcessor/Properties.agda`: `processFrameDirect` decomposition (state/response), end-to-end Ack soundness at JSON level, read-only handler state preservation (extract, build, update, formatDBC). Supporting: `formatResponse-ack-unique` injectivity proof, `handleUpdateFrameByIndex` refactored for provability (where-block pair pattern).

- ✅ Benchmark runner hardening (2026-04-04): `run_all.sh` rewritten with `run_benchmark()` helper: temp file capture, JSON extraction (strips GHC RTS/cgo stdout pollution), Python-based validation, atomic `mv`. `compare.py` gracefully skips corrupt/unreadable files.

- ✅ CAN error/remote frames + CAN-FD BRS/ESI metadata (2026-04-05): Review plan D1+D2 — final items from the Agda code review plan. `TraceEvent` data type in `Trace/CANTrace.agda` with `Data`/`Error`/`Remote` constructors. `TimedFrame` gets `brs : Maybe Bool` and `esi : Maybe Bool` CAN-FD metadata fields. `handleTraceEvent` dispatcher in `StreamState.agda`, `processEventDirect` entry point in `Main.agda`. FFI: `aletheia_send_error` + `aletheia_send_remote` exports. All three bindings updated: Python `send_error()`/`send_remote()`, C++ `send_error()`/`send_remote()` on `AletheiaClient` + `IBackend`, Go `SendError()`/`SendRemote()` on `Client` + `Backend`. Key design: LTL core stays on `TimedFrame` only — protocol layer dispatches `TraceEvent`, zero cascade to 10+ proof/evaluation modules. Closes the entire review plan (phases A-E, D1-D2).

- ✅ Review plan fix implementation — Tiers 1-5, 6 (#42-43), 8 (#55-63) (2026-04-05): ~50 fixes from the consolidated Agda code review plan. **Tier 1**: dead code removal (Prelude, Endianness/Properties), stale comment fixes (7 files), combinator replacements (map, any?, filter), multi-rewrite simplification (subst/cong). **Tier 2**: stdlib replacements (find, map⁺, universal), function deduplication (require, parseCANId, signal finders), shared helpers (TruthVal lemmas, cong₃/cong₄). **Tier 3**: error message consistency (operation prefixes, unified strings). **Tier 4**: where-block extraction + module splits — 9 new modules: `DBC/Validator/{Checks,Formatting}`, `DBC/Validity/Combinators`, `LTL/SignalPredicate/{Types,Cache,Evaluation}`, `LTL/TruthVal/Properties`, `Protocol/StreamState/{Types,Internals}`. **Tier 5**: monadic style (traverse, maybe combinator). **Tier 6**: `ErrorCode` ADT replacing ℕ constants in `BatchExtraction`. **Tier 8**: `listToVec` bounds check (was silent truncation), wire format byte order docs, MAlonzo fragility comments. Total: 80 Agda modules (was 67). Remaining: Tier 6 #44-48 (large type redesigns) and Tier 7 #49-50,54 (structural refactors) — require user scope decisions.

- ✅ Bounded CANId (#44) — intrinsic bounds via T (n <ᵇ max) (2026-04-06): `CANId` constructors now carry proof: `Standard n (T (n <ᵇ 2048))`, `Extended n (T (n <ᵇ 536870912))`. `WellFormedCANId` eliminated (bounds intrinsic). `parseCANId` uses `ifᵀ_then_else_` to construct proof in true branch. Decidable equality via `T-irrelevant` + `cong`. Roundtrip proofs via `ifᵀ-witness` lemma (avoids with-abstraction failure from rigid type dependency). Haskell FFI validates bounds before `unsafeCoerce ()` for proof field. New Prelude utilities: `ifᵀ_then_else_`, `T-irrelevant`, `T→true`, `ifᵀ-witness`. MAlonzo constructor names updated.

- ✅ liftCheck combinator (#50) — requireDec/rejectDec + liftTriangular (2026-04-06): Extracted reusable combinators eliminating repeated with-Dec boilerplate across DBC validity proofs. `requireDec`/`rejectDec` (decidable check building blocks) with 4 proof lemmas, `liftTriangular-sound`/`liftTriangular-complete` for pairwise AllPairs. 12 check functions in Checks.agda converted to one-liner combinator calls. 34 proof functions simplified across ErrorChecks/WarningChecks. `checkAgainst`/`triangularCheck` moved to Combinators.agda and made generic. Net: +242/-225 lines across 4 files. Review plan Tier 7 now fully closed.

- ✅ SignalCache uniqueness guarantee (#47) — @0 erased proof (2026-04-06): `SignalCache` now carries `@0` erased uniqueness proof on its key set. Zero runtime cost via quantity-zero erasure.

- ✅ Bounded DLC newtype (#45) — @0 erased proof + checkDLCOutOfRange removal (2026-04-06): Replaced `DBCMessage.dlc : ℕ` and `StreamCommand` DLC with validated `record DLC` carrying `@0 bounded : T (code <ᵇ 16)`. `bytesToValidDLC` rejects invalid byte counts at parse time. Removed dead `checkDLCOutOfRange` check, `ValidDLC` predicate, `DLCOutOfRange` issue code — all trivially true by construction. `ValidDBC` now has 8 error conditions (was 9), 16 checks (was 17). `StreamCommand` constructors also use `DLC` type; `Main.agda` FFI boundary uses `ifᵀ` for DLC construction. `bytesToValidDLC-roundtrip` proof enables formatter roundtrips. 30 files changed across Agda + all language bindings.

- ✅ Typed error ADT (#48) — 5 domain types + 37 machine-readable error codes (2026-04-06): Replaced all `String ⊎ A` error handling with typed error ADTs. New `Aletheia.Error` module (258 lines): `ParseError`, `FrameError`, `RouteError`, `HandlerError`, `DispatchError` + top-level `Error` sum with `WithContext` wrapping. `formatError` preserves human-readable messages; `errorCode` produces 37 machine-readable codes. JSON protocol error responses gain `code` field. `Prelude.agda`: generalized `require`/`>>=ₑ` from `String` to `∀ {E}`, added `mapₑ` left-map. `withDBC` redesigned from continuation-passing to `HandlerError ⊎ DBC` sum return. `>>=ₑ-congʳ` proof generalized. All 12 Agda modules updated + Haskell FFI (MAlonzo name shifts) + Python (`ErrorCode` enum, `ProtocolError.code`) + C++ (`ErrorCode` enum, `error_code_from_string`, `AletheiaError::code()`) + Go (`Error.Code`, 37 `Code*` constants). 24 files, +776/-226 lines.

- ✅ Phase-indexed StreamState (#46) — sum type eliminating StreamPhase enum (2026-04-06): Replaced `StreamPhase` enum + `StreamState` record with a sum type where phase is encoded in the constructor: `WaitingForDBC | ReadyToStream DBC props cache | Streaming DBC props prev cache`. Invalid state transitions are now unrepresentable. `Maybe DBC` eliminated (ReadyToStream and Streaming always carry a DBC). `prevFrame` field only exists in Streaming phase. `getDBC : StreamState → Maybe DBC` accessor for backward compatibility. All 22 proofs in `FrameProcessor/Properties.agda` simplified: guard proofs become trivial `refl`, preconditions (`phase ≡ Streaming`, `dbc ≡ just dbc`) eliminated entirely, streaming decomposition becomes `refl`. Tier 6 (#44-48) now fully complete.

- ✅ Code review plan F1-F40 — remaining findings (2026-04-06): **F12**: CAN-specific constants (`standard-can-id-max`, `extended-can-id-max`, `max-physical-bits`) moved from `Prelude.agda` to new `CAN/Constants.agda` module, breaking circular dependency (CAN/Frame no longer imports Prelude for CAN constants). 10 consumer modules updated. FFI updated to `AgdaCANConst`. **F16**: `ExtractionResults`/`IndexedExtractionResults` unified into `PartitionedResults K E` parameterized record with generic `emptyPartitioned`/`combinePartitioned`. 5 proof pattern matches in `Batch/Properties.agda` updated. FFI MAlonzo names updated. **Module splits** (F30-F31): `Main.agda` → `Main/JSON.agda` + `Main/Binary.agda`; `Protocol/JSON.agda` → `JSON/{Types,Lookup,Format,Parse}.agda`. Original modules become thin facades. Shakefile updated for qualifier-aware MAlonzo name checking. **FFI safety** (F37-F40): MAlonzo-compiled `dlcToBytes`, CAN ID bounds, stdlib ℚ accessors, consolidated wire format docs. **8 new modules**, bringing total to 88. All 540 Python + 5 C++ + Go tests pass.

**Status**: Complete (2026-02-26 to 2026-04-06)
**Completion**: 100% (core features complete; spec observations tracked in Phase 5.1)

---

### Phase 5.1: Proof Gaps & Spec Observations ✅ COMPLETE

**Scope**: Address proof gaps and specification limitations identified during code review

- ~~Metric operator bounds unproven~~ ✅ PROVEN (2026-04-07): 13 properties in Coalgebra/Properties.agda — stepL terminal at window expiry, runL immediate resolution, past-window monotonicity, remaining-time anti-monotonicity
- ~~Signal cache monotonicity/coherence unproven~~ ✅ PROVEN (2026-04-07): 10 properties across Cache/Properties.agda (6) + FrameProcessor/Properties.agda (4) — entry preservation through updates/signal processing/frame processing, timestamp bound preservation (AllTimestamps≤), cache size non-decreasing
- ~~rangesOverlap incorrect at len=0 + dual overlap algorithms~~ ✅ RESOLVED (2026-04-07): removed rangesOverlap entirely; BatchFrameBuilding.signalsOverlap/anyOverlap/hasOverlaps now delegate to physicallyDisjoint? from DBC/Properties.agda (endianness-aware, formally proven)
- ~~Single-level multiplexing only~~ ✅ RESOLVED (2026-04-07): SignalPresence.When now takes List⁺ ℕ (multi-value mux). Supports extended DBC multiplexing (SG_MUL_VAL_). JSON field `multiplex_value` → `multiplex_values` (array). All Agda proofs (roundtrip, overlap, CanCoexist) updated. Python/C++/Go bindings updated.
- ~~Nested multiplexing~~ ✅ RESOLVED (2026-04-07): `checkSignalPresence` now recursively walks the multiplexor chain bottom-up via `walkMux` with fuel = `length signals` (max acyclic chain length). Cycle detection by fuel exhaustion → `MultiplexorCycle` IssueCode (replaces `MultiplexorNotAlwaysPresent`). 4 properties in `SignalExtraction/Properties.agda` via `checkPresenceP` helper. Cross-language tests: 5 Python (real FFI) + 5 C++ integration (real FFI) + 6 Go mock. Drive-by: 8 pre-existing basedpyright errors in `_client.py` fixed via `map(int, struct.unpack_from(...))` consolidation.
- ~~MetricEventually suc-encoded time~~ ✅ CLOSED (2026-04-07): non-issue. Suc-encoding is on `startTime` (not `window`); deadline 0 is representable and means "must hold now". Already documented in Syntax.agda lines 30-44.
- ~~BatchFrameBuilding name/index duplication~~ ✅ CLOSED (2026-04-07): already resolved. `LookupStrategy K` record + `lookupSignalsG`/`buildFrameG`/`updateFrameG` generics. The six named functions are one-liner aliases over shared implementations.
- ~~DBC roundtrip requires empty metadata (groups/envvars/vtables)~~ ✅ RESOLVED (2026-04-07): Added metadata parsers (parseSignalGroupList, parseEnvironmentVarList, parseValueTableList) to JSONParser.agda with parseOptionalArray for backward compatibility. MetadataRoundtrip.agda proves unconditional roundtrip for all three types. Removed empty-metadata preconditions from WellFormedDBCRT. Fixed pre-existing bug in MessageWF.agda (stale proof hidden by interface cache). 90 Agda modules.
- LTLf completeness and liveness proofs (see sub-items):
  - ~~Two-valued agreement (full completeness)~~ ✅ PROVEN (2026-04-07): Agreement.agda — `runL table proc σ ≡ ⟦ denot table proc ⟧ σ` when all atomic predicates return True/False (TwoValued). Uses `rewrite` + identity lemmas (`∧TV-true-l`, `∨TV-false-l`, etc.) to handle overlapping `∧TV`/`∨TV` clause non-reduction. Four metric helpers extracted for termination. 91 Agda modules.
  - ~~Metric resolution guarantee~~ ✅ PROVEN (2026-04-07): Coalgebra/Properties.agda — `runL-definite` (runL only ever True/False), `runL-monotonic-mtl-sound` (composes adequacy + mtl-equiv via Sound transport), `runL-monotonic-{False,True}` corollaries. On finite monotonic traces, definite ⟦_⟧ₘ verdicts are mirrored exactly by runL — no Unknown, no Continue.
  - ~~Finalization soundness~~ ✅ PROVEN (2026-04-07): Coalgebra/Properties.agda — `finalize-empty-equiv : verdictToSV (finalizeL proc) ≡ ⟦ denot table proc ⟧ []`. Propositional equality between the operational end-of-stream verdict and the denotational empty-trace evaluation, proven by structural induction on all 13 LTL constructors. Connects operational "didn't find it" to denotational "it's not there." Closes the last LTLf liveness sub-item.
  - ~~Safety-liveness duality~~ ✅ PROVEN (2026-04-07): Semantics/Duality.agda — `eventually-always-dual`, `always-eventually-dual`, `until-release-dual`, `release-until-dual`. Four pointwise identities on `⟦_⟧` proven by structural induction on σ + de Morgan + double-negation lifted from Kleene logic. Added `notTV-involutive`, `deMorgan-∧`, `deMorgan-∨` to TruthVal/Properties.agda. 92 Agda modules.
- ~~No bound proof for indexHelper indices~~ ✅ PROVEN (2026-04-07): FrameProcessor/Properties.agda Property 27 — `AllBelow : ℕ → LTL ℕ → Set` predicate, `indexHelper-bound`, `indexFormula-bound`, `simplify-bound`, `stepL-bound`, `lookupAtom-total`, `mkPredTable-bounded`. Layered proof: AllBelow weakening + indexHelper monotonicity + bound preservation through both `simplify` (via per-And/Or `absorb` helpers) and `stepL` (via `combineAnd`/`combineOr` lemmas through `ResultBound`). The `nothing → Unknown` branch in `mkPredTable` is now provably dead code; lookup is total over reachable indices.
- ~~Monotonic predicate defined but unused in Agda~~ ✅ RESOLVED (2026-04-07): `handleDataFrame` now enforces timestamp monotonicity directly in Agda via `checkMonotonic` — backward frames (`timestamp tf < timestamp prev`) are rejected with a new `NonMonotonicTimestamp` `HandlerError` (code `handler_non_monotonic_timestamp`). The `prev` field in the `Streaming` constructor (previously set but never read) is now repurposed as the monotonicity anchor. 6 new properties in FrameProcessor/Properties.agda Property 28: `checkMonotonic-first`/`-≥`/`-<` (runtime check classification), `handleDataFrame-rejects-regress` (backward rejected, prev unchanged — rejected frame never becomes new anchor), `handleDataFrame-accepts-monotonic` (≥ anchor preserves iteration decomposition), `handleDataFrame-first-frame` (nothing prev always accepted). These bridge the streaming pipeline to the existing `Trace.CANTrace.Monotonic` predicate that Coalgebra metric LTL theorems take as hypothesis. Duplicated runtime checks removed from Python (`_client.py`), C++ (`client.cpp`/`client.hpp`), and Go (`client.go`) — Agda is now single source of truth. New `HandlerNonMonotonicTimestamp` added to C++ `ErrorCode` enum and Go `CodeHandlerNonMonotonicTimestamp` constant (41 total error codes, was 40). Cross-binding tests: 1 Python real-FFI (`test_send_frame_non_monotonic_timestamp`), 1 C++ integration (`[integration][monotonic]`), 1 Go mock (`TestSendFrame_NonMonotonicTimestamp`). `Main/Binary.agda` "CALLER CONTRACT" comment replaced with pointer to the in-core enforcement.

**Post-implementation review round (2026-04-07)** — 11 findings (C1/C2/C3 + H1–H6 + D1–D3 + X1/X2) closed after Phase 5.1 14/14 landed:

- **C1** Monotonic bridge lemma from `handleDataFrame` → trace-level `Trace.CANTrace.Monotonic` (closes the enforcement ↔ theorem-hypothesis gap)
- **C2** `LTL/Adequacy/Agreement.agda` module-header sweep — documents that `TwoValued` does NOT hold universally on `mkPredTable` (dead-code Unknown branch, Property 27); both `adequacy` (cold start) and `warm-cache-agreement` (steady state) are production-applicable, with the reasoning chain written out
- **C3** Warm-cache agreement chain: `evalPredicate-cache-definite` → `lookupAtom-warm` → `warm-cache-table-definite` → `warm-cache-bounded-twovalued` → `agreement-bounded` → `warm-cache-agreement`. Composes Property 27 with cache warmness to discharge `agreement`'s `TwoValued` precondition on steady-state hot paths
- **H1+H4** Chained `rewrite` blocks in SimplifySound + Agreement rewritten using identity lemmas from `TruthVal/Properties.agda` (unblocks overlapping Kleene clauses without with-abstraction memory blowup)
- **H2** Brittle `cong₂ f refl eq` in `runL-and-right-True` merged into single `cong₂ f A (trans B C)` to avoid unsolvable metavariable from non-injective `_∧TV_`/`_∨TV_`
- **H3** Two-sided `sound-transport : m₁≡m₂ → d₁≡d₂ → Sound m₁ d₁ → Sound m₂ d₂` combinator extracted in `Adequacy.agda` (composed from existing `sound-transport-monitor`/`sound-transport-denot`); `runL-monotonic-False`/`runL-monotonic-True` now single-call
- **H5** Legacy `inspect` → modern `with expr in eq` migration in 3 files: `CAN/Encoding/Properties.agda` (2 uses), `Data/BitVec/Conversion.agda` (`parity-decomp`), `Protocol/JSON/Properties.agda` (`parseDBC-sound` nested match with 17+ absurdity clauses)
- **H6** Fuel justification documented for `walkMux` (`Validator/Checks.agda`) and `checkPresenceP` (`CAN/SignalExtraction.agda`) — fuel ≤ length signals, strictly decreasing, pigeonhole soundness argument, validator check 5 (`MultiplexorCycle`) discharges cyclic inputs
- **D1+D2+D3** `buildResult`/`updateResult`/`formatResult` deduplicated in `Protocol/Handlers.agda` → single private `frameResponse : String → ∀ {n} → FrameError ⊎ Vec Byte n → Response` helper; update handlers pre-apply `Data.Sum.map₂ CANFrame.payload`; all 4 where-block local helpers removed across `handleBuildFrame`, `handleBuildFrameByIndex`, `handleUpdateFrame`, `handleUpdateFrameByIndex`
- **X1** Error count drift fixed: `.session-state.md`, `CLAUDE.md`, `project_spec_monotonic_enforcement.md` all said 37→38; actual count (after re-scanning `errorCode` case families in `Aletheia/Error.agda`) is 40→41 (parseErrorCode 12 + frameErrorCode 6 + routeErrorCode 9 + handlerErrorCode 10 + dispatchErrorCode 4 = 41)
- **X2** Agent D deferred non-blockers recorded in memory `project_system_review_deferred.md`: 10.1 Timestamp=ℕ unrefined (no unit phantom), 11.1 `mkPredTable` invariant runtime-not-type-level, 14.1 `Main.agda` re-exports implicit, 15.1/15.2 large Properties files (Encoding 1582 lines; FrameProcessor 28+ properties), 12 unproven proof-breadth gaps (`parseDBC-complete` + `formatDBC ∘ parseDBCWithErrors` roundtrip; walkMux/checkPresenceP propositional agreement; cache coherence `cache hit ⇒ verdict matches fresh extraction`)

**Timestamp dimensional refinement (2026-04-08)** — Closes deferred non-blocker 10.1 from `project_system_review_deferred.md`. `TimedFrame.timestamp` and both `TraceEvent` error/remote timestamps now have type `Timestamp μs` (microseconds), a single-constructor record with an erased (`@0`) `TimeUnit` phantom parameter. New module `Aletheia.Trace.Time` (`src/Aletheia/Trace/Time.agda`) defines `TimeUnit` (`ns`/`μs`/`ms`/`s`), `Timestamp (@0 u : TimeUnit)` with `tsValue : ℕ` projection, and unit-preserving operators `_∸ᵗ_`/`_≤ᵗ_`/`_≤ᵗᵇ_`/`_≡ᵗᵇ_`/`_∸ₜₙ_` plus retraction lemmas `tsValue-mkTs`/`mkTs-tsValue`. MAlonzo strips the erased unit entirely: `newtype T_Timestamp_18 = C_mkTs_26 Integer` is the same runtime shape as the old `Timestamp = ℕ` alias, so there is zero hot-path cost (confirmed by benchmarks — Frame Building numbers are at or above the 2026-04-08 post-fix baseline). Two Agda types `Timestamp μs` vs `Timestamp ms` are now distinct and cannot be mixed without an explicit conversion. `Protocol/FrameProcessor/Properties.agda` and `StreamState.agda` use a new `timestampℕ : TimedFrame → ℕ` helper to unwrap at arithmetic/comparison boundaries (metric LTL operators, `checkMonotonic`, `updateCacheFromFrame`). `AletheiaFFI.hs` constructs timestamps via `AgdaTime.C_mkTs_26 (toInteger timestamp)` in all three FFI entry points (`aletheia_send_frame`, `aletheia_send_error`, `aletheia_send_remote`); MAlonzo renumbered the `TimedFrame`/`TraceEvent` constructor mangling to `C_constructor_32`/`C_Error_38`/`C_Remote_40` as a side-effect of the new runtime-relevant field. The unit is fixed at `μs` across all bindings (C++ `std::chrono::microseconds`, Go `Timestamp{Microseconds int64}`, Python docstrings, the binary protocol wire format) — the parameter exists for theorem parameterisation, in-source documentation, and future extensibility to higher-frequency buses. Total: 13 modified files (1 new, 12 edited — `Trace/CANTrace.agda`, `Protocol/StreamState.agda`, `Protocol/Handlers.agda`, `Protocol/Response.agda`, `Protocol/ResponseFormat.agda`, `Protocol/FrameProcessor/Properties.agda`, `LTL/Coalgebra.agda`, `LTL/Semantics.agda`, `LTL/Semantics/MTL.agda`, `LTL/Adequacy.agda`, `LTL/Adequacy/Agreement.agda`, `LTL/Adequacy/WarmCache.agda`). 95 Agda modules total (was 94 + `Trace/Time.agda`). SignalCache `lastObserved : ℕ` intentionally left unchanged — it is internal bookkeeping outside the 10.1 scope and refining it would touch 9 files and reopen `Cache/Properties.agda` proofs for no new dimensional-analysis benefit. All correctness gates green: Python 546 passing, C++ 5/5 ctest, Go -race + vet + gofmt clean, basedpyright 0/0/0, cabal build in 1m38s.

**Deferred non-blocker 11.1 — in-source caution added (2026-04-08)** — Following the Timestamp refinement, deferred item 11.1 (`mkPredTable`'s atom index refactored from `ℕ` to `Fin (length atoms)`, eliminating the proven-dead `nothing → Unknown` branch structurally) was re-analysed and confirmed deferred on performance grounds. MAlonzo compiles `Fin n` as a unary Peano chain (`data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10`) — each `Fin k` is k heap-allocated cells, each pattern match a heap dereference — whereas the current `ℕ` index compiles via BUILTIN to Haskell `Integer` with native `eqInt`/`subInt`. Since `mkPredTable` runs per frame on the streaming loop and its returned closure is invoked by `stepL` for every Atomic cell, this is exactly the same class of hazard as the `Dec`-vs-`Bool` regression (commit `5aa345e`, 30–65% throughput loss). A ~40-line comment block above `mkPredTable` in `src/Aletheia/Protocol/StreamState/Internals.agda:91` now documents the refactor option, the performance hazard, the structural cost (~8 files, four-valued `agreement` theorem shape change, FFI mangling re-verification), and the recommendation to leave it alone unless benchmarked first. `project_system_review_deferred.md` 11.1 updated with the hazard summary and pointer to the in-source caution. No runtime code change; `agda Aletheia/Protocol/StreamState/Internals.agda` clean.

**Deferred non-blockers 15.1/15.2 — large Properties files split into per-topic submodules (2026-04-08)** — Closes the last structural item from `project_system_review_deferred.md`. Both `Aletheia.CAN.Encoding.Properties` (1581 lines, 22 public theorems) and `Aletheia.Protocol.FrameProcessor.Properties` (1256 lines, 28+ public theorems) are now curated facades that re-export per-topic submodules via `open import X.Y public using (...)` blocks. **15.1**: `src/Aletheia/CAN/Encoding/Properties.agda` (1581L) → `Properties/Arithmetic.agda` (Layer 2 ℕ↔ℤ + Layer 3 ℤ↔ℚ algebraic bridge lemmas) + `Properties/Roundtrip.agda` (Layer 4 composition: signal-level `extract ∘ inject ≡ id` for unsigned/signed + `WellFormedSignal` record) + `Properties/Disjoint.agda` (bit preservation under disjoint injection, including mixed byte-order physical disjointness) + 78L facade. **15.2**: `src/Aletheia/Protocol/FrameProcessor/Properties.agda` (1256L) → `Properties/Step.agda` (223L, P1-P8 + P14-P15: state machine guards, `classifyStepResult`/`stepProperty`/`dispatchIterResult` characterisations, Streaming decomposition, Ack/Violation soundness + completeness) + `Properties/Cache.agda` (197L, P10-P13 + P23-P26: cache update decomposition + monotonicity / timestamp-bound preservation) + `Properties/Handlers.agda` (112L, P16-P22: FFI link properties + read-only handler state preservation) + `Properties/Bounded.agda` (625L, P9 `mkPredTable` faithfulness + P27 atom-index bound through `simplify`/`stepL`) + `Properties/Monotonic.agda` (209L, P28-P29: timestamp monotonicity enforcement at the step level + trace-level lift via `checkedFrames`/`HeadBounded` to `Trace.CANTrace.Monotonic`) + ~150L facade. Submodule dependency graph: `Handlers` imports `handleDataFrame-ack-sound` from `Step`; `Monotonic` imports `handleDataFrame-streaming` from `Step`; `Bounded` and `Cache` are leaf modules. The facades re-export every public name so external consumers import the same path unchanged — `LTL/Adequacy/WarmCache.agda` still imports `AllBelow` and `mkPredTable-lookup` from the top-level `Aletheia.Protocol.FrameProcessor.Properties` path. Zero MAlonzo impact: neither facade is in `AletheiaFFI.hs`'s import graph, and the submodule path is what determines mangling (the facade is a pure source-level layer). Splitting buys faster IDE jump-to-definition, independent re-checking per layer, and removes the "one file with many abstraction levels" smell that AGENTS.md Category 15 flags. Total line count across FrameProcessor submodules + facade is 1516 (was 1256 monolithic) — the overhead is facade headers and per-submodule imports, traded for navigation. Gates: Agda type-check clean (Monotonic uses qualified `Data.Nat.<ᵇ` with local `where open import` blocks attached to `with eq` clauses, type-checked successfully), cabal build in 1m51s, Python 546 passing, C++ 5/5 ctest, Go -race + vet + gofmt clean. 95 Agda modules (was 88 → +5 FrameProcessor submodules + 3 Encoding submodules − 1 monolithic Encoding − 0 monolithic FrameProcessor; the monolithic files become facades, so net is +7 modules, but the count was already 95 pre-split).

**Deferred non-blocker 14.1 — curated Main.agda public API (2026-04-08)** — Closes deferred non-blocker 14.1 from `project_system_review_deferred.md`. `src/Aletheia/Main.agda` is now a curated public facade; the old two-line `open import Main.JSON public` / `open import Main.Binary public` is replaced with explicit `using (...)` lists grouped into seven sections (FFI entry points; state machine; command dispatch; frame/trace/DLC types; error types and inspection; JSON and response formatting). Three `Error` names would otherwise collide — `Aletheia.Error.Error` (top-level sum), `Response.Error` (constructor in `Aletheia.Protocol.Message`), and `TraceEvent.Error` (constructor in `Aletheia.Trace.CANTrace`). The two constructors are re-exported as `ResponseError` and `TraceError`, leaving the canonical `Error` name free for the top-level sum type. `src/Aletheia/Main/JSON.agda` cleanup: the helpers `wrapJSON`, `tryParseCommand`, `dispatchCommand`, `handleParsedJSON` are now wrapped in a `private` block (matching `Main/Binary.agda`); `processJSONLine` stays public with its NOINLINE pragma. MAlonzo numbering is unchanged — `d_processJSONLine_64` still exists with the same number and `AletheiaFFI.hs` continues to reference it without modification; MAlonzo compiles private Agda definitions to numbered Haskell symbols regardless of visibility, so the private rewrite is a pure source-level cleanup with zero effect on the FFI name contract. 2 files touched. Gates: Agda type-check clean, cabal build in 2m17s, Python 546 passing, C++ 5/5 ctest, Go -race + vet + gofmt clean.

**Deferred non-blocker §12.1 — JSONParser enforces PhysicallyValid (2026-04-08)** — Closes the last proof-breadth item in `project_system_review_deferred.md`. `DBC/JSONParser.agda` now enforces `PhysicallyValid` at parse time via a `physicalGate` helper: LittleEndian passes through (LE signals trivially satisfy `pv-LE`), BigEndian runs three nested `ifᵀ` checks (`1 ≤ᵇ bl`, `csb + bl ∸ 1 <ᵇ frameBytes * 8`, `bl ∸ 1 ≤ᵇ csb`), each failed check emitting a distinct `ParseError`. `parse-wellformed` is strengthened from `WellFormedDBC` to `WellFormedDBCRT`, which lifts the conditional `parse-format-parse-given-PV` theorem to the unconditional `parse-format-parse : ∀ j d → parseDBCWithErrors j ≡ inj₂ d → parseDBCWithErrors (formatDBC d) ≡ parseDBCWithErrors j`. `PhysicallyValid` refactored from a 4-field record to a 2-constructor data type in `Formatter/WellFormed.agda` (`pv-LE` for LE signals, `pv-BE` carrying the three bound proofs for BE); the old record form rejected `startBit = 0` LE signals via an over-strong `msb-ge-len` constraint. `signal-roundtrip-go` in `Formatter/SignalRoundtrip.agda` pattern-matches on `pv-BE`/`pv-LE` and the BE clauses rewrite with `≤→≤ᵇ-true`/`<→<ᵇ-true` to discharge the gate's nested `ifᵀ` branches. New ParseError variants: `SignalBitLengthZero`, `SignalOverflowsFrame ℕ ℕ ℕ`, `SignalMSBBelowBitLength ℕ ℕ`, with error codes `parse_signal_bit_length_zero`, `parse_signal_overflows_frame`, `parse_signal_msb_below_bit_length`; total error code count 41 → 44. Mirrors added to Python `aletheia/protocols.py`, C++ `error.hpp` + `json_parse.cpp`, Go `error.go`. `parseSignalFields-wf` split into a `postPresence-wf` helper that takes the byte order explicitly (the with-chain on `physicalGate` is stuck on `bo` otherwise); companion `parseSignalFields-pv` returns `PhysicallyValid frameBytes sig`. Chain: `parseSignalFields-pv` → `parseSignal-pv` → `parseSignalList-pv` → `parseMessageBody-pv` → `parseMessage-pv` → `parseMessageList-pv` (returns `All WellFormedMessageRT msgs` by combining `parseMessage-wf` and `parseMessage-pv` at each cons step). Behaviour change: `test_big_endian_signal_exceeds_dlc` in `python/tests/test_dbc_validator.py` now asserts the BE overflow is caught at parse time (`parse_signal_overflows_frame`) rather than downstream by the validator's `signal_exceeds_dlc` — the validator's BE overflow check is now provably redundant for parser-validated DBCs. Gates: Cabal build 1m36s (all 218 MAlonzo modules clean, `libaletheia-ffi.so` rebuilt); Python 546 passing; basedpyright 0/0/0; pylint 9.97/10; C++ 5/5 ctest; Go -race + vet + gofmt clean. Benchmarks: all within ±5% of 2026-04-08 post-fix baseline — `physicalGate` runs only at parse time (one-shot DBC load), not on the streaming hot path, so no throughput impact.

**Post-commit benchmark-driven fix (2026-04-08)** — Frame-building throughput regression (30–65% across all 3 bindings, CAN-FD worst at -64%) initially misdiagnosed as the D1+D2+D3 handler dedup in `Protocol/Handlers.agda`. `git worktree` bisection pinpointed commit `5aa345e` as the actual root cause: it replaced the O(1) `rangesOverlap` in `BatchFrameBuilding.hasOverlaps` with the Dec-valued `physicallyDisjoint?`, whose nested `allBounded` quantifier allocates `Dec` proof terms per bit-pair per frame — MAlonzo `Integer`-boxing on those allocations dominates the hot path. The binary FFI benchmark path (`processBuildFrameBin` → `buildFrameByIndex`) bypasses `Handlers.agda` entirely, which is why D1+D2+D3 could not have been responsible. Fix: Bool-valued `signalsPhysicallyOverlapᵇ` fast path in `DBC/Properties.agda` with precomputed per-signal bit lists hoisted out of the O(m²) pair loop, plus equivalence proofs `physicallyOverlapᵇ-sound` / `physicallyOverlapᵇ-complete` establishing `signalsPhysicallyOverlapᵇ ≡ false ⇔ PhysicallyDisjoint`. Supporting lemmas: `bitsMemberᵇ-false-absent`, `bitsIntersectᵇ-false-disjoint`, `buildPhysicalBits-∈`, `signalPhysicalBits-∈`, `buildPhysicalBits-∈→offset`, `signalPhysicalBits-∈→offset`, `bitsMemberᵇ-true→∈`, `bitsIntersectᵇ-true→witness`. The fast path is as trustworthy as the Dec-valued check; both are provably equivalent. Recovery: CAN 2.0B Frame Building +23–37% and CAN-FD Frame Building +107–147% vs the regression state. AGENTS.md Category 16 updated with the Dec-vs-Bool cost-model lesson; `feedback_hot_path_refactor_benchmark.md` updated with the correct diagnosis; `project_frame_building_regression_2026_04_07.md` marked RESOLVED.

**Path G — three-valued Kleene FinalVerdict (2026-04-09)** — Closes the soundness-but-user-surprising gap where `Always(p)` on a trace that never observes `p`'s signal would operationally yield `Fails` at end-of-stream, while the denotational semantics `⟦ Always (Atomic p) ⟧ σ` says Unknown. Path G adds an `Unsure : String → FinalVerdict` constructor to `Aletheia.LTL.Incremental.FinalVerdict`, refactors `finalizeL` in `LTL/Coalgebra.agda` to three-valued Kleene K3 logic (Atomic → Unsure, Not/And/Or combine via K3 truth tables with Fails as ⊥ and Holds as ⊤), and adds a new `finalizesFails : LTLProc → Bool` helper in `LTL/Simplify.agda` as the guarded companion to `finalizesHolds` — the `Or φ (Eventually ψ) → Eventually ψ` absorption now requires `finalizesFails φ = true` (Unsure alone does not justify collapsing to Fails). Adequacy: `verdictToSV` maps Unsure → Unknown, and `finalize-empty-equiv` in `LTL/Coalgebra/Properties.agda` is updated so that the empty-trace Atomic case resolves to Unknown on both sides. `LTL/Semantics.agda` denotation of `Atomic p` on empty trace is now `Unknown` (matching the operational result). `LTL/SimplifySound.agda` soundness lemmas for empty-trace And/Or cases are rewritten to delegate to per-verdict helpers `runL-X-[] a b (finalizeL a) (finalizeL b) refl refl hyp`, working around Agda's limitation where nested `with finalizeL a | finalizeL b` scrutinee abstraction does not partially evaluate past intermediate `refl` rewrites — the helper form takes the two FinalVerdicts as explicit parameters and discharges the K3 combination algebraically. `LTL/Semantics/MTL.agda` four-valued metric combinators updated with Unsure absorption lemmas. **Protocol layer**: `Protocol/Response.agda` adds an `Unresolved` `PropertyResult` constructor mirroring `Violation` (`property_index`, `reason` fields); `Protocol/Handlers.agda` dispatch converts `FinalVerdict.Unsure r` into `Unresolved`; `Protocol/ResponseFormat.agda` emits `"status": "unresolved"` in the JSON results array. **Bindings**: Python `protocols.py` adds `"unresolved"` to the `status` Literal and `_client.py _parse_finalization_results` handles the new branch; `cli.py` prints a separate `Unresolved` section in `check` output and the JSON summary now carries `total_unresolved`/`unresolved` fields with `status ∈ {"violations", "unresolved", "pass"}`. C++ `response.hpp` adds `Verdict::Unresolved`, `json_parse.cpp parse_stream_result` maps `"unresolved"` → `Verdict::Unresolved`, `client.cpp end_stream` enriches both Fails and Unresolved and logs them separately. Go `result.go` adds `Unresolved` to the `Verdict` iota with `.String() = "unresolved"`, `json.go parsePropertyResult` maps the JSON string, `client.go EndStream` handles both via a switch. Tests: `python/tests/test_eos_finalization.py` updated — 4 tests (`test_changed_by_never_one_frame`, `test_always_never_observed_one_frame`, `test_always_never_observed_many_frames`, `test_eventually_never_observed_is_consistent`) were pinning the pre-Path-G Fails/vacuous-Holds behaviour and now assert `"unresolved"`; the class docstring rewrites the trace walk in K3 terms (`Unsure ∧ Holds = Unsure`, `Unsure ∨ Fails = Unsure`). New `test_end_stream_unresolved_verdict` in `test_unified_client.py`, `TestStreamingLTL_Unresolved` in `go/aletheia/stream_test.go`, third `"unresolved"` result entry in the `parse_stream_result complete` C++ Catch2 test, Go `TestVerdictString`'s Unresolved branch, C++ `static_asserts` for `Verdict::Unresolved` distinctness. **Drive-by**: 154 pre-existing clang-format violations across `cpp/include/aletheia/backend.hpp`, `cpp/src/{backend,client,enrich,ffi_backend,json_parse}.cpp`, and `cpp/tests/integration_tests.cpp` fixed via `clang-format -i` (one-line `if (s == "...") return …;` statements violating `AllowShortIfStatementsOnASingleLine: Never`); this is an unrelated baseline cleanup triggered by the tool gate per `feedback_fix_tool_gate_violations.md`. Also caught a lurking bug from the earlier Path G protocol commit: `cpp/src/json_parse.cpp parse_stream_result` had the enum and test updated but the parser switch still threw `"Unknown verdict status: unresolved"` — the third test entry exposed it. Gates: Agda type-check clean, cabal shake build in 1m33s (218 MAlonzo modules), Python 553 passing, basedpyright 0/0/0, pylint 10.00/10, C++ 5/5 ctest (142 unit + 14 integration + 33 YAML + 47 Excel), clang-format clean, Go 251 passing with `-race`, go vet + gofmt clean. 11 Agda files modified (no new modules); 103 Agda modules total, all `--safe --without-K`.

**AGENTS.md review round 6 (2026-04-10)** — 24 findings across Agda (14), Go (4), C++ (3), Python (2) + 1 promoted cross-binding parity fix. 13 agents reviewed all 127 categories (31 Agda + 32×3 bindings). Key changes: wired dead `ExtractionErr` constructor into extraction pipeline (updated completeness proof); extracted `parseObjectList` combinator with index threading for NotAnObject errors (generalized MetadataRoundtrip proofs over starting index); naming consistency (`_++ₛ_`, `showℕ`, bare Rational import cleanup); dead-branch documentation; `parseCanIdDlc`/`parseBytePayload` routing helpers; replaced hand-rolled `T-irrelevant` with stdlib; `slog.LogAttrs` for Go hot-path logging; `Error` LogLevel for C++; cross-binding EOS iteration order parity. 8 NO-FIX deferrals (bitLength admits 0, metric window/startTime raw ℕ, lastObserved ℕ, PropertyState.index Fin, SimplifySound/SoundOps repetitive, Satisfied stability lemma, _client.py marginal length). MAlonzo mangling fix: `extractionErrorCodeToℕ_142 → _144`. Gates: Python 598, basedpyright 0/0/0, pylint 10.00/10, C++ 5/5 ctest, clang-format clean, Go 251 -race, go vet + gofmt clean. Commit `57a0358`.

**AGENTS.md review rounds 7-10 (2026-04-11 → 2026-04-14)** — Four consecutive full AGENTS.md review rounds. R7: 51 findings (commit `cdd5821`). R8: partial (commit `6ab5639`). R9: 56 findings (commit `7203d9f`). R10: 68 findings across Agda (13), Go (7), C++ (12), Python (13), Docs (20) (commit `f227d88`). Cumulative: hot-path `mapₘ` → pattern match (+10.8% Stream LTL), `to_rational` returns `Result` not throw, INT64_MAX conservative bound, `float_to_rational` NaN/Inf/overflow guards, JSON error key fix, struct.error size checks, build_frame signature in 5 docs, PITCH fabricated API removal, --erasure flag documented. 6 false positives confirmed across rounds (type tightness, CATCHALL, domain model, MAlonzo assumptions, Python raw ints, eval-then-update ordering).

**AGENTS.md review round 11 (2026-04-15)** — 6 batches in two commits: `bf238b3` (Batches 1-5: mechanical, cross-binding parity with Go `excel` extracted to separate module, structural, SA.19.3 `streaming-warms-cache` proof + new `Protocol/Adequacy/StreamingWarm.agda`, docs) + `222b662` (Batch 6 hygiene: Go FFI symbol-list drift, C++ byte-order doc, C++ OOM leak guard, `pyproject.toml` `all` self-reference). Bench verification commit `38839eb` refreshed `d_extractionErrorCodeToℕ_144 → _148`. Stream LTL +2.4% C++ / +3.4% Go / +8.9% Python vs 2026-04-11 baseline.

**AGENTS.md review round 12 (2026-04-15)** — Single consolidated commit `60661a1` (92 files, +4,642 / −3,405). Agda AGDA-25 polymorphic `collectAtomsAcc` signature (`∀ {α} → LTL α → List α → List α`; erased type param, zero MAlonzo impact). Shakefile `check-erasure` phony greps MAlonzo for `C_Standard_12 Integer AgdaAny`, `C_Extended_16 Integer AgdaAny`, `newtype T_Timestamp_18`; fixed `check-invariants` + `check-no-properties-in-runtime` grep-shellout bugs (Exit/Stdout tuple + `[String]` argv). C++ H2/M1/M6: 1,800-line `unit_tests.cpp` split into 7 focused TUs + `test_helpers.hpp` with 40+ include-cleaner headers. Go `go.work` + `concurrent_test.go` for Client mutex surface. Python new `client/_log.py` (15-value `LogEvent` schema ↔ Go slog + C++ Logger), `benchmarks/_common.py` (shared bench boilerplate), `tests/test_error_code_sync.py` (Python↔Go error code parity). `__init__.py` reverted dynamic `__all__` attempt after basedpyright rejected it — static literal `__all__` + non-aliased re-exports is the only pattern pylint + basedpyright both accept without suppressions. Docs D1-D6 cross-ref refresh across 12 files.

**Post-R12 perf fix `1e40b4d`** — Benchmark on 10k×5 frames vs R11 post-commit state found Python CAN 2.0B Stream LTL at −16.1% (real regression, well outside ±2-4% machine noise). Root cause: R12's new `log_event()` helper built `extra` dict + f-string + called `logger.log()` unconditionally, even at DEBUG with no handler — hit on every hot-path `send_frame`. Pre-R12 `_logger.debug("%s …", …)` deferred formatting until after `isEnabledFor`. Fix: early-return on `isEnabledFor(level)` (stdlib-standard pattern). Post-fix Python Stream LTL recovered +10.9% (63,173 → 70,056 fps). Remaining R12-vs-R11 spread (C++ −2.9% / Go −7.8% / Python −7.0% on Stream LTL) is within inter-run machine noise on this WSL host (stdev ~2–4% of mean, Go Δ has no code change to explain it).

**AGENTS.md review round 13 (2026-04-16)** — Docs-dominant round (commit `c243428`). Section A count drift: PROJECT_STATUS C++ 40 files / Python 22 modules / Go 16+15 tests; CLAUDE.md C++/Go binding blocks demoted to cross-references with design-only prose. Section C Python architecture: shallow-copy docstring, lazy-import boundary, three-point coupling block, CLI `mux-query` subcommand + 11 tests. `Predicate.next()` / `Property.next()` **relocated** (not deleted — "discouraged ≠ deprecated"). Section D (28): PROTOCOL.md Common Error Codes table (50 codes), QUICKSTART.md prerequisites, CLAUDE.md newcomer mistakes, README/PITCH qualified throughput, INTERFACES parity code + logging section, PYTHON_API `data` examples. 617 Python tests, pyright 0/0/0, pylint 10.00. Python Stream LTL +8.4% vs R12 baseline.

**AGENTS.md review round 14 (2026-04-16)** — Cross-binding correctness + PhysicalValue precision (commit `a3208aa`, 80 files, +934/−529). Section A HIGH (9): C++ PhysicalValue double→Rational for exact precision (A7, 19 files); WNext operator across 22 Agda files + Python/C++/Go (A8); evaluate-before-update formal proof (A9); cross-binding error code parity — `FRAME_SIGNAL_VALUE_OUT_OF_BOUNDS` added to C++/Go (A3); Python binary zero-denom raise (A2), CAN-FD DLC fix (A4), enrichment zero-denom guard (A6); C++ `parse_frame_response` type check (A1); Shakefile stdlib name detection (A5). Section B MEDIUM (13): Go cgo bounds validation (B1), Go mutable maps→accessor functions (B2), C++ MockBackend binary heuristic (B3), C++ symmetric validation (B4), backend.warning cross-binding vocabulary (B5), Python finalization parsing (B6), Agda ValidationFailed structured (B7), docs JSON→binary-FFI qualifier (B8), PROTOCOL.md unresolved status (B9), aletheia.h send_error/send_remote (B10), CLI.md mux-query (B11), test count fix (B12), Agda version + 16 log events (B13). Section C LOW (23): Go dead code + interface{}→any + naming (C1-C3); C++ SPDX headers + naming + Rational constructor validation + unified MessageKey + MockBackend default test (C4-C8); Python immutability + naming + --version + test gaps (C9-C12); Agda dedup + patterns + combinators (C13-C17); Docs cross-ref consolidation (C18). Verification: 619 Python tests (+2), 268 C++ tests (+4), 276 Go tests, 1163 total. pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean. Benchmarks within WSL2 variance (no regression gate crossed).

**AGENTS.md review round 15 (2026-04-17)** — Cross-binding parity + strict protocol validation (commit `2853644`, 38 files, +617/−207). Section Agda: Error formatting consistency (quoted signal names in `FrameError`), `WrappedParseError` → `WrappedParse` constructor rename in `RouteError`. Section C++ (CX1-CX10): **CX3** strict `IssueSeverity` parsing — Agda wire vocabulary is `{"error","warning"}` only, reject others as `ProtocolError`; **CX8** `ErrorKind::BinaryUnsupported` sentinel added for Go `ErrBinaryPathUnsupported` parity; **CX10** `IBackend::rts_mismatch_info` out-of-line default for ABI stability; clang-format applied to 11 touched files; 4 new unit tests including MockBackend BinaryUnsupported fallthrough. Section Go (GO1/GO2/GO4/GO6/GO7/GO8): **GO1** removed `backend.warning` event (was documented but never emitted; Python/C++/Go all kept at 15 events); severity validation rejects unknown wire values; CX3 parity via switch default returning protocol error. Section Python (14.4): `validate_issue_severities` helper extracted to `_response_parsers.py`; monkeypatch-based fake-FFI test for unknown severity; `_client.py` held below 1000-line pylint cap via helper extraction + unused `ValidationIssue` import removed. Section Docs (DO4-DO8): **DO5** README 50s→46s (accurate: 5M frames / 109,345 fps = 45.7s); **DO8** PROTOCOL.md new "Streaming Semantics: Soundness vs. Completeness" section explaining K5 limitation on `Eventually`/`Until`. **Benchmark Debug-build guard**: `benchmarks/run_all.sh` reads `cpp/build/CMakeCache.txt` and aborts on `CMAKE_BUILD_TYPE=Debug`; `cpp/benchmarks/benchmark.cpp` adds startup `check_release_build()` (fails without NDEBUG) and exposes `build_type` in the JSON `system` block — closes the silent −20% Signal Extraction regression mode caused by a Debug-pinned cache. Verification: 622 Python tests (+3), 275 C++ tests (+7), 223 Go tests, 1120 total. pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean, clang-format clean on R15-touched files, Agda full build green.

**AGENTS.md review round 16 (2026-04-17)** — Test split, doc SSOT, validator types (commit `eae36aa`, 37 files, +1536/−901). High (H1-H7): **H1** PROJECT_STATUS test counts refreshed (Python 624 / C++ 275 / Go 223 / total 1122). **H2** clang-format on 6 C++ files with violations (also picks up an R15 leftover in `cpp/benchmarks/benchmark.cpp` — out of R16 scope, surfaced for the audit trail). **H4** `tests/test_unified_client.py` split (1171 > 1000-line cap) into core (591) + CAN-FD/mux (370) + events/RTS (223), with the shared `simple_dbc` fixture lifted to `conftest.py`. **H5** CLAUDE.md historical session log stripped of stale module counts. **H6** COOKBOOK candump prereq note. **H7** QUICKSTART version-check commands. Medium (M1-M17): **M1** `ValidationFailed : String → HandlerError` refactored to `ValidationFailed : List ValidationIssue → HandlerError` (wire format unchanged via `formatHandlerError` flattening; structured info now preserved Agda-side for future wire revisions). **M2** harmonized `rts.cores_mismatch` event scope. **M4-M5** Python A clean-up. **M6** doc SSOT — confirmed remaining cross-doc references serve distinct purposes (rule definition vs status indicator vs review check) and don't constitute drift. **M7** throughput qualifier scope labels in README + PITCH. **M8** CLI mux-query example output. **M9** COOKBOOK debug-violation + validation-errors recipes. **M10** PROTOCOL error/remote frame state machine. **M11** broke CLAUDE.md:439 dense R15 paragraph into bullets. **M12** README iter_can_log format note. **M13** new `test_lazy_import_boundary.py` guards `aletheia/__init__.py` ↔ `client/_ffi.py` ↔ `_install_config.py` cycle structurally. **M14** CMakeLists yaml-cpp C++20/C++23 conflict comment. **M15** OpenXLSX commit hash → release tag. **M16** strengthened `detail/cache_keys.hpp` off-limits documentation. **M17** INTERFACES.md "freely" vagueness sharpened + C++/Go DBC text workaround documented. Low (L1): BUILDING.md install-version drift note. Verification: 624 Python tests (+2), 275 C++ tests, 223 Go tests, 1122 total. pyright 0/0/0, pylint aletheia/ 10.00, pylint test files 9.95 (only R0801 cross-file fixture similarity remains, refactoring would harm test clarity), ctest 5/5, go -race clean, Agda full build green. Benchmarks within WSL2 ±10% inter-run variance of R15 baseline (steady-state noise floor ~2–4%; transient swings beyond ±10% trigger investigation, per the R12 protocol that caught the −16.1% `log_event` regression).

**AGENTS.md review round 17 (2026-04-18 → 2026-04-19)** — Decomposed into 7 commit phases (C1–C7; C3b/C5b split as sub-phases during implementation). Aggregate diff relative to R16 tip (`eae36aa..9355da9`): 12 commits, 111 files, +2605/−1704. **C1** (`db2d90c`) — Agda per-file items 1, 2, 4, 5, 6 + system items 13, 14, 15; Shakefile `check-ffi-exports` / `regen-ffi-exports` paired with `haskell-shim/ffi-exports.snapshot`, Shakefile `check-stdlib-version`; PROTOCOL.md "Streaming Semantics: Soundness vs. Completeness" section. Item #3 (stdlib-mandated `{{NonZero}}` instance args) resolved in-source as `DEFER-stdlib-mandate` comment blocks in three modules with AGENTS.md Cat 29 text updated accordingly. **C1-fixup** (`2ba39df`) — three user-approved carve-outs: (8a) drop dead `_-_` from `Evaluation.agda:13`; (9b) full error-message harmonisation (adopt `InContext` wrapping uniformly across all 5 error ADTs + unified quoting); (11a) replace local `+-assoc-cancelʳ` in `Rational.agda:186` with stdlib lemma. **C2** (`998ba88`) — Python non-#17 items 16, 18–28, 30, 32–34; `tests/` lint score held at 10.00/10 via four batches (mechanical, restructuring, protected-access, R0801 cross-file dedup). **C3** (`dca748f`) — C++ items 35–40 + Go items 41, 43, 44, 45 + Go/C++ mirror of Python item 34; scoped CMake fix. **C3b** (`be33e26`) — single binary-only frame build/update path: removed JSON-output path across Agda (`BatchFrameBuilding/Properties.agda` deleted → 120 → 119 modules), Haskell shim, MAlonzo snapshot, C++ serializers, Go marshalers, Python ctypes + error code; benchmarks baseline refresh (`774c6c8`). **C4** (`4b84cdf`) — merged `rts.cores_mismatch` event scope into Lifecycle (cross-binding). **C5a** (`fd7a436`) — docs sweep items 48–64 + Structured Logging SSOT. **C5b** (`5166b72`) — promoted BENCHMARKS.md to `docs/development/` (+ shell-syntax fix `37b8dbc`). **C6** (`9355da9`) — Python item #17: repo-root `conftest.py` harness (pre-built DBC + parse_dbc'd client + loader stubs) + `python/tests/test_doc_examples_harness.py` structural Cat 32 gate (parametrised over 11 tracked doc files, bans `python notest`); `pytest-markdown-docs>=0.9.2,<1` pinned in `dev` extras; `python/pyproject.toml`, PYTHON_API/INTERFACES fence retags, AGENTS.md § Cat 32 description + Verification command. **FP (3):** #7 (binary-constructor rewrites inherently 2-step, not G-A2), #24 (runtime optional-dep extras float majors by design), #46 (15 events confirmed across all three bindings). **DEFER (6):** #3 (in-source `DEFER-stdlib-mandate` comments), #12 (FFI `unsafeCoerce`), #27 (DBC metadata), #31 (`send_frames_iter`), #38 (C++/Go DBC text), #42 (Go `context.Context`), plus **R17-DEF-6** (C++/Go doc-example harness mirror of C6). Verification: 649 Python tests (+25 from R16: C3 ProtocolError symmetry, C3b ctypes + error code exits, C6 `test_doc_examples_harness` 12 + markdown-docs runtime 103), 273 C++ tests (−2 from R16: 159 + 34 + 33 + 47 across 4 Catch2 binaries, R17 C3b removed JSON-output build/update), 223 Go tests (unchanged), 1145 total. pyright `aletheia/` 0/0/0, pylint `aletheia/` 10.00, pylint `tests/` 10.00, pylint `conftest.py` 10.00, ctest 5/5, go -race clean, Agda full build green. Benchmark audit (15 runs via two-batch protocol) confirmed no real regression vs R16 baseline; apparent B1 negatives were session-level WSL2/thermal noise, normalised by B2.

**Phase A — Cross-binding feature matrix + structural gates (2026-04-20)** — Commits `8b58ff0` (A.1 plan), `a96a0e1` (A.2 YAML seed, 29 × 3), `c80e9c7` (A.3 Python gate), `48c1439` (A.4 Go gate via `go/ast`), `5ea6a6d` (A.5 C++ gate via yaml-cpp + lexical-noise strip), `b5bfbeb` (A.6 default-battery wiring + stats refresh to 1207 total tests). `docs/FEATURE_MATRIX.yaml` is now the authoritative source for cross-binding parity: one row per user-facing capability, `bindings.{python,cpp,go}.{status, entry?, reason?, notes?}` with `not_applicable` requiring a non-empty `reason`. Structural tests fail CI when any `implemented` entry can't be resolved to a real public symbol — a silent API rename now breaks the build instead of drifting unnoticed.

**Phase B.1 — DBC metadata Tier 1 (2026-04-20)** — Commits `2928f63` (Python `DBCSignalGroup` / `DBCEnvironmentVar` / `DBCValueTable` TypedDicts + `dbc_to_json` population from cantools), `1cc3250` (C++ binding + clang-tidy audit on `ALETHEIA_CLANG_TIDY=ON` tree), `eced521` (ignore `cpp/build-tidy/`), `e458a3a` (Go binding), `ffd8679` (Go env-var test asserts exact `Rational` numerator/denominator instead of pass-by-default punt), `75a728c` (`dbc_metadata_tier1` matrix row flipped to `implemented`). Tier 1 fields (`signalGroups`, `environmentVars`, `valueTables`) already existed in the Agda core and flowed through the formatter; B.1 stopped the FFI boundary from dropping them.

**Phase B.1.x — DBC metadata Tier 2 + signal receivers (2026-04-20)** — Two commits landed.
- **Commit 1 of 2** (`2367812`, 37 files, +4439/−51): Tier 2 fields — nodes (`BU_`), comments (`CM_`), and attribute definitions/defaults/assignments (`BA_DEF_`/`BA_DEF_DEF_`/`BA_`/`BA_REL_`) — wired end-to-end through Agda core types + `JSONParser` + `Formatter` (with roundtrip proofs closed in `Formatter/Properties.agda`, `MessageRoundtrip.agda`, `SignalRoundtrip.agda`), validator, and all three binding structs. `Float` bounds round-trip as exact `Rational` (`Fraction` in Python), matching R14-A7 precision handling. Matrix split: `dbc_metadata_full` stub replaced with `dbc_metadata_tier2` (implemented) + `dbc_signal_receivers` (planned, for Commit 2).
- **Commit 2 of 2** (`93c02bf`, 26 files, +534/−76): `DBCSignal.receivers : List String` (trailing node list on `SG_` lines) + CHECK 21 `UnknownSignalReceiver` warning via `liftPerSignal`. `DBCMessage.receivers` derived binding-side as union of signal receivers. `Vector__XXX` cantools placeholder stripped on parse and re-emitted as fallback when the per-signal list is empty. New `"receivers"` JSON wire key on every signal. Matrix: `dbc_signal_receivers` → `implemented`; new `dbc_message_senders` row reserved for Commit 3 (`BO_TX_BU_` transmitters). Includes an R14-leftover `gofmt` fix in `go/benchmarks/main.go` (struct-tag alignment), scope-flagged in the commit body per the "never dismiss tool gate findings as pre-existing" rule.

Verification across Phase A/B: 735 Python tests + 1 expected-skip + 103 markdown-docs fences; 290 C++ tests across 5 runtime ctest binaries + `static_tests`; 238 Go tests `-race` clean; **1263 total**. pyright `aletheia/` 0/0/0; pylint `aletheia/` / `tests/` / `conftest.py` all 10.00/10; clang-tidy clean on B.1.x-touched files; go vet + gofmt clean; Agda full build + Shake guards (`check-ffi-exports` / `check-stdlib-version` / `check-erasure`) all green. Benchmark two-batch noise protocol (`feedback_benchmark_noise_diagnostics.md`) confirmed apparent B1 deltas on B.1.x Commit 2 were session-level WSL2/thermal noise — B2 normalised to within variance; cross-binding asymmetry + `DBCSignal.receivers` being parse-time-only (not per-frame hot path) sealed the diagnosis.

**Pylint gate hardening (`c4bda3f`, 2026-04-20)** — Adds `pythonpath = ["."]` to `[tool.pylint.main]` in `python/pyproject.toml`. Canonical dev flow stays `pip install -e .[dev]` inside `python/.venv`; this entry is belt-and-suspenders so `pylint tests/` resolves `aletheia.*` without requiring editable install. Inline comment flags the pylint 4.x `source-roots` rename (semantic divergence from pylint 3's `pythonpath`) for the eventual upper-bound bump per Phase 6 toolchain-upgrade item.

**Status**: Complete (14/14 items + post-implementation review round + post-commit regression fix + Path G three-valued finalisation + review rounds 6-17 + Phase A matrix gates + Phase B.1 Tier 1 + Phase B.1.x Tier 2 + signal receivers, all spec observations resolved or deferred with memory)

---

## Key Metrics

**Codebase**:
- Agda modules: 119 (all `--safe --without-K`, 4 also `--no-main`) — evolution: 92 (R7, 2026-04-07) → 95 (R8 post-commit + `Timestamp μs` refinement) → 103 (R9, 2026-04-14) → 120 (R11 split of large `Properties` files behind facade re-exports, 2026-04-15) → 119 (R17 C3b removed `BatchFrameBuilding/Properties.agda` as part of JSON-output path removal, 2026-04-19). See the "Prior" entries in [CLAUDE.md § Current Session Progress](../CLAUDE.md#current-session-progress) for per-round detail.
- Python modules: 22 (13 top-level + 9 in `aletheia/client/` subpackage)
- C++ files: 41 (14 public headers + 1 public detail header + 11 source + 3 internal detail headers + 11 test `.cpp` + 1 `test_helpers.hpp`)
- Go files: 16 source + 16 test (in `go/aletheia/`); separate `go/excel/` package for the optional Excel loader
- Lines of code: ~15,500 Agda + ~5,300 Python + ~4,000 C++ + ~4,400 Go (source only)

**Testing**:
- Python tests: 735 passing (via FFI) + 1 expected-skip (`test_lazy_import_boundary.py` skips when `_install_config.py` isn't present — guards the dev-checkout vs installed-wheel boundary); additionally 103 doc-example `python` fences executed end-to-end by `pytest --markdown-docs` via the repo-root `conftest.py` harness (R17 C6). Includes 64 cross-binding parity tests (`tests/test_feature_matrix_parity.py`) that validate `docs/FEATURE_MATRIX.yaml` schema (34 rows after B.1.x commit 2 split `dbc_signal_receivers`/`dbc_message_senders`) + every Python `implemented` entry
- C++ tests: 170 unit + 38 integration + 33 YAML + 47 Excel + 2 parity TEST_CASEs (290 total) across 5 runtime ctest binaries (`unit_tests`, `integration_tests`, `yaml_tests`, `excel_tests`, `feature_matrix_tests`) + 1 compile-time binary (`static_tests`), built from 12 `.cpp` sources; `feature_matrix_tests` reads `docs/FEATURE_MATRIX.yaml` and verifies every C++ `implemented` entry resolves to a header + whole-word symbol under `cpp/include/`
- Go tests: 238 passing in `go/aletheia` across 17 test files (mock backend, `-race` clean); the optional `go/excel` package is a separate Go module and is not counted in the total. Includes 2 parity tests (`feature_matrix_test.go`) that validate the matrix schema + every Go `implemented` entry via `go/ast` source parsing (handles `Type.Method` receivers and `excel:<ident>` sub-package references)
- Total: 1263 tests

**Performance** (canonical source — other docs may round or summarize these numbers):

*Benchmarks: 10,000 frames × 5 runs, AMD Ryzen 9 5950X, Linux 6.6 (WSL2). C++ g++-15 -O3, Go 1.26.1, Python 3.13.12.*

| Benchmark | C++ (fps) | Go (fps) | Python (fps) | Measured |
|---|---:|---:|---:|---|
| CAN 2.0B: Stream LTL (2 props) | **109,345** | 97,082 | 70,917 | 2026-04-06 |
| CAN 2.0B: Signal Extraction | **212,857** | 166,527 | 87,424 | 2026-04-06 |
| CAN 2.0B: Frame Building† | **76,469** | 71,692 | 55,093 | 2026-04-06 |
| CAN-FD: Stream LTL (3 props) | **48,248** | 47,516 | 34,737 | 2026-04-06 |
| CAN-FD: Signal Extraction | **14,930** | 14,493 | 12,143 | 2026-04-06 |
| CAN-FD: Frame Building† | **20,567** | 20,052 | 17,830 | 2026-04-06 |

† Frame Building rows have an additional post-fix 2026-04-08 measurement documented in the note immediately below the table; those numbers are not the canonical ones and are deliberately not substituted here.

> **Frame Building regression resolved (2026-04-08).** An earlier 30–65% regression on Frame Building rows (commit `5aa345e`, introduced by the `physicallyDisjoint?` Dec-valued check in `BatchFrameBuilding.hasOverlaps`) was traced via `git worktree` bisection and fixed by a Bool-valued fast path with formal equivalence proofs in `DBC/Properties.agda` (`signalsPhysicallyOverlapᵇ`, `physicallyOverlapᵇ-sound`, `physicallyOverlapᵇ-complete`). Per-signal physical bit lists are precomputed once in `hasOverlaps` and the O(m²) pair loop runs over cached lists with primitive ℕ equality — no `Dec` allocations on the hot path. See `project_frame_building_regression_2026_04_07.md` and AGENTS.md Category 16 for the cost-model lesson. The canonical numbers above still reflect the 2026-04-06 steady state; post-fix measurements (10000 frames × 5 runs, 2026-04-08) show Frame Building at C++ 58,712 / Go 65,106 / Python 47,789 (CAN 2.0B) and C++ 15,226 / Go 17,181 / Python 14,858 (CAN-FD) — a full +107–147% recovery on CAN-FD vs the regression state. The remaining gap (~10–25%) vs canonical reflects system noise plus residual list-representation overhead; further optimization is not blocked.

> **Note on C++ vs Go on Frame Building.** Frame Building is the only benchmark where Go can overtake C++, and the 2026-04-08 run does show Go +11% on CAN 2.0B and +13% on CAN-FD. This is not a C++ vs Go performance truth — it is benchmark geometry. Frame Building does the *least* Agda work per call and the *most* binding-side work, so per-call glibc `malloc` for the three scratch `std::vector`s in `AletheiaClient::build_frame` plus `std::unordered_map<SignalKey, uint32>` lookups become visible relative to Go's per-P bump allocator and built-in map. Stream LTL and Signal Extraction remain clearly C++-dominant. Future C++ optimizations (thread-local scratch buffers, small-vector, `ankerl::unordered_dense` / `absl::flat_hash_map`) would likely recapture the Frame Building lead but are not scheduled. See `project_cpp_vs_go_frame_building.md` for details.

- Build time: 0.26s (no-op), ~11s (incremental)
- Per-frame latency: ~9 us (CAN 2.0B streaming, C++)
- Memory: O(1) verified (1.08x growth across 100x trace increase)
- **Binary FFI**: All hot-path operations use binary FFI (no JSON parsing): `aletheia_send_frame` (streaming), `aletheia_extract_signals_bin`, `aletheia_build_frame_bin`, `aletheia_update_frame_bin`. All three bindings call the binary endpoints directly.
- **Single-threaded runtime**: Deployable to minimal containers (1 vCPU) with headroom over a 500 kbit/s CAN bus (~4,000 frames/sec). CAN-FD at 5 Mbit/s requires ~6,000 fps — all operations exceed this across all bindings (minimum: 12,143 fps Python CAN-FD extraction, 2x headroom).
- **Multi-bus scaling**: Each `AletheiaClient` has independent state (`StablePtr`). Multiple Python threads can monitor separate CAN buses in parallel. ctypes releases the GIL during FFI calls. For N buses on N vCPUs, pass `-N` to `hs_init` for parallel GHC capabilities.

**Verification**:
- All 119 Agda modules use `--safe --without-K` (4 also use `--no-main`)
- Zero postulates in production code
- All provable correctness properties proven (LTL adequacy, DBC validation, signal roundtrip, frame processing, predicate table, signal cache, response formatting, initial state, metric operator window bounds)
- **Pipeline soundness proven**: 8 unsound absorption rules removed, 4 remaining guarded with `finalizesHolds`, 2 structural idempotency rules added. `absorb-runL`, `simplify-runL`, `pipeline-adequate`, `production-adequate` all proven in `Adequacy/Pipeline.agda`
- **All verification suites green**: Python (basedpyright 0 errors, pylint 10.00/10), C++ (clang-format clean, clang-tidy clean, all ctest suites pass), Go (go test -race, go vet, gofmt all clean)

---

### Phase 6: Extensions & New Protocols (Planned)

**Scope**: Binding feature gaps, dependency cleanup, and automotive Ethernet support

**Binding feature gaps**:
- DBC `.dbc` text file parsing for C++ and Go (both accept pre-parsed DBC JSON; can't parse raw `.dbc` files client-side)
- Go multiplexing query helpers (expose queryable mux relationships)

**Toolchain upgrades**:
- Upgrade `basedpyright` and `pylint` to the latest stable releases, re-verify the 0/0/0 + 10.00/10 gates on the updated versions, and bump the upper pins in `python/pyproject.toml` (`basedpyright>=1.0,<2`, `pylint>=3.0,<4`) accordingly.

**LGPL contingency**:
- ~500 lines to eliminate cantools/python-can/libgmp if needed

**SOME/IP support**:
- Extend Aletheia to automotive Ethernet via SOME/IP (Scalable service-Oriented MiddlewarE over IP)
- SOME/IP is fundamentally different from CAN: service-oriented rather than signal-based, with a 16-byte header and variable structured payloads
- Requires new frame model, extraction logic, and LTL atomic predicates (service-level: response timing, subscription freshness, method sequencing)
- Existing LTL engine is reusable; also covers CAN-over-Ethernet (DoIP/ISO 13400)

**Status**: Not started

---

**End of Status Report**

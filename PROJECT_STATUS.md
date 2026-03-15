# Aletheia Project Status

**Last Updated**: 2026-03-15

---

## Current Position

**Phase 4 - Production Hardening** 🚧

Phases 1-3 complete. Phase 4 focuses on making Aletheia usable by non-developers
(automotive technicians, test engineers) and production-ready for deployment.

**Status**: Phase 4 in progress

**Latest Release**: v0.3.2 (Phase 3 complete)

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
- Throughput: 9,229 fps (108 us/frame via FFI)

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
   - `LTL/Bisimilarity.agda`: Proven behavioral bisimilarity between monitor and coalgebra
   - `step-bisim`: All 14 operators proven (Atomic, Not, And, Or, Next, Always, Eventually, Until, Release, MetricEventually, MetricAlways, MetricUntil, MetricRelease, NextActive)
   - `finalize-bisim`: All 14 operators proven — `finalizeEval st ≡ finalizeL proc` (propositional equality)
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
   - `LTL/SignalPredicate.agda`: SignalVal (True/False/Unknown/Pending), Kleene logic, SignalCache
   - `LTL/Incremental.agda`: Inconclusive state, safety vs liveness semantics
   - `LTL/Coalgebra.agda`: Mirrored Inconclusive handling for bisimilarity
   - `LTL/Bisimilarity.agda`: All 13 operator proofs updated for Inconclusive
   - Key improvement: No frame filtering needed - Unknown signals continue monitoring
6. ✅ Performance optimization - COMPLETE
   - Target: 8,000 fps (125 us/frame for 1 Mbps CAN bus)
   - Achieved: 9,229 fps (108 us/frame) — 2.88x speedup
   - Steps: GHC compiler flags, Fin→ℕ elimination, FFI shared library (eliminated IPC)

**Status**: Complete (started 2025-12-17)
**Completion**: 100% (6/6 goals complete)

---

### Phase 4: Production Hardening 🚧 IN PROGRESS

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
   - Returns `tuple[int, int, bytearray]` — feeds directly to `send_frame()`
   - Full public API migrated from `list[int]` to `bytearray`
   - Options: `skip_error_frames`, `skip_remote_frames`, `strict_dlc`, `on_error`

6. ✅ Richer violation diagnostics — COMPLETE
   - `CheckResult` carries `signal_name` and `condition_desc` from all builders
   - `AletheiaClient.send_frame()` auto-enriches violations: extracts signal value, builds human-readable reason
   - Bounded extraction cache (256 unique frames) keeps throughput above 8,000 fps target
   - `PropertyViolationResponse` extended with `signal_name`, `actual_value`, `condition` fields
   - CLI and all consumers get enriched violations for free via client-level enrichment

7. ✅ Deployment guide + install/uninstall — COMPLETE (Shakefile, `cabal run shake -- install`)

8. ✅ Tutorial / cookbook — COMPLETE (`docs/guides/TUTORIAL.md`, `docs/guides/COOKBOOK.md`, `docs/guides/QUICKSTART.md`)

9. ✅ DBC Validator — COMPLETE (not yet committed)
   - Agda: `DBC/Validator.agda` (new), `DBC/Types.agda`, `Data/Message.agda`, `Protocol/Routing.agda`, `Protocol/StreamState.agda`
   - `validateDBCFull : DBC → List ValidationIssue` — 7 structural checks, all issues accumulated
   - `IssueCode` enum: `DuplicateMessageId | DuplicateSignalName | FactorZero | MultiplexorNotFound | MultiplexorNotAlwaysPresent | GlobalNameCollision | MinExceedsMax`
   - Decidable types throughout (`_≟-CANId_`, `any?`, `_∈?_`)
   - Dual-layer validation: `parseDBC` runs both `validateDBC` + `validateDBCFull`
   - Python: `client.validate_dbc()`, `cli validate` subcommand, 11 FFI integration tests
   - 335 total tests pass, 0 regressions

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
- Renamed `ThreeVal` → `SignalVal` (now 4 constructors: True, False, Unknown, Pending)

**Documentation**: Interface Guide (`docs/reference/INTERFACES.md`) with Check API, YAML, and Excel
end-to-end workflows. Cross-linked from README, INDEX, and Python API Guide.

**Demos**: 10 demo scripts + data files in `examples/demo/`:
- `demo.py` (main presentation), `demo_check_api.py`, `demo_yaml_loader.py`, `demo_excel_loader.py`, `demo_all_interfaces.py`, `dbc_validation.py`, `frame_injection.py`, `drive_log.py`
- `engine_ecu_sim.py`, `test_engine_naive.py`, `demo_ltl_bug.py` (staleness demo)
- `demo_workbook.xlsx` (persistent Excel workbook for live demo)

**Status**: Complete (started 2026-02-06, Goals 1-3 complete 2026-02-07, Goal 5 complete 2026-02-08, Goal 4 complete 2026-02-15, Goal 6 complete 2026-02-16, Goals 7-8 complete 2026-02-17, Goal 9 complete 2026-02-19, Goals 10 + EOS fix complete 2026-02-21, Goal 11 complete 2026-02-22)
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
- `iterate-correct`: Property-list iteration ≡ forward specification (spec-equivalence)
- Signal predicate trust boundary documented (parametric by design)
- **Gap D modules** (`LTL/Semantics.agda`, `LTL/Adequacy.agda`, `LTL/Coalgebra.agda`) — ✅ COMPLETE:
  - Denotational LTLf semantics for all 13 operators (`⟦_⟧`) ✅
  - Coalgebra: Rosu formula progression with combineAnd/combineOr ✅
  - `Sound` relation (6-ctor monitoring soundness) ✅
  - **Rosu refactoring (10-step plan, 9 of 10 done)**:
    - ✅ Steps 18a–18h: All Rosu refactoring + adequacy theorem complete
    - ✅ Step 18i: Simplification — removed 429 lines of dead code (1490 → 1061)
    - Remaining: 18j (clean build + 344 Python tests + performance benchmarks)
    - Deleted: Bisimilarity.agda, CoalgebraBisim.agda, StepResultBisim.agda
  - **Adequacy theorem** (1061 lines): Four-layer proof (Sound compositionality → operational decomposition → soundness transport → non-recursive metric helpers). Zero postulates, zero holes.
- All proof modules use `--safe --without-K`
- All files type-check with zero holes

---

### Phase 5: Optional Extensions ⏳ PLANNED

**Scope**: Features driven by user feedback and real-world needs

**Planned**:
- Value tables and enumerations
- DBC pretty-printer
- Additional validation rules
- CAN format converters (BLF, ASC, MF4)
- Frame injection utilities

**Research needed**:
- Mixed byte order signals: Investigate prevalence of signals with different byte orders (Intel/Motorola) within the same CAN message, based on publicly available DBC files. Current batch proofs assume same byte order; mixed byte orders require different disjointness semantics due to DBC start bit conventions (LSB for Intel, MSB for Motorola).

**Status**: Not started

---

## Key Metrics

**Codebase**:
- Agda modules: 41
- Python modules: 11
- Lines of code: ~6,400 Agda + ~6,200 Python

**Testing**:
- Unit tests: 344 passing (via FFI)

**Performance**:
- Build time: 0.26s (no-op), ~11s (incremental)
- Throughput: 9,229 fps streaming LTL, 8,184 fps signal extraction
- Per-frame latency: 108 us
- Memory: O(1) verified (1.08x growth across 100x trace increase)

**Verification**:
- Safe modules: 38 of 41 use `--safe` (36 with `--without-K`, 2 variants)
- Coinductive modules: 3 use `--sized-types` (for infinite trace semantics)
- Zero postulates in production code

---

## Next Steps

**Current**:
- Gap D remaining step:
  - **Step 18j**: Clean build + 344 Python tests + principled performance benchmarks
  - Commit all Gap D changes (18i simplification not yet committed)
- Update docs (PYTHON_API.md, CLI.md) for new features.
- Additional DBC validation checks to research and implement.
- Refactor `CAN/DBCHelpers.agda` to use decidable types instead of raw `Bool`.

**Future**:
- Phase 5: Optional extensions (value tables, format converters, CAN-FD)

---

**End of Status Report**

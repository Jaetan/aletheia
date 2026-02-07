# Aletheia Project Status

**Last Updated**: 2026-02-06

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
   - All operators proven: Atomic, Not, And, Or, Next, Always, Eventually, Until, Release, MetricEventually, MetricAlways, MetricUntil, MetricRelease (12/12)
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
   - `LTL/SignalPredicate.agda`: ThreeVal (True/False/Unknown), Kleene logic, SignalCache
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

**Goals** (8 total):

1. ⏳ Check API — high-level property library (`python/aletheia/checks.py`)
   - Pre-built, parameterized automotive check patterns (range safety, rate limiting,
     response time, debounce, heartbeat/timeout, startup sequences)
   - Fluent API: `Check.signal("Speed").never_exceeds(220)` returns a `Property`
   - Industry vocabulary: "check", "never_exceeds", "stays_between", "when/then/within"
   - Designed for technicians: domain language, no LTL knowledge required
   - Each check includes docstring showing equivalent manual DSL form

2. ⏳ YAML loader (`python/aletheia/yaml_loader.py`)
   - Declarative check definitions in YAML files
   - Schema: signal + condition + value/limits + time constraint + severity
   - Supports simple checks and when/then response-time checks
   - Loadable via `load_checks("checks.yaml")` or CLI

3. ⏳ Excel loader (`python/aletheia/excel_loader.py`)
   - Read DBC definitions from Excel (Message ID, Signal Name, Start Bit, etc.)
   - Read check definitions from Excel (Signal, Condition, Limit, Time, Severity)
   - Provide downloadable .xlsx templates with headers and validation hints
   - Full workflow: `aletheia check --dbc vehicle.xlsx --checks tests.xlsx --log drive.csv`
   - Dependency: `openpyxl` (lightweight, standard)

4. ⏳ CLI tool (`python -m aletheia`)
   - `aletheia check` — run checks from YAML/Excel against a CAN log file
   - `aletheia extract` — extract signals from a single frame
   - `aletheia signals` — list signals in a DBC (or Excel)
   - No Python scripting required for common workflows

5. ⏳ CAN log reader (`python/aletheia/readers.py`)
   - CSV reader (lowest common denominator)
   - Vector ASC reader (common text-based format)
   - Bridge the gap between "I have a log file" and "I'm checking properties"

6. ⏳ Richer violation diagnostics
   - Include signal values at point of violation (not just property index + timestamp)
   - Human-readable violation summaries
   - Structured JSON output for CI/CD integration

7. ⏳ Deployment guide (`docs/DEPLOYMENT.md`)
   - Docker: Dockerfile example, multi-stage build, sysinfo.py sizing
   - systemd: service file for long-running monitor
   - CI/CD: GitHub Actions / GitLab CI snippets
   - Logging: structured JSON output for violations

8. ⏳ Tutorial / cookbook (`docs/TUTORIAL.md`)
   - End-to-end walkthrough for each tier (Excel, YAML, Check API, DSL)
   - Oriented toward learning (vs demo scripts which are presentation-oriented)
   - Separate paths for technicians and developers

**Status**: In progress (started 2026-02-06)

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
- Agda modules: 40
- Python modules: 8
- Lines of code: ~5,500 Agda + ~4,500 Python

**Testing**:
- Unit tests: 120 passing (0.17s via FFI)

**Performance**:
- Build time: 0.26s (no-op), ~11s (incremental)
- Throughput: 9,229 fps streaming LTL, 8,184 fps signal extraction
- Per-frame latency: 108 us
- Memory: O(1) verified (1.08x growth across 100x trace increase)

**Verification**:
- Safe modules: 37 of 40 use `--safe` (35 with `--without-K`, 2 variants)
- Coinductive modules: 3 use `--sized-types` (for infinite trace semantics)
- Zero postulates in production code

---

## Next Steps

**Current**:
- Phase 4: Production hardening — property library, CLI, log readers, diagnostics, deployment, tutorial

**Future**:
- Phase 5: Optional extensions (value tables, format converters, CAN-FD)

---

**End of Status Report**

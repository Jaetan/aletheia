# Aletheia Project Status

**Last Updated**: 2026-01-30

---

## Current Position

**Phase 3 - Verification + Performance** 🚧

Phase 2 is complete and released as v0.1.0-alpha. Moving to Phase 3 focusing on formal correctness proofs and performance optimization.

**Status**: Phase 3 in progress

**Previous Release**: v0.1.0-alpha (Phase 2 complete)

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
- Python StreamingClient (subprocess wrapper)

**Phase 2B.2 - Streaming LTL**:
- Incremental LTL evaluation (O(1) memory)
- Coinductive streaming interface
- Frame modification mid-stream
- Integration tests with memory profiling
- Throughput: ~10K frames/sec

**Phase 2B.3 - Polish**:
- Counterexample generation with violation details
- Rich error messages
- Python DSL refinement
- Performance tuning (parallel GHC)
- Comprehensive documentation

**Extension - Batch Signal Operations**:
- FrameBuilder: Build/update CAN frames with multiple signals
- SignalExtractor: Extract all signals with partitioned results
- Rich result objects (values/errors/absent signals)
- 32 unit tests

**Status**: 100% Complete

---

### Phase 3: Verification + Performance 🚧 IN PROGRESS

**Scope**: Formal correctness proofs and performance optimization

**Goals** (7 total):
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
5. ⏸️ Performance optimization (target: 1M frames/sec) - NOT STARTED
6. ⏸️ Parser memoization - NOT STARTED
7. ⏸️ Signal caching - NOT STARTED

**Status**: In progress (started 2025-12-17)
**Completion**: 57% (4/7 goals complete)

---

### Phase 4: Production Hardening ⏳ PLANNED

**Scope**: User-facing polish and robustness

**Planned**:
- Comprehensive error messages
- User documentation and tutorials
- Standard library of common LTL checks
- Edge case handling
- Production deployment guides

**Status**: Not started

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
- Unit tests: 146 passing
- Integration tests: Memory profiling, streaming protocol validation

**Performance**:
- Build time: 0.26s (no-op), ~11s (incremental)
- Throughput: ~10K frames/sec (streaming)
- Memory: O(1) verified (1.08x growth across 100x trace increase)

**Verification**:
- Safe modules: 37 of 40 use `--safe` (35 with `--without-K`, 2 variants)
- Coinductive modules: 3 use `--sized-types` (for infinite trace semantics)
- Zero postulates in production code

---

## Next Steps

**Phase 3 Remaining Goals**:
1. ⏸️ Performance optimization (target: 1M frames/sec, currently ~10K frames/sec)
2. ⏸️ Parser memoization
3. ⏸️ Signal caching

**Completed**:
- ✅ Parser soundness proofs
- ✅ LTL semantics proofs (bisimilarity, all operators)
- ✅ CAN encoding proofs (batch operations, disjointness preservation)
- ✅ DSL translation proofs (roundtrip, completeness)

**Future**:
- Phase 4: Production hardening, documentation, standard library
- Phase 5: Optional extensions (value tables, format converters)

---

**End of Status Report**

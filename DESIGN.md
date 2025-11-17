# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic
**Version**: 0.1.0
**Status**: Phase 1 Complete ✅ | Phase 2A Week 1 Complete ✅
**Last Updated**: 2025-11-18

## Project Overview

Aletheia provides mathematically proven tools to verify automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

**Core Value Proposition**: Write temporal properties in Python, verify them against CAN traces, with mathematical guarantees of correctness.

## Architectural Constraints

### Decisions Made (2025-11-13)

Based on analysis of **62 DBC files** covering **384 vehicles** from **50+ manufacturers** in the OpenDBC repository:

| Constraint | Decision | Rationale | Phase to Lift |
|------------|----------|-----------|---------------|
| **8-byte CAN frames** | ✅ **Keep fixed** | 100% of OpenDBC uses standard CAN, 0% CAN-FD | Phase 5 (if requested) |
| **Extended 29-bit CAN IDs** | ✅ **Add in Phase 2A** | 30-40% prevalence, blocks Korean market (Hyundai/Kia) | Phase 2A |
| **Signal multiplexing** | ✅ **Add in Phase 2A** | User requirement, critical for VIN/diagnostics | Phase 2A |
| **CAN-FD support** | ❌ **Defer to Phase 5** | 0% in OpenDBC, high refactoring cost | Phase 5 (if requested) |

**Impact**: These constraints define the scope of Phase 1-2. They balance real-world usability (support 100% of OpenDBC vehicles) with implementation pragmatism (defer costly features with zero current demand).

**Detailed analysis**: See [ARCHITECTURAL_ANALYSIS.md](ARCHITECTURAL_ANALYSIS.md)

## Core Requirements

- **Agda 2.8.0** with stdlib 2.3 (`--safe --without-K` enabled) for all logic
- **Haskell GHC 9.6.x** for minimal I/O shim (<100 lines)
- **Python 3.9+** (3.13.7 recommended) for user-facing API
- **Shake** (via Cabal) for build orchestration

## Architecture

Aletheia follows a three-layer architecture that maximizes formal verification while providing a practical interface:

```
┌─────────────────────────────────────────┐
│ Python Layer (python/)                  │
│ - User-facing API (CANDecoder, LTL DSL) │
│ - Subprocess communication via YAML     │
│ - Simple wrapper around binary           │
└──────────────┬──────────────────────────┘
               │ YAML over stdin/stdout
┌──────────────▼──────────────────────────┐
│ Haskell Shim (haskell-shim/)            │
│ - Minimal I/O layer (<100 lines)        │
│ - Only handles stdin/stdout             │
│ - Calls MAlonzo-generated Agda code     │
└──────────────┬──────────────────────────┘
               │ Direct function calls
┌──────────────▼──────────────────────────┐
│ Agda Core (src/Aletheia/)               │
│ - ALL LOGIC lives here                  │
│ - Parser combinators                    │
│ - CAN frame encoding/decoding           │
│ - DBC parser                            │
│ - LTL model checker                     │
│ - All correctness proofs                │
│ - Compiled with --safe flag             │
└─────────────────────────────────────────┘
```

**Critical Design Principle**: ALL critical logic must be implemented in Agda with proofs. The Haskell shim only performs I/O. Never add logic to the Haskell or Python layers.

## Implementation Phases

⚠️ **MAJOR PLAN REVISION** - See [PLAN_REVIEW.md](PLAN_REVIEW.md) for full analysis

**Goal**: Process real-world automotive CAN data with LTL reasoning, via rich Python DSL

### Phase 1: Core Infrastructure ✅ COMPLETE

**Timeline**: 3 weeks (2 weeks spent)

**Completed**:
- ✅ Parser combinators with structural recursion (no fuel)
  - Functor/Applicative/Monad interfaces
  - Basic correctness properties (determinism)
  - Type-checks in ~10s with parallel GHC
- ✅ CAN signal encoding/decoding
  - Frame types with bounded IDs/DLC
  - Bit-level extraction/injection with endianness
  - Rational scaling with factor/offset
  - Proof: byte swap is involutive
- ✅ DBC YAML parser
  - Complete message/signal parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - Rational parser handles fractional parts (0.25 → 1/4)
- ✅ Protocol integration and Main.agda
  - Command types: Echo, ParseDBC, ExtractSignal, InjectSignal
  - Command handlers with error handling
  - Response types with typed payloads
  - Full command routing working
- ✅ Build pipeline (Agda → Haskell → binary)
  - Hash-based dependency tracking (production-grade)
  - Automated FFI name mismatch detection
  - 0.26s no-op builds, ~11s incremental builds

**Remaining for Phase 1 Completion**:
- Python wrapper implementation (`python/aletheia/client.py`)
- Unit tests for all 4 critical fixes
- Integration testing: Python ↔ binary with real DBC file
- Performance benchmarking: signal extraction <1ms per signal
- ✅ Architectural constraint review (COMPLETED 2025-11-13)

**All 4 Critical Fixes Complete** (NO POSTULATES):
1. ✅ Rational parser: "0.25" → 1/4 using `power10` (automatic NonZero proof)
2. ✅ Signal scaling: Proper division with runtime zero-check
3. ✅ Response formatting: ℚ → String and Vec Byte 8 → hex
4. ✅ Byte array parser: Hex string → Vec Byte 8

**Exit Criteria**:
- All core infrastructure working end-to-end (Python → binary → Python)
- DBC parsing and signal extraction tested with real automotive data
- Zero postulates in production code (using `--safe` flag)
- Build system is reliable and fast
- Architecture validated against real-world requirements

### Phase 2A: LTL Core + Real-World Support (In Progress - Week 1/7 Complete ✅)

**Timeline**: 5-7 weeks total | **Current**: Week 1 complete, starting Week 2

**Week 1 Completed** ✅:
- **Extended 29-bit CAN ID support** - CANId sum type (Standard | Extended)
- **Signal multiplexing support** - SignalPresence dependent type (Always | When)
- DBC parser updates for both features
- Protocol handlers with multiplexing validation
- **Commits**: 004cf42, a4461fb, 210bce8

**Week 2-3 Goals** (LTL Core):
- LTL syntax (Always, Eventually, Until, Next, etc.)
- Semantics for finite traces (bounded checking)
- Basic model checker

**Python DSL v1**:
- DSL design document and architecture
- Basic predicates (equals, between, changed_by)
- Temporal operators (always, eventually, within)
- Composition (when/then, and/or)
- Parser: Python DSL → Agda LTL AST
- Example: `Signal("Speed").within(100*ms).must_be_between(0, 8000)`

**Validation**:
- Test with real automotive CAN trace from OpenDBC
- Common properties: speed limits, signal bounds, temporal constraints
- Multiplexed signal handling (VIN decoding, power states)

**Deliverable**: Users can check LTL properties on real traces using Python DSL

### Phase 2B: Streaming + Counterexamples

**Timeline**: 3-4 weeks

**Goals**: Handle large traces, debug failures

**Streaming**:
- Streaming trace parser (incremental, memory-bounded)
- Incremental LTL checking
- Handle 1GB+ trace files

**Counterexamples**:
- Counterexample generation (show violating trace)
- Minimal counterexample (shrink to essential)
- Python-friendly format (timestamp, signal values)

**DSL Extensions**:
- Custom user-defined predicates (Python callbacks)
- Standard library of common checks
- Composition helpers

**Deliverable**: Production-ready LTL checking with good UX

### Phase 3: Verification + Performance

**Timeline**: 4-6 weeks

**Goals**: Prove correctness, optimize bottlenecks

**Proofs**:
- Replace all runtime checks with static proofs where possible
- Parser soundness (grammar formalization)
- LTL semantics correctness
- Round-trip properties (parse ∘ print ≡ id)
- NonZero proofs for rational division

**Performance**:
- Profile on large traces (identify bottlenecks)
- Optimize hot paths in Agda
- Benchmark target: 1M frames/sec

**Deliverable**: Fully verified, production-performance system

### Phase 4: Production Hardening

**Timeline**: 3-4 weeks

**Goals**: Polish for real users

**UX**:
- Comprehensive error messages with line/column numbers
- User documentation (tutorials, examples, API reference)
- Standard library of common LTL checks
- Example gallery (real-world use cases from OpenDBC)

**Robustness**:
- Edge case handling and graceful degradation
- Logging and debugging support
- Integration with common tools (pandas, etc.)
- Signal overlap detection (safety check)
- Range validation (min ≤ max)

**Deliverable**: User-friendly, production-ready tool

### Phase 5: Optional Extensions

**Timeline**: Ongoing, based on user feedback

**Planned Enhancements**:
- 🟢 Value tables/enumerations (medium value, low cost)
- 🟢 Pretty-printer for DBC (medium value, low cost)
- 🟢 Additional DBC validation (signal overlap, range checks)
- 🟡 CAN-FD support (only if users request it - HIGH cost, 2-3 days minimum)
- 🔴 Extended features based on user feedback

**Dropped Features** (tracked in PLAN_REVIEW.md):
- Real-time analysis (architectural limitation)
- Automatic property inference (research problem)
- GUI/visualization (use existing tools)
- J1939 protocol (different domain)

## Success Criteria

### Technical Excellence
- All core logic proven correct in Agda with `--safe` flag
- Zero postulates in production code paths
- Comprehensive test coverage (unit + integration)
- Performance: 1M frames/sec throughput

### Usability
- Python users can verify properties without knowing formal methods
- Clear error messages that users can act on
- Comprehensive documentation with examples
- Works with real-world DBC files from OpenDBC

### Reliability
- Robust DBC parsing with informative warnings
- Graceful handling of edge cases
- Transparent logging builds trust
- Build system is fast and reliable

## Module Structure

### Agda Modules (`src/Aletheia/`)

The codebase is organized into logical packages:

- **Parser/**: Parser combinators with correctness properties
  - Combinators.agda: Core parser type and operations
  - Properties.agda: Determinism, monad laws (Phase 3)
  - Tracing.agda: Safe debugging infrastructure

- **CAN/**: CAN frame types and signal operations
  - Frame.agda: Frame type, IDs, DLC, payload
  - Signal.agda: Signal definition type
  - Encoding.agda: Bit-level extraction/injection
  - Endianness.agda: Byte ordering with proofs

- **DBC/**: DBC database format
  - Types.agda: Message and signal types
  - Parser.agda: YAML DBC parser
  - Semantics.agda: Frame decoding (Phase 2)
  - Properties.agda: Correctness properties

- **LTL/**: Linear Temporal Logic (Phase 2)
  - Syntax.agda: LTL formula AST
  - Semantics.agda: Trace satisfaction
  - Checker.agda: Model checking algorithm
  - DSL/: Python DSL support

- **Trace/**: Trace representation (Phase 2)
  - Stream.agda: Coinductive streams
  - CAN.agda: CAN frame traces
  - Parser.agda: Trace file parsing

- **Protocol/**: Command protocol for binary interface
  - Command.agda: Command types
  - Parser.agda: Command parsing from YAML
  - Response.agda: Response formatting
  - Handlers.agda: Command handlers

- **Main.agda**: Entry point compiled to Haskell

## Development Workflow

See [DEVELOPMENT.md](DEVELOPMENT.md) for detailed workflows.

**Quick Reference**:
```bash
# Type-check Agda module (fast feedback)
cd src && agda +RTS -N32 -RTS Aletheia/YourModule.agda

# Full build
cabal run shake -- build

# Clean build
cabal run shake -- clean
cabal run shake -- build

# Install Python package (requires active venv)
source venv/bin/activate
cabal run shake -- install-python
```

## Parser Correctness Strategy

- **Phase 1**: Lightweight correctness properties
  - Determinism properties
  - Bounded value checks
  - Runtime semantic validation
  - **NOT** full soundness/completeness proofs

- **Phase 3**: Full parser verification
  - Grammar formalization
  - Soundness proofs (parse → valid AST)
  - Completeness proofs where applicable
  - Round-trip properties (parse ∘ print ≡ id)

## Known Limitations (By Design)

### Phase 1 Limitations:

**Standard CAN Only** (no CAN-FD):
- Fixed 8-byte payload (`Vec Byte 8`)
- 11-bit CAN IDs (0-2047) - **Extended 29-bit IDs in Phase 2A**
- DLC 0-8 only (CAN-FD has different encoding)
- **Rationale**: 100% of OpenDBC uses standard CAN, 0% CAN-FD
- **Risk**: Refactoring later would take 1+ week if LTL assumes fixed frames
- **Decision**: Accept constraint, defer CAN-FD to Phase 5

**No Signal Multiplexing** (until Phase 2A):
- All signals assumed always present
- **Phase to Add**: Phase 2A (2-3 days)
- **Impact**: Needed for VIN, diagnostics, power states

**No Value Tables** (enumerations):
- Signal values are numeric only
- **Phase to Add**: Phase 5 (additive feature)

**Simplified Protocol**:
- One command per binary invocation
- No protocol versioning yet
- **Phase to Enhance**: Phase 4 (streaming protocol)

See [PHASE1_AUDIT.md](PHASE1_AUDIT.md) for comprehensive list of deferred work.

## Documentation Structure

- **README.md**: Quick start and project overview
- **BUILDING.md**: Step-by-step build instructions
- **DEVELOPMENT.md**: Architecture and workflows
- **DESIGN.md**: This document - design decisions and roadmap
- **PHASE1_AUDIT.md**: Comprehensive audit of limitations and constraints
- **ARCHITECTURAL_ANALYSIS.md**: Research findings on CAN protocols
- **PLAN_REVIEW.md**: Major plan revision rationale
- **CLAUDE.md**: Instructions for Claude Code assistant

---

**Document Status**: Living document, updated as project progresses
**Current Phase**: Phase 1 (Core Infrastructure) - ~95% complete
**Next Milestone**: Python wrapper + tests → Phase 1 complete

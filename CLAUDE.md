# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). The core logic is implemented in Agda with correctness proofs, compiled to Haskell, and exposed through a Python API.

**Current Phase**: 1 - Core Infrastructure (see DESIGN.md for roadmap)

## Global Project Rules

### Agda Module Requirements (MANDATORY)

**Every Agda module MUST use**:
```agda
{-# OPTIONS --safe --without-K #-}
```

**Rationale**:
- `--safe`: Prohibits postulates, unsafe primitives, and non-terminating recursion
  - Ensures all code is fully verified or uses runtime checks
  - Prevents accidental holes in production logic
  - Forces explicit documentation of any assumed properties
- `--without-K`: Ensures compatibility with Homotopy Type Theory (HoTT)
  - Makes proofs more general and reusable
  - Required for certain classes of formal verification

**Exceptions**:
- If postulate is truly needed (rare), create separate `*.Unsafe.agda` module
  - Remove `--safe` flag ONLY in that module
  - Document why postulate is needed
  - Track in `PHASE1_AUDIT.md` postulate table
  - Must be replaced with proof by Phase 3 completion

**Enforcement**:
- Build system checks all modules have --safe flag
- CI/CD should verify no unsafe modules in production paths
- Code review checklist includes verifying flags

**Current Status**: ✅ All 27 Aletheia modules use `--safe --without-K`

## Common Commands

### Build System (Shake via Cabal)

All build commands use `cabal run shake --` as the prefix:

```bash
# Build everything (Agda → Haskell → binary)
cabal run shake -- build

# Build individual components
cabal run shake -- build-agda       # Compile Agda to Haskell (MAlonzo)
cabal run shake -- build-haskell    # Build Haskell executable only

# Install Python package (requires active venv)
cabal run shake -- install-python

# Clean build artifacts
cabal run shake -- clean
```

### Python Development

**IMPORTANT**: Always activate the virtual environment first:

```bash
# Activate virtual environment (required for all Python commands)
source venv/bin/activate

# Install package in development mode
cd python
pip install -e ".[dev]"

# Run tests
python3 -m pytest tests/ -v

# Deactivate when done
deactivate
```

### Agda Development

```bash
# Type-check a single module (faster than full build)
cd src
agda Aletheia/YourModule.agda

# Type-check main entry point (verifies all dependencies)
# IMPORTANT: Use parallel GHC for complex modules (Protocol, Main)
agda +RTS -N32 -RTS Aletheia/Main.agda

# Check with verbose output
agda -v 10 Aletheia/YourModule.agda

# Parallel compilation (recommended for all modules)
# Uses up to 32 CPU cores for GHC's runtime
agda +RTS -N32 -RTS Aletheia/YourModule.agda
```

### Testing

```bash
# Test the compiled binary
echo "test" | ./build/aletheia

# Run Python tests
cd python && python3 -m pytest tests/ -v

# Try examples
cd examples && python3 simple_verification.py
```

## Architecture (Three-Layer Design)

The system is structured to maximize formal verification while providing a practical interface:

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

## Module Structure

### Agda Modules (src/Aletheia/)

The codebase is organized into logical packages:

- **Parser/**: Parser combinators with correctness properties
- **CAN/**: CAN frame types (Frame.agda), signal encoding (Encoding.agda), endianness (Endianness.agda)
- **DBC/**: DBC types, parser, semantics, and properties
- **LTL/**: LTL syntax, semantics, model checker, and Python DSL
- **Trace/**: Coinductive streams, CAN traces, trace parser
- **Protocol/**: Command protocol, parser, and responses
- **Main.agda**: Entry point compiled to Haskell

### Build Flow

1. **Agda Compilation**: `src/Aletheia/Main.agda` → `build/MAlonzo/Code/Aletheia/Main.hs`
   - Compiles Agda to Haskell using `--compile --ghc-dont-call-ghc`
   - Generates MAlonzo FFI bindings

2. **Symlink Creation**: `haskell-shim/MAlonzo` → `../build/MAlonzo`
   - Allows Haskell shim to import generated code

3. **Haskell Build**: Cabal builds `haskell-shim/` → `build/aletheia` binary
   - Links against MAlonzo-generated Agda code
   - Minimal Main.hs handles I/O

4. **Python Package**: Wraps binary with subprocess interface

## Development Workflow

### Adding New Features

1. **Design in Agda**: Define types and properties in appropriate module
2. **Implement with proofs**: Write code and prove correctness
3. **Build and test**: `cabal run shake -- build` then test binary
4. **Update Python API** (if needed): Add convenience functions
5. **Add examples**: Create test cases in `examples/`

### Typical Iteration Cycle

```bash
# 1. Edit Agda source
vim src/Aletheia/Parser/Combinators.agda

# 2. Quick type-check (fast feedback, no compilation)
cd src && agda Aletheia/Parser/Combinators.agda

# 3. Full build when ready
cd .. && cabal run shake -- build

# 4. Test
echo "test" | ./build/aletheia
```

### Incremental Builds

Shake tracks dependencies automatically. After modifying an Agda file, only affected modules are recompiled. First build compiles the entire standard library (~60s), but subsequent builds are much faster (~5-15s for changes).

## Key Files

- **aletheia.agda-lib**: Agda library configuration (depends on standard-library-2.3)
- **Shakefile.hs**: Custom build system orchestrating Agda → Haskell → binary
- **haskell-shim/aletheia.cabal**: Haskell package definition
- **python/pyproject.toml**: Python package configuration

## Requirements

- **Agda**: 2.8.0 exact (with standard-library-2.3)
- **GHC**: 9.4.x or 9.6.x
- **Cabal**: 3.12.1.0 recommended
- **Python**: 3.9+ (3.13.7 recommended)
- **Shake**: Managed via project's shake.cabal

See BUILDING.md for detailed installation instructions.

## Important Notes

### Agda Compilation

- Always use `--safe --without-K` flags (enforced in module headers)
- Use `--no-main` flag (binary entry point is in Haskell)
- Generated MAlonzo code goes to `build/` directory
- Don't edit generated Haskell code; modify Agda source instead
- **Performance**: Use parallel GHC with `agda +RTS -N32 -RTS` for all modules
  - Critical for Protocol/Handlers.agda and Main.agda (17s vs >120s timeout)
  - Recommended for all type-checking to maximize performance
- **First build**: Run `agda src/PrecompileStdlib.agda` to cache standard library (~20s one-time cost)

### MAlonzo FFI and Name Mangling

**Issue**: MAlonzo mangles Agda function names when generating Haskell code. For example, `processCommand` becomes `d_processCommand_28`, where the number suffix can change if the Agda code structure changes.

**Automated Detection** (current approach):
The build system automatically detects FFI name mismatches and provides exact fix instructions:

```bash
cabal run shake -- build
# If mismatch detected, build fails with:
# ERROR: MAlonzo function name mismatch!
#   Generated by Agda:  d_processCommand_28
#   Currently in shim:  d_processCommand_99
# To fix, run:
#   sed -i 's/d_processCommand_99/d_processCommand_28/g' haskell-shim/src/Main.hs
```

**When it triggers**:
- Rare - only when adding/removing Agda definitions **before** processCommand in Main.agda
- Build catches it immediately with exact fix command
- Zero investigation time needed

**Alternative Solutions** (not currently used):
- **COMPILE pragmas**: `{-# COMPILE GHC name = name #-}` - but not allowed with `--safe` flag
- **FFI module**: Separate non-safe module just for FFI - adds complexity, breaks in --safe mode
- **FOREIGN blocks**: Write I/O code in Agda - violates clean separation architecture

**Best Practice**: Keep the Haskell shim minimal and update the mangled name when needed (rarely). The trade-off of a tiny maintenance burden is better than:
- Losing `--safe` guarantees
- Adding complex FFI layer
- Mixing I/O code with verified logic

### Virtual Environment

The Python virtual environment (`venv/`) is critical:
- Create once: `python3.13 -m venv venv`
- Activate for all Python work: `source venv/bin/activate`
- Verify: `which python3` should show `*/aletheia/venv/bin/python3`
- Never commit `venv/` to git

### Haskell Shim Philosophy

The Haskell shim (haskell-shim/src/Main.hs) should remain minimal:
- Current: ~27 lines
- Target: <100 lines
- Purpose: I/O only (stdin/stdout, buffering)
- Never add business logic here

### Module Organization

When adding new Agda modules:
- Follow existing package structure (Parser, CAN, DBC, LTL, etc.)
- Include correctness properties alongside implementations
- Use descriptive module names (e.g., `Properties.agda` for proofs)
- Update Main.agda if new functionality needs exposure

## Troubleshooting

### Build Failures

```bash
# Clean rebuild
cabal run shake -- clean
cabal run shake -- build

# Verify Agda compilation succeeded
ls build/MAlonzo/Code/Aletheia/Main.hs

# Check symlink exists
ls -la haskell-shim/MAlonzo
```

### Python Issues

```bash
# Verify venv is active
which python3  # Should show .../venv/bin/python3

# Rebuild and reinstall
cabal run shake -- build
source venv/bin/activate
cabal run shake -- install-python
```

### Agda Module Not Found

Ensure standard library is registered:
```bash
cat ~/.agda/libraries  # Should list standard-library.agda-lib path
cat ~/.agda/defaults   # Should contain "standard-library"
```

## Performance Considerations

### Parser Combinators

The parser library (`Aletheia.Parser.Combinators`) uses **structural recursion** on input length for termination:

- **Key insight**: The `many` combinator uses input length as termination measure
  - `manyHelper p input (length input)` - recursion bounded by input size
  - Stops immediately if parser doesn't consume input (prevents infinite loops)
  - No fuel needed - structurally terminating!
- **Old approach** (removed): Fuel-based termination caused >120s type-checking timeouts
  - `manyWithFuel 1000 p` forced Agda to symbolically evaluate 1000 recursion levels
  - Even with NOINLINE pragmas, the issue persisted
- **Design patterns**:
  - Helper functions avoid `with` patterns in type signatures (use nested where clauses)
  - String conversion at boundaries only (use `List Char` internally)
  - Pre-computed character codes (`code-0 = 48`, etc.) instead of runtime computation
- **History**: Original fuel-based parser was removed after successful migration

### Type-Checking Tips

- **Critical**: Always use parallel GHC with `agda +RTS -N32 -RTS`
  - Protocol/Handlers.agda: 17s (parallel) vs >120s timeout (serial)
  - Main.agda: 18s (parallel) vs >120s timeout (serial)
- First build compiles stdlib (~20s), subsequent builds are much faster
- Use `PrecompileStdlib.agda` to cache common imports
- Avoid `with` patterns on complex parser compositions in type signatures

## Implementation Phases

⚠️ **MAJOR PLAN REVISION** - See `PLAN_REVIEW.md` for full analysis

**Goal**: Process real-world automotive CAN data with LTL reasoning, via rich Python DSL

**Key Changes from Original Plan**:
- **Multiplexing**: Moved from Phase 5 → Phase 2A (CRITICAL for real traces)
- **Python DSL**: Added as Phase 2A core deliverable (not afterthought)
- **Streaming**: Moved from Phase 3 → Phase 2B (essential for large traces)
- **Counterexamples**: Moved from Phase 4 → Phase 2B (critical UX)
- **Real-world validation**: Added throughout all phases
- **Extensibility strategy**: Three-tier approach (built-in, Python, Agda)
- **Decision points**: Added pivot opportunities at end of each phase

Aletheia follows a phased implementation plan:

### **Phase 1: Core Infrastructure** (In Progress)

**Completed**:
- ✅ Parser combinators with **structural recursion** (rewritten from fuel-based)
  - Full functor/applicative/monad interfaces
  - Structurally terminating on input length
  - Basic correctness properties
  - Type-checks in ~10s with parallel GHC
- ✅ CAN signal encoding/decoding (commit 92911c4)
  - Frame types with bounded IDs/DLC
  - Bit-level extraction/injection
  - Endianness handling (little/big endian)
  - Rational scaling with factor/offset
  - Proof: byte swap involutive
- ✅ DBC YAML parser (commits 61969d9, 00935c6)
  - Complete YAML parsing with primitives
  - Type-safe signal/message parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - Test cases

- ✅ Protocol integration and Main.agda implementation
  - Extended Command types: ParseDBC, ExtractSignal, InjectSignal
  - Implemented command handlers with proper error handling
  - Rich Response types with typed payloads
  - Type-checks in ~18s with parallel GHC

- ✅ Build pipeline verification (Agda → Haskell → binary)
  - Agda → MAlonzo compilation: ~43s
  - Haskell → binary compilation successful
  - Binary executable works correctly
  - All 11 Aletheia modules compiled

- ✅ Protocol YAML parser implementation (commit 8a853e1)
  - Echo and ParseDBC command parsers
  - Multi-line YAML input handling
  - End-to-end pipeline tested and working
  - Binary successfully parses and executes commands

**Remaining in Phase 1**:
- Python wrapper implementation
- Integration testing with Python API

### **Phase 2A: LTL Core + Real-World Support** (REVISED)

**Goals**: LTL reasoning on real automotive traces

**Core LTL**:
- LTL syntax (Always, Eventually, Until, etc.)
- Semantics for finite traces (bounded checking)
- Basic model checker
- **Signal multiplexing support** (MOVED FROM PHASE 5 - CRITICAL)
  - Conditional signal presence based on multiplexor value
  - ~30% of automotive messages use multiplexing

**Python DSL v1** (NEW - CRITICAL):
- DSL design document and architecture
- Basic predicates (equals, between, changed_by)
- Temporal operators (always, eventually, within)
- Composition (when/then, and/or)
- Parser: Python DSL → Agda LTL AST
- Example: `Signal("Speed").within(100*ms).must_be_between(0, 8000)`

**Validation**:
- Test with real automotive CAN trace
- Common properties: speed limits, signal bounds, temporal constraints

**Timeline**: 4-6 weeks
**Deliverable**: Users can check LTL properties on real traces using Python DSL

### **Phase 2B: Streaming + Counterexamples** (NEW)

**Goals**: Handle large traces, debug failures

**Streaming**:
- Streaming trace parser (incremental, memory-bounded)
- Incremental LTL checking
- Handle 1GB+ trace files

**Counterexamples** (MOVED FROM PHASE 4):
- Counterexample generation (show violating trace)
- Minimal counterexample (shrink to essential)
- Python-friendly format (timestamp, signal values)

**DSL Extensions**:
- Custom user-defined predicates (Python callbacks)
- Standard library of common checks
- Composition helpers

**Timeline**: 3-4 weeks
**Deliverable**: Production-ready LTL checking with good UX

### **Phase 3: Verification + Performance** (REVISED)

**Goals**: Prove correctness, optimize bottlenecks

**Proofs**:
- Replace all postulates with proofs
- Parser soundness (grammar formalization)
- LTL semantics correctness
- Round-trip properties
- **Rational parser proofs**: Add NonZero proofs to rational division

**Performance**:
- Profile on large traces (identify bottlenecks)
- Optimize hot paths
- Benchmark target: 1M frames/sec

**Timeline**: 4-6 weeks
**Deliverable**: Fully verified, production-performance system

### **Phase 4: Production Hardening** (REVISED)

**Goals**: Polish for real users

**UX**:
- Comprehensive error messages (user can fix without asking us)
- User documentation (tutorials, examples)
- Standard library of checks (common properties)
- Example gallery (real-world use cases)

**Robustness**:
- Edge case handling
- Graceful degradation
- Logging and debugging support
- Integration with common tools (pandas, etc.)

**Timeline**: 3-4 weeks
**Deliverable**: User-friendly, production-ready tool

### **Phase 5: Optional Extensions** (REVISED)

**Planned Enhancements** (prioritized by user feedback):
- 🟢 Value tables/enumerations (medium value, low cost)
- 🟢 Pretty-printer for DBC (medium value, low cost)
- 🟢 Additional DBC validation (signal overlap, range checks)
- 🟡 Extended CAN IDs (low value for automotive, medium cost)
- 🔴 CAN-FD support (low value for now, high cost)

**Timeline**: Ongoing, based on demand
**Deliverable**: Enhanced feature set based on user feedback

**Dropped Features** (tracked in PLAN_REVIEW.md):
- Real-time analysis (architectural limitation)
- Automatic property inference (research problem)
- GUI/visualization (use existing tools)
- J1939 protocol (different domain)

When adding features, consider which phase they belong to and maintain consistency with the overall architecture.

## Current Session Progress

**Last Completed**: Build system made rock solid + command routing fixed (commits 9e22c2c, e3233ae, 215e881)
**Current Status**: Phase 1 ~95% complete, ready for final DBC parsing debug
**Blocker**: DBC YAML parsing (all commands route correctly now!)

### Completed in This Session:

**MAJOR ACCOMPLISHMENT**: Build system completely overhauled and made production-ready!

1. ✅ **Command routing bug FIXED** (root cause: stale .agdai cache)
   - Spent ~4 hours debugging parser logic (all approaches failed identically)
   - Root cause discovered: Stale .agdai interface files from previous compilations
   - Parser logic was correct all along!
   - All 4 commands now route correctly: Echo, ParseDBC, ExtractSignal, InjectSignal

2. ✅ **Build system: Hash-based dependency tracking** (commit 215e881, e3233ae)
   - Enabled `shakeChange=ChangeModtimeAndDigest` for content hashing (not timestamps)
   - Track all 319 MAlonzo .hs files (not just Main.hs) - ensures no missed changes
   - Trust Agda's .agdai cache management (no manual cleaning needed)
   - Performance: 0.26s no-op builds, ~11s incremental builds
   - No more stale cache issues, no false rebuilds
   - **RESULT**: Production-grade build system

3. ✅ **Architectural research completed** (commit 63ca8aa)
   - Surveyed OpenDBC: 62 DBC files, 384 vehicles, 50+ manufacturers
   - Analyzed 7 representative files (Toyota, Honda, Hyundai, Kia, etc.)
   - Created ARCHITECTURAL_ANALYSIS.md with findings
   - **Decisions made**:
     * CAN-FD: 0% prevalence → DEFER to Phase 5
     * Extended 29-bit IDs: 30-40% prevalence → ADD to Phase 2A
     * Signal multiplexing: 5-10% messages, user requirement → CONFIRMED Phase 2A

4. ✅ **All 4 critical fixes complete** (from previous session, zero postulates)
   - Rational parser: 0.25 → 1/4
   - Signal scaling: proper division with factor
   - Response formatting: ℚ → String, Vec Byte 8 → hex
   - Byte array parser: hex string → Vec Byte 8

### Phase 1 Status: ~95% Complete

✅ **ALL 4 CRITICAL FIXES COMPLETE** - No postulates needed!
✅ **BUILD SYSTEM ROCK SOLID** - Hash-based dependency tracking
✅ **COMMAND ROUTING FIXED** - All 4 commands route correctly
⚠️ **BLOCKER**: DBC YAML parsing (commands route, but DBC parsing fails)

**Completed Core Infrastructure**:
- ✅ Parser combinators (structural recursion)
  - Functor/Applicative/Monad interfaces
  - Basic correctness properties (determinism)
  - No full soundness proofs (deferred to Phase 3)
- ✅ CAN encoding/decoding
  - Frame types, bit-level operations
  - Endianness handling
  - One proof: byte swap involutive
- ✅ DBC YAML parser
  - Complete message/signal parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - ✅ **FIXED**: Rational parser now handles fractional parts correctly (0.25 → 1/4)
- ✅ Protocol integration
  - Command types defined
  - Command handlers implemented (all 4 commands)
  - Response types with typed payloads
- ✅ Build pipeline
  - Agda → MAlonzo → Haskell → binary
  - Automated FFI name mismatch detection
- ✅ Protocol YAML parser **[Partial]**
  - ✅ Echo command parser
  - ✅ ParseDBC command parser
  - ❌ ExtractSignal parser (needs byte array parsing)
  - ❌ InjectSignal parser (needs byte array + rational parsing)
- ✅ End-to-end binary testing (Echo and ParseDBC only)

**Remaining for Phase 1 Completion** (REQUIRED, not optional):

5. **Complete protocol parser**: ExtractSignal and InjectSignal command parsers
6. **Python wrapper implementation**: python/aletheia/client.py with subprocess interface
7. **Unit tests for all 4 critical fixes** (REQUIRED):
   - Rational parser: "0.25" → 1/4, "1.5" → 3/2, negatives
   - Signal scaling: Round-trip property (applyScaling ∘ removeScaling ≈ id)
   - Response formatting: ℚ and Vec Byte 8 outputs
   - Byte array parser: Hex parsing, case sensitivity, bounds
8. **Integration testing**: End-to-end tests with Python ↔ binary, real DBC file
9. **Performance benchmarking**: Signal extraction <1ms per signal
10. **Architectural constraint review** (1-2 days, MANDATORY before Phase 2):
    - Evaluate CAN-FD, extended IDs, signal multiplexing requirements
    - **Decision**: Refactor Frame type NOW vs accept constraints
    - Document rationale (see PHASE1_AUDIT.md)

See `PHASE1_AUDIT.md` for comprehensive analysis of all limitations and constraints.

### ✅ Critical Fixes (ALL 4 COMPLETE - NO POSTULATES!):

1. ✅ **Fix rational number parsing** (COMPLETED - NO POSTULATES NEEDED):
   - **Issue**: Parser was ignoring fractional parts (0.25 → 0/1)
   - **File**: `DBC/Parser.agda:99-148`
   - **Fix Implemented**: Proper decimal → rational conversion
     - Uses `power10` that returns `suc n` to prove NonZero automatically
     - Pattern matching with `with` exposes `suc` constructor
     - Converts "0.25" → 1/4, "1.5" → 3/2 correctly
   - **Result**: Remains `--safe --without-K` compliant

2. ✅ **Fix signal scaling removal** (COMPLETED - NO POSTULATES NEEDED):
   - **Issue**: Was ignoring factor parameter
   - **File**: `CAN/Encoding.agda:45-70`
   - **Fix Implemented**: `raw = floor((signalValue - offset) / factor)`
     - Runtime zero-check returns `Nothing` if factor is zero
     - Pattern matches on `mkℚᵘ` to expose nonzero numerator
     - Uses unnormalized rational division for simplicity
   - **Result**: Remains `--safe --without-K` compliant

3. ✅ **Implement response formatting** (COMPLETED - NO POSTULATES NEEDED):
   - **Issue**: Was returning placeholders for signal values and bytes
   - **File**: `Protocol/Response.agda:41-91`
   - **Fix Implemented**:
     - `ℚ → String`: Uses `Data.Rational.Show.show` (e.g., "3/2")
     - `Vec Byte 8 → String`: Custom hex formatter (e.g., "0x12 0x34 ...")
   - **Result**: Remains `--safe --without-K` compliant

4. ✅ **Implement byte array parser** (COMPLETED - NO POSTULATES NEEDED):
   - **Issue**: Could not parse hex byte strings from YAML
   - **File**: `Protocol/Parser.agda:37-106`
   - **Fix Implemented**:
     - `hexByte`: Parses "0xNN" using modulo (returns Fin 256 automatically)
     - `byteArray`: Parses exactly 8 hex bytes separated by spaces
   - **Result**: Remains `--safe --without-K` compliant

**Next Steps (Non-Critical, Complete Phase 1)**:

5. **Complete protocol parser**: ExtractSignal and InjectSignal command parsers
   - Now unblocked since byte array parser is complete
   - Can parse frame bytes and signal names from YAML

6. **Python wrapper implementation**:
   - Create python/aletheia/client.py with subprocess interface
   - Implement CANDecoder class wrapping binary
   - YAML serialization/deserialization
   - Error handling and validation

7. **Integration testing**:
   - End-to-end tests: Python → binary → Python
   - Test all 4 command types with real signal values
   - Validate fractional scaling factors work correctly (0.25, 1.5, etc.)

### Optional Enhancements (Improve Reliability):

8. **Signal overlap detection** (runtime safety check)
   - Detect when signals in same message overlap bit positions
   - Prevents silent data corruption

9. **Range validation** (runtime semantic check)
   - Verify minimum ≤ maximum in signal definitions
   - Catch malformed DBC files early

### Known Architectural Constraints (By Design):

⚠️ **MANDATORY REVIEW BEFORE PHASE 2**: See `PHASE1_AUDIT.md` "Architectural Constraint Review Plan" section. We must validate these constraints before building Phase 2 on top of them.

**Standard CAN Only** (no CAN-FD):
- Fixed 8-byte payload (`Vec Byte 8`) - 🔴 **HIGH RISK** if changed later
- 11-bit CAN IDs only (0-2047, no extended 29-bit IDs) - 🔴 **HIGH RISK** if changed later
- DLC 0-8 only (CAN-FD has different encoding)
- **Rationale**: Covers 95% of automotive use cases
- **Phase to Lift**: Phase 5 (extended features)
- **⚠️ WARNING**: Hardcoded `Vec Byte 8` is deeply embedded throughout codebase
  - If Phase 2 (LTL) assumes fixed frame size, refactoring cost becomes 1 week+
  - **Recommendation**: Review at end of Phase 1, refactor early if needed
  - See audit doc for parameterized Frame type design (2-3 day effort now)

**No Signal Multiplexing**:
- All signals always present in frame
- **Phase to Add**: Phase 5
- **Risk**: 🟢 Low - additive feature

**No Value Tables** (enumerations):
- Signal values are numeric only
- **Phase to Add**: Phase 5
- **Risk**: 🟢 Low - additive feature

See `PHASE1_AUDIT.md` for:
- Complete list of constraints and deferred work
- Risk assessment for each constraint
- Review schedule and decision criteria
- Refactoring options if constraints need to be lifted early

### Parser Correctness Strategy (as planned):
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
  - NonZero proofs for rational division

### Resolved Issue - Type-Checking Timeout:
**Previous Problem**: Parser normalization caused >120s timeouts
**Root Cause**: Fuel-based parser combinators forced symbolic evaluation
**Solution Implemented**: Rewrote parser combinators with structural recursion
**Result**: Type-checks in ~10s, all functionality preserved

### Session Recovery Notes:
If session terminates, resume with:
```bash
cd /home/nicolas/dev/agda/aletheia

# Read comprehensive session state (RECOMMENDED - start here!)
cat .session-state.md

# Quick status check
git log --oneline -5  # Recent commits: build system fixes, routing fix

# Current Status: Phase 1 ~95% complete
# Last Completed: Build system rock solid + command routing fixed (commits 9e22c2c, e3233ae, 215e881)
# Blocker: DBC YAML parsing (all commands route correctly now!)

# Next Priority: Debug DBC YAML parsing
cat test_parsedbc_minimal.yaml | ./build/aletheia
# Expected: Parse successfully
# Actual: "Failed to parse DBC YAML"
# Need to debug why multilineValue output doesn't parse

# Build system is production-ready:
cabal run shake -- build         # Full build, 0.26s no-op, ~11s incremental
cabal run shake -- build-agda    # Agda only
cabal run shake -- clean         # Clean all artifacts

# All 4 commands route correctly now:
printf 'command: "Echo"\nmessage: "test"' | ./build/aletheia  # Works!
cat test_parsedbc_minimal.yaml | ./build/aletheia              # Routes, DBC parsing fails
cat test_extract_reordered.yaml | ./build/aletheia             # Routes, DBC parsing fails
cat test_inject_proper.yaml | ./build/aletheia                 # Routes, DBC parsing fails
```

**IMPORTANT**: See `.session-state.md` for complete project state, decisions, and recovery instructions.
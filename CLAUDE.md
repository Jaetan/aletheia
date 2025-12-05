# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). The core logic is implemented in Agda with correctness proofs, compiled to Haskell, and exposed through a Python API.

**Current Phase**: 2 - LTL + Real-World Support (Phase 2B.1 Complete, Quality Improvements In Progress)

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
  - Must be replaced with proof by Phase 3 completion

**Enforcement**:
- Build system checks all modules have --safe flag
- CI/CD should verify no unsafe modules in production paths
- Code review checklist includes verifying flags

**Current Status**: ✅ All 27 Aletheia modules use `--safe --without-K`

### Modules Not Using --safe Flag

Four modules require extensions incompatible with --safe:

1. **Main.agda** - Uses `--sized-types` for coinductive LTL checking
   - Required for: MAlonzo compilation with coinductive LTL evaluation
   - Safety trade-off: Entry point marshals between Agda and Haskell I/O

2. **LTL/Coinductive.agda** - Uses `--guardedness --sized-types` for infinite trace semantics
   - Required for: Coinductive streams representing infinite traces
   - Safety trade-off: Productivity checking via --guardedness instead of --safe

3. **Protocol/StreamState.agda** - Uses `--guardedness --sized-types` for streaming LTL checking
   - Required for: Coinductive stream processing of large trace files
   - Safety trade-off: Productivity checking via --guardedness instead of --safe

4. **Data/DelayedColist.agda** - Uses `--guardedness --sized-types` for coinductive stream type
   - Required for: Thunk-based delay in infinite traces
   - Safety trade-off: Productivity checking via --guardedness instead of --safe
   - Used by: LTL/Coinductive for infinite trace semantics

**Rationale**: Coinductive types (required for infinite traces and streaming) need `--guardedness` for productivity checking, which is incompatible with `--safe`. This is an intentional and documented trade-off for the LTL subsystem.

**Verification Status**: All four modules use only standard library coinductive types and primitives. No postulates or unsafe operations are used.

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

See [Architecture Overview](docs/architecture/DESIGN.md#architecture) for the three-layer design diagram.

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
  - Critical for Protocol/StreamState.agda and Main.agda (17s vs >120s timeout)
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
- Current: 54 lines
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
  - Protocol/StreamState.agda: 17s (parallel) vs >120s timeout (serial)
  - Main.agda: 18s (parallel) vs >120s timeout (serial)
- First build compiles stdlib (~20s), subsequent builds are much faster
- Use `PrecompileStdlib.agda` to cache common imports
- Avoid `with` patterns on complex parser compositions in type signatures

## Implementation Phases

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

### **Phase 1: Core Infrastructure** ✅ (Complete)

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
- ✅ DBC JSON parser (migrated from YAML in Phase 2B)
  - Complete JSON parsing with primitives
  - Type-safe signal/message parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - Test cases

- ✅ Protocol integration and Main.agda implementation
  - Extended Command types: ParseDBC, SetProperties, StartStream, EndStream
  - Implemented command handlers with proper error handling
  - Rich Response types with typed payloads
  - Type-checks in ~18s with parallel GHC

- ✅ Build pipeline verification (Agda → Haskell → binary)
  - Agda → MAlonzo compilation: ~43s
  - Haskell → binary compilation successful
  - Binary executable works correctly
  - All 27 Aletheia modules compiled

- ✅ Protocol JSON parser implementation (Phase 2B streaming protocol)
  - All streaming commands: parseDBC, setProperties, startStream, endStream
  - JSON line protocol (one command per line)
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

**Documentation** (Priority):
- Python API reference with clear examples
- LTL property JSON format specification
- "Why Formal Verification?" guide for non-technical stakeholders
  - Target: Python developers and managers unfamiliar with formal methods
  - Must be candid, precise, concise
  - Address concerns: complexity, overhead, when it's worth it
  - Explain what guarantees you get vs traditional testing

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
- 🔴 CAN-FD support (low value for now, high cost)

**Timeline**: Ongoing, based on demand
**Deliverable**: Enhanced feature set based on user feedback

When adding features, consider which phase they belong to and maintain consistency with the overall architecture.

## Current Session Progress

**Last Completed**: Phase 1 100% complete! All critical bugs fixed (commits 8fc48a3, 60a94a4, ca619bb)
**Current Status**: Ready to begin Phase 2A - LTL Core + Real-World Support
**Major Achievement**: Fixed two critical pattern matching bugs (shiftR and power10)

### Completed in This Session:

**MAJOR ACCOMPLISHMENT**: Phase 1 Complete - All Critical Bugs Fixed!

1. ✅ **Fixed shiftR pattern matching bug** (commit 8fc48a3)
   - **Issue**: Bit extraction returning wrong values (0x09 → 5 instead of 9)
   - **Root cause**: `shiftR (suc value) (suc n)` bound `value` to inner number
   - **Fix**: Changed to `shiftR value (suc n)` to divide full value
   - **Time**: ~6 hours debugging
   - **Result**: ALL bit extraction tests pass

2. ✅ **Fixed power10 pattern matching bug** (commit 60a94a4)
   - **Issue**: Rational parsing incorrect (0.25 → 5/42 instead of 1/4)
   - **Root cause**: `suc (9 + prev * 10)` treated `suc m` as `m+1`
   - **Fix**: Pattern match with `with` to extract `m`, use `10 * m`
   - **Time**: ~30 minutes debugging
   - **Result**: ALL rational parsing tests pass

3. ✅ **Python wrapper implementation** (Phase 2B)
   - StreamingClient with subprocess interface to binary
   - JSON line protocol (one command per line)
   - All streaming commands: parseDBC, setProperties, startStream, endStream, send_frame
   - Proper error handling and validation
   - Python DSL for LTL properties (Signal().less_than().always())

4. ✅ **Build system: Production-ready** (previous session)
   - Hash-based dependency tracking
   - Automated FFI name mismatch detection
   - 0.26s no-op builds, ~11s incremental builds

### Phase 1 Status: 100% Complete! 🎉

✅ **ALL CRITICAL BUGS FIXED** - Both pattern matching issues resolved
✅ **BUILD SYSTEM ROCK SOLID** - Hash-based dependency tracking
✅ **ALL 4 COMMANDS WORKING** - Echo, ParseDBC, ExtractSignal, InjectSignal
✅ **END-TO-END SIGNAL EXTRACTION** - Bit extraction + scaling both work perfectly

**Completed Core Infrastructure**:
- ✅ Parser combinators (structural recursion)
  - Functor/Applicative/Monad interfaces
  - Basic correctness properties (determinism)
  - No full soundness proofs (deferred to Phase 3)
- ✅ CAN encoding/decoding
  - Frame types, bit-level operations
  - Endianness handling
  - One proof: byte swap involutive
- ✅ DBC JSON parser (migrated from YAML in Phase 2B)
  - Complete message/signal parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - ✅ **FIXED**: Rational parser now handles fractional parts correctly (0.25 → 1/4)
- ✅ Protocol integration
  - Command types defined
  - Command handlers implemented (streaming protocol)
  - Response types with typed payloads
- ✅ Build pipeline
  - Agda → MAlonzo → Haskell → binary
  - Automated FFI name mismatch detection
- ✅ Protocol JSON parser (Phase 2B streaming protocol)
  - ✅ parseDBC command parser
  - ✅ setProperties command parser
  - ✅ startStream / endStream command parsers
  - ✅ DataFrame parser (timestamp, CAN ID, 8-byte payload)
- ✅ End-to-end streaming tests (all 5 tests passing)

**Phase 1 Complete** - All Requirements Met:

✅ Protocol parser complete (all 4 commands)
✅ Python wrapper implemented (subprocess interface)
✅ All critical bugs fixed (shiftR, power10)
✅ End-to-end signal extraction working
✅ Build system production-ready

**Test Results**:
- Bit extraction: 0x01→1, 0x09→9, 0xAB→171, 0xFF→255 ✓
- Rational parsing: 0.25, 0.5, 1.5, 0.125 all work correctly ✓
- Signal scaling: 10000 × 0.25 = 2500.0 ✓

**Next Steps**: Begin Phase 2A (LTL Core + Real-World Support)
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

4. ✅ **Implement JSON protocol parser** (COMPLETED - Phase 2B):
   - **Migration**: Moved from YAML to JSON line protocol
   - **File**: `Protocol/Routing.agda` and `Protocol/JSON.agda`
   - **Implemented**:
     - JSON parsing with proper error handling
     - All streaming commands: parseDBC, setProperties, startStream, endStream
     - DataFrame parsing (timestamp, CAN ID, 8-byte payload)
   - **Result**: Remains `--safe --without-K` compliant

**Phase 2B Complete** - Streaming Protocol Operational:

✅ JSON streaming protocol fully implemented
✅ Python StreamingClient with DSL support
✅ All 5 integration tests passing
✅ Incremental LTL checking working
✅ Property violation detection operational

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
cat .session-state.md  # Comprehensive project state and recovery instructions

# Quick status check
git log --oneline -5  # Recent commits: shiftR fix, power10 fix, docs update

# Current Status: Phase 1 100% complete!
# Last Completed: Fixed power10 bug, all tests pass (commits 8fc48a3, 60a94a4, ca619bb)
# Ready for: Phase 2A - LTL Core + Real-World Support

# Verify everything works:
source venv/bin/activate
cd python && python3 -m pytest tests/ -v  # Should all pass

# Build system commands:
cabal run shake -- build         # Full build, 0.26s no-op, ~11s incremental
cabal run shake -- build-agda    # Agda only
cabal run shake -- clean         # Clean all artifacts

# Test streaming protocol:
cd python && python3 << 'EOF'
from aletheia import StreamingClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Example: Simple property check
dbc_json = dbc_to_json("../examples/example.dbc")
property = Signal("Speed").less_than(220).always()

with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    # ... stream frames ...
EOF
```

**IMPORTANT**: See `.session-state.md` for complete project state, decisions, and recovery instructions.
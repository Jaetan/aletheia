# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). The core logic is implemented in Agda with correctness proofs, compiled to Haskell, and exposed through a Python API.

**Current Phase**: 1 - Core Infrastructure (see DESIGN.md for roadmap)

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

**Remaining in Phase 1**:
- End-to-end testing through Python wrapper
- Integration testing with sample DBC files

### **Phase 2: LTL Foundation**
- LTL syntax and semantics
- Coinductive trace streams
- Basic model checker
- Temporal property verification

### **Phase 3: Temporal Bounds and Streaming**
- Bounded LTL checking
- Streaming verification
- Grammar formalization for parsers
- Parser soundness proofs

### **Phase 4: Robustness Improvements**
- Comprehensive logging
- Counterexample generation
- Error recovery and reporting
- Performance profiling

### **Phase 5: Optimization and Feature Extensions**

**Planned Enhancements**:
- Full rational number parsing with NonZero proofs
- Additional encoding/decoding tests and properties
- Enhanced DBC validation (signal overlap detection, range validation)
- Pretty-printer implementation for DBC
- Round-trip property proofs (parse ∘ print ≡ id)
- Advanced error reporting with precise locations
- Performance optimizations

When adding features, consider which phase they belong to and maintain consistency with the overall architecture.

## Current Session Progress

**Last Completed**: Protocol integration (commit 30efae6)

### Completed in This Session:
1. ✅ DBC parser with correctness properties (commits 61969d9, 00935c6)
   - Full YAML parser with primitives
   - Correctness properties: bounded values, determinism
   - Runtime semantic checks and test cases

2. ✅ Protocol integration (commit 30efae6)
   - Extended Command types: ParseDBC, ExtractSignal, InjectSignal
   - Rich Response types with typed payload data
   - Full command handlers in Main.agda
   - Type-safe integration of all Phase 1 components

### Known Issue - Type-Checking Timeout (DEEP ISSUE):
**Problem**: Parser normalization causes timeout even after modularization
- **Root Cause**: Fuel-based parser combinators force symbolic evaluation during type-checking
- **Impact**: Cannot compile Agda → Haskell (>2min timeout persists)
- **Not a correctness issue**: All code is type-safe and logically correct
- **Attempted fixes** (commit cde5921):
  - ✅ Split Main.agda into Handlers module
  - ✅ Added NOINLINE pragmas
  - ❌ Still times out on Handlers.agda

**Resolution Options**:

**Option A - Hybrid Approach (Recommended for Now)**:
1. Keep core logic in Agda for verification
2. Use postulates for handlers in Agda (to get types)
3. Implement actual handlers in Haskell shim
4. Benefit: Can compile and test, lose some verification

**Option B - Rewrite Parser Combinators**:
1. Replace fuel-based termination with sized types
2. More complex but should compile faster
3. Phase 4 task (optimization phase)

**Option C - Incremental Compilation** :
1. Cache type-checked modules
2. Only recompile changed parts
3. Requires build system improvements

### Files Modified (Uncommitted):
- None (all changes committed)

### Decision: Option B - Rewrite Parser Combinators (CHOSEN)

**Rationale**:
- Fuel-based approach caused compilation timeout - need to fix root cause
- Cannot keep codebase in non-compilable state long-term
- Risk of compounding issues as more code is added
- Better to fix thoroughly now than accumulate technical debt
- No time pressure - can take time to do it right

**Implementation Plan**:
1. ✅ Research sized types in Agda
2. 🚧 Design new combinator structure using sized types
3. ⏳ Rewrite Parser/Combinators.agda incrementally
4. ⏳ Update DBC/Parser.agda to use new combinators
5. ⏳ Test compilation performance
6. ⏳ Verify all existing tests still pass

**Expected Benefits**:
- Faster type-checking (no fuel-based symbolic evaluation)
- Same correctness guarantees (sized types are well-founded)
- Cleaner termination proofs
- Better foundation for future parsers

### Session Recovery Notes:
If session terminates, resume with:
```bash
cd /home/nicolas/dev/agda/aletheia
git log --oneline -7  # Check latest commits

# Current Status: Rewriting parser combinators with sized types (Option B chosen)
# Working on: src/Aletheia/Parser/Combinators.agda

# Next actions:
# 1. Read current Parser/Combinators.agda to understand structure
# 2. Research Agda sized types (Size, ↑, ∞)
# 3. Create new parser type using sized types instead of fuel
# 4. Rewrite core combinators: pure, _<$>_, _<*>_, _>>=_
# 5. Test with simple parsers first
# 6. Gradually migrate DBC parser to new combinators
```
- You can use the ghc options to the agda compiler to use up to 32 cpus.
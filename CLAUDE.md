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

**Last Completed**: Protocol YAML parser (commit 8a853e1)

### Completed in This Session:
1. ✅ Parser combinators rewrite with structural recursion
   - Replaced fuel-based termination with input-length-based approach
   - Progress checking prevents infinite loops (sameLengthᵇ)
   - Type-checks in ~10s (previously >120s timeout)
   - Maintains all correctness guarantees

2. ✅ Build pipeline verification
   - Agda → MAlonzo compilation working (~43s)
   - Haskell shim integration successful
   - Binary executable created and tested
   - Automated FFI name mismatch detection implemented

3. ✅ Protocol YAML parser implementation (commit 8a853e1)
   - Implemented parseCommand in Protocol/Parser.agda
   - Echo and ParseDBC command parsers functional
   - Updated Main.agda to use protocol parser
   - Changed Haskell shim to read multi-line input (getContents)
   - End-to-end testing successful:
     * Echo command: ✅ Parses and echoes messages
     * ParseDBC command: ✅ Successfully parses sample.dbc.yaml

### Phase 1 Status: ~85% Complete

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
  - **Limitation**: Rational parser ignores fractional parts (Phase 5 enhancement)
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

**Remaining for Phase 1 Completion**:
1. **Protocol parser completion**:
   - Implement ExtractSignal command parser
   - Implement InjectSignal command parser
   - Requires: byte array parser (Vec Byte 8 from hex strings)
   - Requires: rational number parser (reuse from DBC or improve)

2. **Python wrapper implementation**:
   - Create python/aletheia/client.py with subprocess interface
   - Implement CANDecoder class wrapping binary
   - YAML serialization/deserialization
   - Error handling and validation

3. **Integration testing**:
   - End-to-end tests: Python → binary → Python
   - Test all 4 command types
   - Error case testing
   - Sample DBC file testing

**Parser Correctness Strategy** (as planned):
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

### Resolved Issue - Type-Checking Timeout:
**Previous Problem**: Parser normalization caused >120s timeouts
**Root Cause**: Fuel-based parser combinators forced symbolic evaluation
**Solution Implemented**: Rewrote parser combinators with structural recursion
**Result**: Type-checks in ~10s, all functionality preserved

### Session Recovery Notes:
If session terminates, resume with:
```bash
cd /home/nicolas/dev/agda/aletheia
git log --oneline -5  # Check latest commits

# Current Status: Phase 1 ~85% complete
# Last Completed: Protocol YAML parser (partial - Echo/ParseDBC only)
# Commits: 8a853e1 (protocol parser), 3aca901 (CLAUDE.md update)

# Next Steps for Phase 1 completion:
# 1. Complete protocol parser (ExtractSignal/InjectSignal commands)
#    - Need byte array parser for Vec Byte 8
#    - Need rational parser (can reuse from DBC)
# 2. Implement Python wrapper (python/aletheia/client.py)
# 3. Integration tests (Python ↔ binary)

# Current working tests:
printf 'command: "Echo"\nmessage: "test"' | ./build/aletheia
cat examples/sample.dbc.yaml | sed '1s/^/command: "ParseDBC"\nyaml: /' | ./build/aletheia

# To rebuild if needed:
cabal run shake -- build  # Full build (Agda + Haskell)
cabal run shake -- build-haskell  # Haskell only (if Agda unchanged)
```
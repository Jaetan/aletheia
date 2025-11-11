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
agda Aletheia/Main.agda

# Check with verbose output
agda -v 10 Aletheia/Main.agda

# Use GHC RTS options for faster compilation (parallel GC, more threads)
agda +RTS -N8 -RTS Aletheia/YourModule.agda
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
- **Performance**: Use GHC RTS options for faster compilation: `agda +RTS -N8 -RTS`
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

The parser library (`Aletheia.Parser.Combinators`) uses fuel-based termination (`defaultFuel = 1000`). To avoid expensive symbolic evaluation during type-checking:

- Helper functions like `runParser` avoid `with` patterns, using simple pattern matching instead
- String conversion happens at boundaries only (use `List Char` internally)
- Pre-computed character codes (`code-0 = 48`, etc.) instead of runtime computation

### Type-Checking Tips

- First build compiles stdlib (~20s), subsequent builds are much faster
- Use `PrecompileStdlib.agda` to cache common imports
- Avoid `with` patterns on complex parser compositions in type signatures
- Use `+RTS -N8 -RTS` to parallelize GHC's runtime during type-checking

## Implementation Phases

Aletheia follows a phased implementation plan:

### **Phase 1: Core Infrastructure** (In Progress)

**Completed**:
- ✅ Parser combinators with fuel-based termination (commit 077b39d)
  - Full functor/applicative/monad interfaces
  - Basic correctness properties
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

**Currently Working On**:
- 🚧 Protocol integration and Main.agda implementation
  - Extend Command types beyond Echo
  - Add ParseDBC, ExtractSignal, InjectSignal commands
  - Implement command handlers in Main.agda
  - Create proper Response types
  - Build and test end-to-end pipeline

**Remaining in Phase 1**:
- Build pipeline verification (Agda → Haskell → binary)
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

**Last Completed**: DBC parser with correctness properties (commits 61969d9, 00935c6)

**Next Steps**: Protocol integration for Phase 1 completion
1. Update Protocol/Command.agda with DBC-related commands
2. Implement command handlers in Main.agda
3. Create Response types for command results
4. Build and test the complete pipeline

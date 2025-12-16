# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). The core logic is implemented in Agda with correctness proofs, compiled to Haskell, and exposed through a Python API.

**Current Phase**: See [PROJECT_STATUS.md](PROJECT_STATUS.md) for detailed phase status

## Table of Contents

- [Global Project Rules](#global-project-rules)
- [Common Commands](#common-commands)
- [Architecture](#architecture-three-layer-design)
- [Module Structure](#module-structure)
- [Development Workflow](#development-workflow)
- [Key Files](#key-files)
- [Requirements](#requirements)
- [Important Notes](#important-notes)
- [Troubleshooting](#troubleshooting)
- [Performance Considerations](#performance-considerations)
- [Implementation Phases](#implementation-phases)
- [Current Session Progress](#current-session-progress)

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

**Current Status**: ✅ All Aletheia modules use `--safe --without-K` or documented exceptions†

† **31 total modules**: 27 use `--safe`, 4 coinductive without `--safe`

### Module Safety Flag Breakdown

**By flag combination**:
- **21 modules**: `--safe --without-K` (pure safe, no coinduction)
- **1 module**: `--safe --without-K --no-main` (Parser/Combinators)
- **5 modules**: `--safe --without-K --guardedness` (Trace/Stream, Trace/Context, LTL/Incremental, LTL/JSON, LTL/SignalPredicate)
- **4 modules**: `--without-K --guardedness --sized-types` (no `--safe` - coinductive)

**Modules not using `--safe` flag (4 of 31)**:

Four modules require extensions incompatible with `--safe` for coinductive stream processing:

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

See [Building Aletheia](docs/development/BUILDING.md) for comprehensive build instructions, including:
- Build system commands (Shake via Cabal)
- Python virtual environment setup
- Common development workflows
- Troubleshooting build issues

Quick reference (see [BUILDING.md](docs/development/BUILDING.md) for detailed instructions):
```bash
cabal run shake -- build              # Build everything
python3 -m venv venv && source venv/bin/activate  # Set up Python environment
python3 -m pytest tests/ -v           # Run tests
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

Agda modules are organized by package:
- **Parser/**: Parser combinators and string utilities
- **CAN/**: CAN frame encoding/decoding (Endianness, Encoding)
- **DBC/**: DBC file parser
- **LTL/**: Linear Temporal Logic (Syntax, Semantics, Coinductive, Incremental, SignalPredicate)
- **Trace/**: Trace types (Stream, Context)
- **Protocol/**: JSON protocol and streaming state machine
- **Data/**: Utility types (DelayedColist)

See [Architecture Overview](docs/architecture/DESIGN.md) for the three-layer architecture diagram.

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

See [BUILDING.md](docs/development/BUILDING.md#prerequisites) for detailed requirements and installation instructions.

Quick reference: Agda 2.8.0, GHC 9.4.x/9.6.x, Cabal 3.12+, Python 3.12+ (uses `typing.override`)

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

MAlonzo mangles function names (e.g., `processCommand` → `d_processCommand_28`). The build system auto-detects mismatches and provides exact fix commands:

```bash
cabal run shake -- build
# If mismatch: ERROR with sed command to fix it
```

**When it triggers**: Rarely - only when adding/removing Agda definitions before `processCommand` in Main.agda.

**Best Practice**: Keep Haskell shim minimal (currently 74 lines), update mangled names when needed. Alternative solutions (COMPILE pragmas, FFI modules) would compromise `--safe` guarantees.

### Virtual Environment

See [BUILDING.md](docs/development/BUILDING.md#2-set-up-python-virtual-environment) for Python virtual environment setup.

Quick reference: Create with `python3 -m venv venv`, activate with `source venv/bin/activate`

### Haskell Shim Philosophy

The Haskell shim (haskell-shim/src/Main.hs) should remain minimal:
- Current: 74 lines
- Target: <100 lines
- Purpose: I/O only (stdin/stdout, buffering)
- Never add business logic here

### Module Organization

When adding new Agda modules:
- Follow existing package structure (Parser, CAN, DBC, LTL, etc.)
- Include correctness properties alongside implementations
- Use descriptive module names (e.g., `Properties.agda` for proofs)
- Update Main.agda if new functionality needs exposure

### Import Naming Conventions

When importing stdlib modules with conflicting names, use **subscript suffix** pattern for consistency:

**Standard naming:**
- String operators: `_++ₛ_`, `_≟ₛ_`
- List operators: `_++ₗ_`
- Rational operators: `_+ᵣ_`, `_*ᵣ_`, `_-ᵣ_`, `_≤ᵣ_`

**Example:**
```agda
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)

-- Usage (underscores invisible at call sites)
result = "hello" ++ₛ "world"   -- NOT _++ₛ_
combined = list1 ++ₗ list2
```

**Important**: Underscores are invisible in infix usage, but remain when passing operators as parameters (e.g., `foldr _++ₛ_ ""`).

## Troubleshooting

**Build failures**: `cabal run shake -- clean && cabal run shake -- build`

**Python issues**: Verify venv active (`which python3` → should show `.../venv/bin/python3`)

**Agda module not found**: Check `~/.agda/libraries` lists standard-library path and `~/.agda/defaults` contains "standard-library"

**MAlonzo name mismatch**: Build provides exact sed command - just run it

**Type-checking timeout**: Always use `agda +RTS -N32 -RTS` for parallel GHC

## Performance Considerations

**Parser Combinators**: Use structural recursion on input length (not fuel-based) to avoid type-checking timeouts. Helper functions avoid `with` patterns in type signatures.

**Type-Checking**: **Always use `agda +RTS -N32 -RTS`** for parallel GHC (17s vs >120s timeout for StreamState/Main). First build caches stdlib (~20s).

## Implementation Phases

For detailed phase completion status, deliverables, and roadmap, see [PROJECT_STATUS.md](PROJECT_STATUS.md).

**Quick Summary**:
- ✅ Phase 1: Core Infrastructure (complete)
- ✅ Phase 2A: LTL Core + Real-World Support (complete)
- ✅ Phase 2B: Streaming + Counterexamples (complete)
- ✅ Phase 2B.1: Batch Signal Operations (complete)
- 🔜 Phase 3: Verification + Performance (next)

---

## For Human Developers

This section provides guidance for developers new to Agda or the Aletheia codebase.

### For Agda Newcomers

If you're new to Agda but familiar with Python/typed languages:

**Basic Syntax:**
- `→` means function arrow (like `->` in types)
- `∀` means "for all" (universal quantification)
- `ℕ` is natural numbers (type Nat with `\bN`)
- `ℚ` is rationals (type with `\bQ`)
- `≡` is propositional equality (type with `\==`)

**Safety Flags:**
- `--safe` ensures no undefined behavior (like Rust's borrow checker)
  - No postulates, no unsafe primitives, all functions terminate
  - Used in 27 of 31 Aletheia modules
- `--without-K` ensures proofs are constructive (no axiom of choice)
  - Makes code compatible with Homotopy Type Theory
  - Required for formal verification

**Dependent Types:**
Types can depend on values:
- `Vec Byte 8` - vector of exactly 8 bytes (length in type!)
- `Fin n` - numbers 0 to n-1 (bounds checking at compile time)
- `CANFrame` uses `Fin 2048` for standard IDs (impossible to exceed range)

**Common Patterns:**
- **Pattern matching with `with`**: Extract intermediate values
- **Structural recursion**: Functions recurse on structurally smaller inputs
  - Parser combinators recurse on `length input` (always decreasing)
  - No fuel needed - termination guaranteed!
- **Module imports with renaming**: Avoid name clashes (see Import Naming Conventions above)

**Reading Error Messages:**
- **Yellow highlighting**: Type mismatch - check expected vs actual types
- **"Not in scope"**: Import missing or wrong module name
- **"Termination checking failed"**: Function might not terminate
  - Use structural recursion on input length or add fuel parameter
  - See Parser/Combinators.agda for examples
- **"_X_42 is not defined"**: Agda generates metavariables - fill the hole!

**Why formal methods for automotive?**
- Guarantees correctness (not just testing)
- Signal extraction bugs can cause safety issues
- LTL properties prove temporal safety constraints

**Resources:**
- [Agda Documentation](https://agda.readthedocs.io/)
- [Standard Library](https://agda.github.io/agda-stdlib/)
- [Agda Tutorial](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html)

### Code Style

**Agda:**
- Naming: Follow stdlib conventions
- Indentation: 2 spaces
- Line length: Aim for 80 characters, max 100

**Haskell:**
- Style: Follow standard Haskell style
- Keep it minimal: Haskell shim should stay <100 lines

**Python:**
- Style: PEP 8
- Type hints: Use throughout
- Docstrings: Google style

### Contributing

**Commit Messages:**
Follow conventional commits:
```
feat(CAN): Add multiplexed signal support
fix(Parser): Handle trailing whitespace in DBC
docs(BUILDING): Add macOS-specific notes
```

**Before Committing:**
1. Ensure code type-checks: `agda src/Aletheia/Main.agda`
2. Build succeeds: `cabal run shake -- build`
3. Tests pass: `cd python && pytest`

---

## Current Session Progress

See [PROJECT_STATUS.md](PROJECT_STATUS.md) for phase status and deliverables.

See [.session-state.md](.session-state.md) for session recovery, next steps, and current work context.
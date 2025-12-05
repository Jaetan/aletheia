# Development Guide

---
**Version**: 1.0.0
**Last Updated**: 2025-12-05
**Phase**: 2B.1 Complete
---

This document describes the architecture, module structure, and development workflows for Aletheia.

## For Agda Newcomers

If you're new to Agda but familiar with Python/typed languages:

### Basic Syntax
- **`→`** means function arrow (like `->` in types)
- **`∀`** means "for all" (universal quantification)
- **`ℕ`** is natural numbers (type Nat with `\bN`)
- **`ℚ`** is rationals (type with `\bQ`)
- **`≡`** is propositional equality (type with `\==`)

### Safety Flags
- **`--safe`** ensures no undefined behavior (like Rust's borrow checker)
  - No postulates, no unsafe primitives, all functions terminate
  - Used in 23 of 27 Aletheia modules
- **`--without-K`** ensures proofs are constructive (no axiom of choice)
  - Makes code compatible with Homotopy Type Theory
  - Required for formal verification

### Dependent Types
Types can depend on values:
- `Vec Byte 8` - vector of exactly 8 bytes (length in type!)
- `Fin n` - numbers 0 to n-1 (bounds checking at compile time)
- `CANFrame` uses `Fin 2048` for standard IDs (impossible to exceed range)

### Common Patterns
- **Pattern matching with `with`**: Extract intermediate values
  ```agda
  -- Extract Maybe value for dependent matching
  foo x with someComputation x
  ... | just y = useY y
  ... | nothing = default
  ```
- **Structural recursion**: Functions recurse on structurally smaller inputs
  - Parser combinators recurse on `length input` (always decreasing)
  - No fuel needed - termination guaranteed!
- **Module imports with renaming**: Avoid name clashes
  ```agda
  open import Data.String using (String) renaming (_++_ to _++ₛ_)
  open import Data.List using (List) renaming (_++_ to _++ₗ_)
  ```

### Reading Error Messages
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

## Architecture Overview

For the full architecture diagram, see [DESIGN.md](../architecture/DESIGN.md#architecture).

### Design Principles

1. **Proven Correctness**: All critical logic lives in Agda with `--safe` flag
2. **Minimal Trust Base**: Haskell shim is <100 lines, only does I/O
3. **Transparency**: Comprehensive logging at all levels
4. **Composability**: Modular design with clear interfaces

## Module Structure

### Agda Modules (`src/Aletheia/`)

See source files for detailed structure of each package:
- Parser (combinators and properties)
- CAN (frames, signals, encoding)
- DBC (types, parser, semantics)
- LTL (syntax, semantics, checker, DSL)
- Trace (streams, CAN traces, parser)
- Protocol (commands, parser, response)

## Development Workflow

### Adding a New Feature

1. **Design in Agda**: Define types and properties
2. **Implement with proofs**: Write code and prove correctness
3. **Update Haskell shim** (if needed): Usually no changes required
4. **Expose in Python**: Add convenience functions
5. **Test**: Add examples and tests

### Typical Development Cycle

```bash
# 1. Edit Agda source
vim src/Aletheia/CAN/Frame.agda

# 2. Type-check (fast feedback)
cd src
agda Aletheia/CAN/Frame.agda

# 3. Build and test
cd ..
cabal run shake -- build
python3 examples/test_feature.py

# 4. Commit
git add src/Aletheia/CAN/Frame.agda
git commit -m "CAN.Frame: Add multiplexed signal support"
```

## Code Style

### Agda

- **Naming**: Follow stdlib conventions
- **Indentation**: 2 spaces
- **Line length**: Aim for 80 characters, max 100

### Haskell

- **Style**: Follow standard Haskell style
- **Keep it minimal**: Haskell shim should stay <100 lines

### Python

- **Style**: PEP 8
- **Type hints**: Use throughout
- **Docstrings**: Google style

## Testing

### Agda Proofs

Proofs are tests! If an Agda module type-checks with `--safe`, the proofs are valid.

### Python Tests

```bash
cd python
python3 -m pytest tests/ -v
```

## Contributing

### Commit Messages

Follow conventional commits:
```
feat(CAN): Add multiplexed signal support
fix(Parser): Handle trailing whitespace in DBC
docs(BUILDING): Add macOS-specific notes
```

### Before Committing

1. Ensure code type-checks: `agda src/Aletheia/Main.agda`
2. Build succeeds: `shake build`
3. Tests pass: `cd python && pytest`

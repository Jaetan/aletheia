# Development Guide

---
**Version**: 1.0.0
**Last Updated**: 2025-12-05
**Phase**: 2B.1 Complete
---

This document describes the architecture, module structure, and development workflows for Aletheia.

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

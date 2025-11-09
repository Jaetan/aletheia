# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic
**Version**: 0.1.0
**Date**: 2025-11-08

## Project Overview

Aletheia provides mathematically proven tools to verify automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

## Core Requirements

- **Agda 2.8.0** with stdlib 2.3 (`--safe` enabled) for all logic
- **Haskell** for minimal I/O shim
- **Python** for user-facing API
- **Shake** for build system

## Architecture

See DEVELOPMENT.md for full architecture details.

## Implementation Phases

### Phase 1: Core Infrastructure (2-3 weeks)
- Project setup
- Parser combinators library
- CAN frame types and basic encoding/decoding
- Simple DBC parser
- Haskell shim
- Python wrapper

### Phase 2: LTL Foundation (2-3 weeks)
- LTL syntax and semantics
- Coinductive traces
- Basic model checker
- Python DSL

### Phase 3: Temporal Bounds & Streaming (2 weeks)
- Bounded temporal operators
- Online checker with buffering
- Timestamp handling

### Phase 4: Robustness & UX (2 weeks)
- DBC parser robustness
- Comprehensive logging
- Counterexample generation
- Documentation

### Phase 5: Optimization & Extension (ongoing)
- Counterexample minimization
- Performance tuning
- Extended features

## Success Criteria

- All core logic proven correct in Agda
- Python users can verify without knowing formal methods
- Transparent logging builds trust
- Robust DBC parsing
- Clear error messages

---

**Document Status**: Living document
**Last Updated**: 2025-11-08

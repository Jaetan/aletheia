# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic
**Version**: 0.3.2
**Status**: Phase 3 - Verification + Performance (see [PROJECT_STATUS.md](../../PROJECT_STATUS.md))
**Last Updated**: 2026-02-03

## Project Overview

Aletheia provides mathematically proven tools to verify automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

**Core Value Proposition**: Write temporal properties in Python, verify them against CAN traces, with mathematical guarantees of correctness.

## Architectural Constraints

CAN protocol decisions (extended IDs, multiplexing) were researched during Phase 1→2 transition and are now implemented in Phase 2A/2B.

**Key Decisions**:

| Constraint | Decision | Phase |
|------------|----------|-------|
| **8-byte CAN frames** | ✅ Keep fixed | Phase 5 (if requested) |
| **Extended 29-bit CAN IDs** | ✅ Implemented | Phase 1 |
| **Signal multiplexing** | ✅ Implemented | Phase 2A |
| **CAN-FD support** | ❌ Deferred | Phase 5 (if requested) |

## Architecture

Aletheia follows a three-layer architecture that maximizes formal verification while providing a practical interface:

```
┌─────────────────────────────────────────┐
│ Python Layer (python/)                  │
│ - User-facing API (AletheiaClient, DSL)│
│ - Loads shared library via ctypes       │
│ - JSON protocol over FFI calls          │
└──────────────┬──────────────────────────┘
               │ ctypes FFI (JSON strings)
┌──────────────▼──────────────────────────┐
│ Haskell FFI (haskell-shim/)             │
│ - AletheiaFFI.hs: foreign export ccall  │
│ - Compiled to libaletheia-ffi.so        │
│ - State via StablePtr (IORef)           │
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

## Streaming Protocol

**Phase 2B** implements a JSON-based streaming protocol for processing large CAN traces with O(1) memory.

**Key Design**:
- JSON protocol over direct FFI calls (ctypes → shared library)
- No subprocess or IPC overhead — function calls within the same process
- Sequential message processing (no threading)
- Incremental LTL checking with immediate violation reporting

See [PROTOCOL.md](PROTOCOL.md) for complete protocol specification, message types, and state machine details.

---

## Documentation

- **[PROTOCOL.md](PROTOCOL.md)** - Complete JSON protocol specification
- **[PROJECT_STATUS.md](../../PROJECT_STATUS.md)** - Project status and roadmap
- **[CLAUDE.md](../../CLAUDE.md)** - Development guidelines
- **[BUILDING.md](../development/BUILDING.md)** - Build instructions

---

**End of Design Document**

# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic
**Version**: 1.1.1
**Status**: Phase 5.1 complete (see [PROJECT_STATUS.md](../../PROJECT_STATUS.md) for the authoritative status)
**Last Updated**: 2026-04-15

## Project Overview

Aletheia provides mathematically proven tools to verify automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

**Core Value Proposition**: Write temporal properties in Python, C++, or Go, verify them against CAN traces, with mathematical guarantees of correctness.

## Architectural Constraints

CAN protocol decisions (extended IDs, multiplexing) were researched during Phase 1→2 transition and are now implemented in Phase 2A/2B.

**Key Decisions**:

| Constraint | Decision | Phase |
|------------|----------|-------|
| **CAN-FD support** | ✅ Implemented | Phase 5 |
| **Extended 29-bit CAN IDs** | ✅ Implemented | Phase 2A |
| **Signal multiplexing** | ✅ Implemented | Phase 2A |

## Architecture

Aletheia follows a three-layer architecture that maximizes formal verification while providing a practical interface:

```
┌─────────────────────────────────────────┐
│ Language Bindings                       │
│ - Python (python/): ctypes, JSON + binary│
│ - C++ (cpp/): dlopen, JSON + binary     │
│ - Go (go/): cgo + dlopen, JSON + binary │
│ - Four interface tiers per binding:     │
│   Check API / YAML / Excel / DSL        │
└──────────────┬──────────────────────────┘
               │ FFI (JSON commands + binary frames)
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
│ - All 120 modules use --safe --without-K│
└─────────────────────────────────────────┘
```

**Why Haskell as the middle layer?** MAlonzo (Agda's compiler backend) generates Haskell. GHC provides mature shared library output (`foreign-library`), and its FFI supports all major languages via `foreign export ccall`.

**Critical Design Principle**: ALL critical logic must be implemented in Agda with proofs. The Haskell shim only performs I/O. Never add logic to the Haskell, Python, C++, or Go layers. Client-side enrichment (formula descriptions, violation formatting) is convenience logic in the binding layers.

## Streaming Protocol

The JSON-based streaming protocol (completed in Phase 2B) processes large CAN traces with O(1) memory.

**Key Design**:
- JSON protocol over direct FFI calls (ctypes/dlopen → shared library)
- No subprocess or IPC overhead — function calls within the same process
- Sequential processing per session (multiple independent sessions supported)
- Incremental LTL checking with immediate violation reporting

See [PROTOCOL.md](PROTOCOL.md) for complete protocol specification, message types, and state machine details.

---

## Documentation

- **[PROTOCOL.md](PROTOCOL.md)** - Complete JSON protocol specification
- **[INTERFACES.md](../reference/INTERFACES.md)** - Check API, YAML, Excel interface guide
- **[PYTHON_API.md](../reference/PYTHON_API.md)** - Python DSL and client reference
- **[PROJECT_STATUS.md](../../PROJECT_STATUS.md)** - Project status and roadmap
- **[BUILDING.md](../development/BUILDING.md)** - Build instructions

---

**End of Design Document**

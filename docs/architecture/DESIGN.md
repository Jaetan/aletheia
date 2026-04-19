# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md); status in [PROJECT_STATUS.md](../../PROJECT_STATUS.md).

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
│ - All 119 modules use --safe --without-K│
└─────────────────────────────────────────┘
```

**Why Haskell as the middle layer?** MAlonzo (Agda's compiler backend) generates Haskell. GHC provides mature shared library output (`foreign-library`), and its FFI supports all major languages via `foreign export ccall`.

**Critical Design Principle**: ALL critical logic must be implemented in Agda with proofs. The Haskell shim only performs I/O. Never add logic to the Haskell, Python, C++, or Go layers. Client-side enrichment (formula descriptions, violation formatting) is convenience logic in the binding layers.

## Why Agda / Haskell / JSON

**Why Agda for the core?** Signal-extraction and LTL bugs in an automotive stack can mask real safety issues or raise false ones; both are expensive. Testing narrows the failure space, but only proof rules it out. Agda's dependent types let us state correctness — "signal extraction inverts frame building on well-formed DBCs", "LTLf simplification preserves the Kleene verdict", "parsing round-trips formatting" — as types, and then the typechecker is the verifier. The `--safe` flag forbids postulates, partial functions, and unsafe primitives, so the 119 modules that make up the core cannot hide an unproven step. Proof-of-fit: every DBC-side guarantee currently enforced by runtime checks in peer tooling is instead discharged once at type-check time here.

**Why Haskell as the compilation target?** Agda has three production backends (MAlonzo→Haskell, JavaScript, Erasure→Haskell). MAlonzo is the only one that yields a shared library consumable from Python, C++, and Go without a language-specific runtime on the consumer side — GHC's `foreign-library` emits a standard `.so` that `ctypes`, `dlopen`, and `cgo` all load uniformly. GHC also gives us a mature concurrent runtime for the streaming path and a stable C ABI for the FFI boundary. The Haskell shim stays thin (~470 lines across 3 files): it marshals C values into Agda's data constructors and forwards — no business logic lives in Haskell.

**Why JSON on the wire (and binary on the hot path)?** JSON is the greatest-common-denominator format across Python, C++, and Go: every binding has a mature parser, every protocol inspector can read it, and the wire format is debuggable without tooling. Protocol Buffers and MessagePack would save bytes but force schema-compiler infrastructure into every consumer and lose the "paste the response into a bug report" property. For the streaming hot path — where JSON parsing dominated the per-frame cost — we keep JSON for commands but use a binary `aletheia_send_frame()` entry point for data frames (4.3× CAN 2.0B, 9.1× CAN-FD throughput vs JSON). That split lets control-plane messages stay human-readable while the data plane runs at near-native speed.

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

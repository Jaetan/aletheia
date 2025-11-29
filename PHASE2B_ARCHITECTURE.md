# Phase 2B.1 Architecture - JSON Streaming Protocol

**Status**: ✅ Complete
**Date**: 2025-11-29
**Session**: JSON Protocol Migration

## Overview

Phase 2B.1 implements a pure JSON streaming protocol for real-time CAN frame analysis with LTL property checking. The architecture eliminates YAML entirely, using JSON throughout for clean, streaming-friendly communication.

## Architecture Decisions

### 1. Pure JSON Streaming (No YAML Embedding)

**Previous (Phase 1)**: `.dbc` text → YAML → Agda
**Current (Phase 2B.1)**: `.dbc` text → **JSON (Python)** → Agda

**Decision**: Remove YAML from the streaming protocol entirely.

**Rationale**:
- JSON is streaming-friendly (line-delimited)
- No format juggling (one format throughout)
- Cleaner separation: Python handles file formats, Agda handles logic
- Standard library support (cantools for .dbc parsing)

### 2. DBC Parsing Strategy

**Implementation**:
- Python layer: `aletheia.dbc_converter` uses `cantools` to parse `.dbc` → JSON
- Agda layer: `Aletheia.DBC.JSONParser` parses JSON → `DBC` record type

**Key Files**:
- `python/aletheia/dbc_converter.py` - DBC → JSON converter
- `src/Aletheia/DBC/JSONParser.agda` - JSON → DBC parser
- `src/Aletheia/DBC/Types.agda` - DBC data types (unchanged)

**JSON Structure**:
```json
{
  "version": "1.0",
  "messages": [{
    "id": 256,
    "name": "SpeedMessage",
    "dlc": 8,
    "extended": false,
    "sender": "ECU",
    "signals": [{
      "name": "Speed",
      "startBit": 0,
      "length": 16,
      "byteOrder": "little_endian",
      "signed": false,
      "factor": 0.1,
      "offset": 0.0,
      "minimum": 0.0,
      "maximum": 300.0,
      "unit": "km/h",
      "presence": "always"
    }]
  }]
}
```

### 3. Streaming Protocol Flow

**State Machine**:
1. `WaitingForDBC`: Initial state
2. `ReadyToStream`: After `parseDBC` command
3. `Streaming`: After `startStream` command

**Commands**:
- `parseDBC`: Load DBC structure (JSON object, not YAML string)
- `setProperties`: Set LTL properties to check
- `startStream`: Begin streaming mode
- `data`: Process incoming CAN frame
- `endStream`: End streaming and emit final results

**Response Types**:
- `Success` / `Error`: Command acknowledgments
- `PropertyResponse`: Violation/Satisfaction/Pending results
- `Ack`: Frame processed, no property triggered
- `Complete`: Stream ended

### 4. Module Organization

**Phase 2B Active Modules**:
```
Aletheia/
├── Main.agda                      # Entry point (processJSONLine only)
├── Data/
│   ├── Message.agda               # StreamCommand, Request, Response
│   └── DelayedColist.agda         # Streaming primitives
├── DBC/
│   ├── Types.agda                 # DBC data structures
│   └── JSONParser.agda            # JSON → DBC parser (NEW)
├── Protocol/
│   ├── JSON.agda                  # JSON parser/formatter
│   ├── Routing.agda               # Request routing, response formatting
│   ├── StreamState.agda           # State machine, command handlers
│   └── Response.agda              # Response types, counterexample data
├── LTL/
│   ├── Syntax.agda                # LTL AST
│   ├── JSON.agda                  # JSON → LTL parser
│   ├── SignalPredicate.agda       # Signal evaluation
│   ├── Incremental.agda           # Incremental LTL checker
│   └── Coinductive.agda           # Coinductive LTL semantics
└── CAN/
    ├── Frame.agda                 # CAN frame types
    ├── Signal.agda                # Signal definition
    ├── Encoding.agda              # Signal encoding/decoding
    └── Endianness.agda            # Byte order handling
```

**Phase 1 Deprecated Modules** (unused in Phase 2B):
```
Aletheia/
├── Protocol/
│   ├── Command.agda               # Phase 1 command types
│   ├── Handlers.agda              # Phase 1 command handlers
│   └── Parser.agda                # Phase 1 YAML protocol parser
├── DBC/
│   ├── Parser.agda                # YAML DBC parser
│   └── ParserTraced.agda          # Traced YAML parser
└── DebugDBC.agda                  # Debug utilities
```

### 5. Type Safety Guarantees

**Agda Flags**: All modules use `{-# OPTIONS --safe --without-K #-}`
- Exception: `Main.agda` uses `--sized-types` for coinductive types

**Safety Properties**:
- ✅ No postulates in streaming protocol
- ✅ Structurally terminating parsers
- ✅ Type-safe state transitions
- ✅ Bounded integer operations (Fin types)

### 6. Error Handling Strategy

**JSON Parsing**:
- Invalid JSON → `"TRACE_PARSE: Invalid JSON"`
- Missing fields → Specific error messages
- Type mismatches → `Nothing` propagation

**DBC Parsing**:
- Invalid structure → `"Failed to parse DBC JSON"`
- Missing required fields → Parser returns `Nothing`

**State Machine**:
- Invalid transitions → Descriptive error responses
- Example: `"Must call ParseDBC before StartStream"`

### 7. Debug Traces (To Be Cleaned)

**Current Trace Points**:
- `TRACE_PARSE`: JSON parsing failures
- `TRACE_DF0-DF5`: Data frame parsing stages
- `getIntDebug`: Integer extraction debugging

**Cleanup Plan** (next session):
- Remove trace functions after integration tests pass
- Keep only production error messages
- Document expected error scenarios

## Integration

### Python → Agda Interface

**Entry Point**: `processJSONLine : StreamState → String → StreamState × String`

**Usage**:
```python
from aletheia.dbc_converter import dbc_to_json
import json

# Convert .dbc to JSON
dbc_json = dbc_to_json("example.dbc")

# Send to Agda binary
state = initial_state
request = json.dumps({"type": "command", "command": "parseDBC", "dbc": dbc_json})
new_state, response = process_json_line(state, request)
```

### Haskell Shim

**File**: `haskell-shim/src/Main.hs`
**Function**: Calls `d_processJSONLine_NNN` from MAlonzo-generated code
**Role**: Pure I/O wrapper (stdin/stdout only)

## Design Constraints

### Fixed 8-Byte Frames

**Current**: `Vec Byte 8` hardcoded throughout
**Impact**: No CAN-FD support, no variable DLC
**Lift In**: Phase 5 (if needed)

### Standard CAN IDs Only (Updated)

**Current**: Both 11-bit and 29-bit CAN IDs supported
**Implementation**: `CANId` type with `Standard` and `Extended` constructors
**Coverage**: ~95%+ of automotive use cases

### Signal Multiplexing Support (Updated)

**Current**: Full multiplexing support implemented
**Implementation**: `SignalPresence` type with `Always` and `When` constructors
**Coverage**: Handles conditional signal presence based on multiplexor values

## Build System

**Command**: `cabal run shake -- build`
**Steps**:
1. Compile Agda → MAlonzo Haskell (`build/MAlonzo/`)
2. Create symlink (`haskell-shim/MAlonzo → ../build/MAlonzo`)
3. Build Haskell executable (`build/aletheia`)

**Dependency Tracking**: SHA256 hashes of Agda source files
**Incremental Builds**: ~11s for typical changes
**No-op Builds**: 0.26s

## Testing Strategy

**Unit Tests** (Agda):
- Parser properties (determinism)
- Bounded value checks
- Type-level guarantees

**Integration Tests** (Python):
- End-to-end JSON streaming
- DBC conversion
- Property checking

**Pending** (next session):
- Full integration test with converted .dbc
- Verify all commands work with JSON protocol

## Future Work

### Phase 2B.2 (Next):
- Clean up debug traces
- Complete integration testing
- Document streaming protocol spec

### Phase 3 (Verification):
- Replace bounded checks with proofs
- Parser soundness/completeness
- Round-trip properties
- NonZero proofs for rational division

### Phase 4 (Production):
- Error message polish
- User documentation
- Performance profiling
- Standard library of checks

## References

- **Previous Sessions**: See `.session-state.md`, `SESSION_SUMMARY.md`
- **Design Document**: `DESIGN.md`
- **Phase 1 Audit**: `PHASE1_AUDIT.md`

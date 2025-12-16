# Aletheia (Ἀλήθεια) Design Document

**Project**: Formally verified CAN frame analysis with Linear Temporal Logic
**Version**: 0.1.0
**Status**: Phase 2B Complete + Batch Operations Extension ✅ | JSON Streaming Protocol with LTL Checking (see [PROJECT_STATUS.md](../../PROJECT_STATUS.md))
**Last Updated**: 2025-12-02

## Project Overview

Aletheia provides mathematically proven tools to verify automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

**Core Value Proposition**: Write temporal properties in Python, verify them against CAN traces, with mathematical guarantees of correctness.

## Architectural Constraints

### Decisions Made (2025-11-13)

Based on analysis of **62 DBC files** covering **384 vehicles** from **50+ manufacturers** in the OpenDBC repository:

| Constraint | Decision | Rationale | Phase to Lift |
|------------|----------|-----------|---------------|
| **8-byte CAN frames** | ✅ **Keep fixed** | 100% of OpenDBC uses standard CAN, 0% CAN-FD | Phase 5 (if requested) |
| **Extended 29-bit CAN IDs** | ✅ **IMPLEMENTED** | Supported via CANId sum type (Standard \| Extended) | Phase 1 |
| **Signal multiplexing** | ✅ **Add in Phase 2A** | User requirement, critical for VIN/diagnostics | Phase 2A |
| **CAN-FD support** | ❌ **Defer to Phase 5** | 0% in OpenDBC, high refactoring cost | Phase 5 (if requested) |

**Impact**: These constraints define the scope of Phase 1-2. They balance real-world usability (support 100% of OpenDBC vehicles) with implementation pragmatism (defer costly features with zero current demand).

**Detailed analysis**: See [ARCHITECTURAL_ANALYSIS.md](ARCHITECTURAL_ANALYSIS.md)

## Core Requirements

See [BUILDING.md](../development/BUILDING.md#prerequisites) for detailed requirements.

Quick reference: Agda 2.8.0, GHC 9.6.x, Python 3.12+, Shake build system

## Architecture

Aletheia follows a three-layer architecture that maximizes formal verification while providing a practical interface:

```
┌─────────────────────────────────────────┐
│ Python Layer (python/)                  │
│ - User-facing API (StreamingClient, DSL)│
│ - Subprocess communication via JSON     │
│ - Simple wrapper around binary           │
└──────────────┬──────────────────────────┘
               │ JSON over stdin/stdout
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

## Streaming Protocol Architecture (Phase 2B)

**Added**: 2025-11-26 | **Status**: Implemented - JSON protocol with synchronous Python subprocess communication
**Updated**: 2025-11-26 | **Paradigm Shift**: Pivoted from YAML to JSON, introduced three-layer architecture

### Design Rationale

**Problem**: For large CAN traces (1GB+), neither Python nor the binary can materialize the full trace in memory.

**Constraints**:
1. Python reads frames from stream (file, network, real-time capture)
2. Python may need to modify frames mid-stream (Frame 153 debugging scenario)
3. Binary must process incrementally without buffering full trace
4. Multiple LTL properties must be checked in **single pass** (stream non-replayable)
5. Violations reported **immediately** (not waiting for end of stream)
6. Commands (encode/decode services) need immediate response, independent of data stream
7. Command priority: "Process all pending commands before next data frame"

**Solution**: Three-layer architecture with JSON protocol, synchronous Python subprocess, and sequential Haskell processing.

### Three-Layer Architecture (Option D: Truly Dumb Haskell)

**Design Decision**: After analyzing latency requirements and CAN bus characteristics, we chose the simplest possible architecture: sequential message processing with no threading or multiplexing complexity.

```
┌─────────────────────────────────────────────────────────────┐
│ Python Layer (subprocess, synchronous blocking I/O)         │
│ - subprocess.Popen() with stdin/stdout pipes                │
│ - Synchronous: send message → block → read response         │
│ - Tags all messages: {"type": "command"|"data", ...}        │
│ - Can modify frames mid-stream (Frame 153 scenario)         │
└──────────────────────────┬─────────────────────────────────┘
                           │
                  [Line-delimited JSON]
                  One message per line
                           │
                           ▼
         ┌─────────────────────────────────────────┐
         │ Single stdin pipe (FIFO, no queuing)    │
         └─────────────────┬───────────────────────┘
                           │
┌──────────────────────────▼────────────────────────────────────┐
│ Haskell Layer (~15 lines, truly dumb)                        │
│ - while(true): line = readLine(); result = agda(line); print  │
│ - Line buffering handled by hGetLine                          │
│ - No threading, no queues, no multiplexing                    │
│ - Just a thin wrapper around MAlonzo function call            │
└──────────────────┬────────────────────────────────────────────┘
                   │
          [String → Agda → String]
                   │
                   ▼
┌──────────────────────────────────────────────────────────────┐
│ Agda Layer (ALL logic lives here)                           │
│ - processJSONLine : String → String                          │
│ - Parses JSON, routes by type field                          │
│ - Command handlers: parseDBC, setProperties, encode, decode  │
│ - Data handler: Frame → LTL check → Violation or Ack         │
│ - State machine: DBC, properties, checker state              │
│ - Validates all state transitions                            │
│ - Returns response for EVERY message (sync or violation)     │
└──────────────────────────────────────────────────────────────┘
```

**Key Principles**:
1. **Agda has ALL logic** - validation, state, routing, LTL checking
2. **Haskell is truly dumb** - ~15 lines, just I/O loop
3. **Python controls flow** - subprocess management, stream modification, user interaction
4. **Sequential processing** - no queues, no threading, simplest possible
5. **Every message gets response** - commands return results, data frames return violations or acks

**Latency Analysis** (why Option D works):

| Scenario | Frame Rate | Per-Frame Time | Burst Size | Max Latency | Acceptable? |
|----------|------------|----------------|------------|-------------|-------------|
| Real-time CAN | 250 Hz | 4ms | N/A | < 1ms | ✅ Yes (serial bus) |
| Replay | 10K frames/sec | 100μs | 1000 frames | 100ms | ✅ Yes (at boundary) |

**Upgrade Path**: If latency becomes an issue in practice, we can upgrade to Option A (two file descriptors with threading) for guaranteed bounded latency. But start simple.

**Platform**: Linux x86_64/amd64 only, Ubuntu ≥22.04 or Debian unstable, GNU tools

### Protocol Format

**Line-Delimited JSON** (one JSON object per line):

**Input Messages** (Python → Haskell → Agda):

```json
{"type": "command", "command": "parseDBC", "dbc": {"version": "1.0", "messages": [{"name": "VehicleSpeed", ...}]}}
{"type": "command", "command": "setProperties", "properties": ["Signal('Speed').always.between(0, 200)", ...]}
{"type": "command", "command": "startStream"}
{"type": "data", "timestamp": 1000, "id": 256, "data": [18, 52, 86, 120, 154, 188, 222, 240]}
{"type": "data", "timestamp": 1001, "id": 256, "data": [19, 53, 87, 121, 155, 189, 223, 241]}
{"type": "command", "command": "encode", "message": "VehicleSpeed", "signal": "Speed", "value": 1000}
{"type": "data", "timestamp": 1002, "id": 256, "data": [20, 54, 88, 122, 156, 190, 224, 242]}
{"type": "command", "command": "endStream"}
```

**Output Messages** (Agda → Haskell → Python):

```json
{"type": "response", "command": "parseDBC", "status": "success"}
{"type": "response", "command": "setProperties", "status": "success"}
{"type": "response", "command": "startStream", "status": "success"}
{"type": "violation", "property": 0, "timestamp": 1050, "reason": "Speed = 250 violates always.between(0, 200)"}
{"type": "response", "command": "encode", "status": "success", "data": [232, 3, 0, 0, 0, 0, 0, 0]}
{"type": "satisfaction", "property": 1}
{"type": "response", "command": "endStream", "status": "success"}
{"type": "complete", "pending": [{"property": 2, "status": "pending"}]}
```

**Message Types**:

| Type | Direction | Purpose | Response |
|------|-----------|---------|----------|
| `command` | Python → Agda | Service requests (parseDBC, encode, decode) or control (startStream, endStream) | Immediate `response` |
| `data` | Python → Agda | CAN frame for LTL checking | Immediate response (violation, ack, or property result) |
| `response` | Agda → Python | Acknowledgment of command | Synchronous |
| `violation` | Agda → Python | LTL property violation detected | Immediate synchronous response to data frame |
| `satisfaction` | Agda → Python | LTL property satisfied | Immediate synchronous response to data frame |
| `complete` | Agda → Python | Stream ended, final pending results | Synchronous response to endStream command |

**JSON Schema** (validation in Phase 2B.1, proofs in Phase 3):
- Command schema: Required fields per command type
- Data schema: Required timestamp, id, data (8-element array)
- Response schema: Status + optional payload
- Report schema: Violation/satisfaction structure

### Property Lifecycle and Early Termination

**Property States**:
- **Active**: Currently being checked against incoming frames
- **Violated**: Decided false, reported immediately with counterexample
- **Satisfied**: Decided true, reported immediately
- **Pending**: Cannot decide without full trace, reported at EndStream

**Early Termination Semantics** (Finite Prefix of Infinite Traces):

| LTL Operator | Can Fail Early? | Can Succeed Early? | Semantics at EndStream |
|--------------|-----------------|--------------------|-----------------------|
| `Always(φ)` | ✅ Yes (first ¬φ) | ❌ No | Success if no violations seen |
| `Eventually(φ)` | ❌ No | ✅ Yes (first φ) | Failure if never satisfied |
| `Until(φ U ψ)` | ✅ Yes (φ fails) | ✅ Yes (ψ satisfied) | Failure if ψ never satisfied |
| `Never(φ)` | ✅ Yes (first φ) | ❌ No | Success if φ never seen |

**Property Removal**: Once a property is decided (violated or satisfied), it is removed from the active checking set. This:
- Improves performance (fewer properties to check per frame)
- Prevents redundant violation reports
- Allows Python to handle violations immediately

### Implementation Layers

#### Agda Layer (Core Logic)

**Output Stream Type**:
```agda
data PropertyResult : Set where
  Violation    : ℕ → Counterexample → PropertyResult
  Satisfaction : ℕ → PropertyResult
  Pending      : ℕ → Bool → PropertyResult
```

**Handler Signature**:
```agda
handleCheckStreamingLTL : DBC                         -- Parsed DBC structure
                        → List LTLFormula             -- LTL properties
                        → Colist Char ∞               -- Input stream (stdin)
                        → DelayedColist PropertyResult ∞  -- Output stream
```

**Incremental Multi-Property Checker**:
```agda
checkAllPropertiesIncremental : ∀ {i : Size}
                              → DBC
                              → List (ℕ × LTL SignalPredicate)
                              → DelayedColist TimedFrame i
                              → DelayedColist PropertyResult i
```

**Key Design Points**:
- Takes list of **indexed** properties (to identify them in results)
- Returns `DelayedColist PropertyResult` - a stream of results
- Internally partitions properties into decided vs. active on each frame
- Emits results immediately when properties settle
- At EndStream marker, emits pending results

#### Haskell Layer (I/O Orchestration)

**JSON Line Protocol**:
```haskell
-- JSON streaming mode (Phase 2B)
-- Reads JSON lines from stdin, processes them with Agda, writes JSON responses to stdout
jsonStreamLoop :: StreamState -> IO ()
jsonStreamLoop state = do
    eof <- isEOF
    when (not eof) $ do
        -- Read one JSON line
        line <- getLine

        -- Call Agda processJSONLine
        let result = processJSONLine state line

        -- Extract (newState, responseJSON) from result
        let (newState, responseJSON) = result

        -- Print response
        putStrLn responseJSON
        hFlush stdout  -- CRITICAL: Force output immediately

        -- Continue with new state
        jsonStreamLoop newState
```

**Key Mechanism**: Haskell's lazy evaluation ties the streams together:
1. Pattern matching on `resultStream` forces Agda computation
2. Agda computation pulls from `inputStream` (frame Colist)
3. Pulling from `inputStream` triggers Haskell's lazy I/O (reads stdin)
4. Frames flow through incrementally, results emitted as they're decided

**Memory Behavior**:
- No buffering - stdin read on demand as Agda pulls frames
- Only checker state + current frame in memory (not full trace)
- Old frames garbage-collected after processing

#### Python Layer (User Interface)

**Concurrent Streaming**:
```python
import json

class StreamingClient:
    """JSON streaming client for incremental LTL checking"""

    def __init__(self):
        self.proc = subprocess.Popen(['./aletheia'], ...)

    def parse_dbc(self, dbc: dict) -> dict:
        """Parse DBC file (JSON format)"""
        return self._send_command({
            "type": "command",
            "command": "parseDBC",
            "dbc": dbc
        })

    def set_properties(self, properties: list[dict]) -> dict:
        """Set LTL properties to check"""
        return self._send_command({
            "type": "command",
            "command": "setProperties",
            "properties": properties
        })

    def send_frame(self, timestamp: int, can_id: int, data: list[int]) -> dict:
        """Send a CAN frame for incremental checking"""
        return self._send_command({
            "type": "data",
            "timestamp": timestamp,
            "id": can_id,
            "data": data
        })
```

**Usage Pattern**:
```python
from aletheia import StreamingClient, Signal

property = Signal("Speed").less_than(220).always()

with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in can_trace:
        response = client.send_frame(frame.timestamp, frame.can_id, frame.data)
        if response.get("type") == "property":
            print(f"Violation: {response}")

    client.end_stream()

# Main thread: feed frames
for frame in frame_stream:
    checker.feed_frame(frame)

    # Check for violations (non-blocking)
    try:
        result = checker.get_result(timeout=0)
        print(f"Violation: {result}")
        # Python decides whether to continue or stop
    except queue.Empty:
        pass

checker.end_stream()

# Get final results
while True:
    result = checker.get_result()
    if result['status'] == 'complete':
        break
```

### Protocol Safety

**Guard Against Post-EndStream Frames**:
```haskell
-- After EndStream, verify no more data
extraInput <- hReady stdin
when extraInput $ do
  extra <- hGetLine stdin
  unless (all isSpace extra) $
    error "Protocol violation: frames after EndStream"
```

**Violation**: If Python sends frames after EndStream, binary terminates with error.

### Infinite Trace Semantics

**No Finite Trace Assumption**:
- DelayedColist is coinductive (supports infinite streams)
- LTL checker uses coinductive semantics
- EndStream is an explicit termination signal, not EOF

**Finite Prefix Semantics**:
- When EndStream is received, checker reports results based on finite prefix seen
- `Always(φ)`: True if no violations in prefix (cannot prove true for infinite trace)
- `Eventually(φ)`: False if not satisfied in prefix (may be satisfied later in infinite trace)

This matches standard LTL semantics over **finite prefixes of infinite traces**.

### Performance Characteristics

**Space Complexity**: O(|checker state| + |current frame|) - **not** O(|trace|)

**Time Complexity**: O(|frames| × |active properties| × |signals per frame|)
- Active properties decrease as they settle
- Amortized cost improves over trace

**Throughput Target**: 100K frames/sec (Phase 2B), 1M frames/sec (Phase 3)

## Implementation Phases

**Goal**: Process real-world automotive CAN data with LTL reasoning, via rich Python DSL

### Phase 1: Core Infrastructure ✅ COMPLETE

**Timeline**: 3 weeks (2 weeks spent)

**Completed**:
- ✅ Parser combinators with structural recursion (no fuel)
  - Functor/Applicative/Monad interfaces
  - Basic correctness properties (determinism)
  - Type-checks in ~10s with parallel GHC
- ✅ CAN signal encoding/decoding
  - Frame types with bounded IDs/DLC
  - Bit-level extraction/injection with endianness
  - Rational scaling with factor/offset
  - Proof: byte swap is involutive
- ✅ DBC JSON parser (migrated from YAML in Phase 2B)
  - Complete message/signal parsing
  - Correctness properties: bounded values, determinism
  - Runtime semantic checks
  - Rational parser handles fractional parts (0.25 → 1/4)
- ✅ Protocol integration and Main.agda
  - Command types: Echo, ParseDBC, ExtractSignal, InjectSignal
  - Command handlers with error handling
  - Response types with typed payloads
  - Full command routing working
- ✅ Build pipeline (Agda → Haskell → binary)
  - Hash-based dependency tracking (production-grade)
  - Automated FFI name mismatch detection
  - 0.26s no-op builds, ~11s incremental builds

**Remaining for Phase 1 Completion**:
- Python wrapper implementation (`python/aletheia/streaming_client.py` and `python/aletheia/binary_client.py`)
- Unit tests for all 4 critical fixes
- Integration testing: Python ↔ binary with real DBC file
- Performance benchmarking: signal extraction <1ms per signal
- ✅ Architectural constraint review (COMPLETED 2025-11-13)

**All 4 Critical Fixes Complete** (NO POSTULATES):
1. ✅ Rational parser: "0.25" → 1/4 using `power10` (automatic NonZero proof)
2. ✅ Signal scaling: Proper division with runtime zero-check
3. ✅ Response formatting: ℚ → String and Vec Byte 8 → hex
4. ✅ Byte array parser: Hex string → Vec Byte 8

**Exit Criteria**:
- All core infrastructure working end-to-end (Python → binary → Python)
- DBC parsing and signal extraction tested with real automotive data
- Zero postulates in production code (using `--safe` flag)
- Build system is reliable and fast
- Architecture validated against real-world requirements

### Phase 2A: LTL Core + Real-World Support (In Progress - Weeks 1-3/7 Complete ✅)

**Timeline**: 5-7 weeks total | **Current**: Weeks 1-3 complete, starting Python DSL

**Week 1 Completed** ✅:
- **Extended 29-bit CAN ID support** - ✅ IMPLEMENTED - CANId sum type (Standard | Extended)
- **Signal multiplexing support** - SignalPresence dependent type (Always | When)
- DBC parser updates for both features
- Protocol handlers with multiplexing validation
- **Commits**: 004cf42, a4461fb, 210bce8

**Week 2-3 Completed** ✅ (LTL Core):
- ✅ LTL syntax (existing Syntax.agda with all temporal operators)
- ✅ SignalPredicate (atomic propositions: Equals, LessThan, Between, ChangedBy)
- ✅ Bounded semantics (satisfiesAt for finite trace lists with repeat-last)
- ✅ Model checker (checkTrace with CheckResult type)
- ✅ Efficient decidable comparisons (single-check `_<ℚ_`, proof-ready)
- ✅ Coinductive traces with `fromListRepeat` (enables Phase 2B streaming)
- ✅ Python wrapper verified working (Phase 1 complete!)
- **Commits**: 760bb78, c527cd2, de48383, 4dac736, b84f5a3
- **Note**: Trace parser deferred to Phase 2B (streaming implementation)

**Week 4-5 Plan** (Python DSL v1) - **CURRENT FOCUS**:

**Risk Mitigation (Examples-First Design)**:
- Designed API from 10 real-world properties (speed limits, braking, VIN, etc.)
- Simplified DSL for Phase 2A (single-signal predicates only)
- Deferred complexity to Phase 2B (multi-signal, arithmetic, callbacks)

**Translation Correctness** (PROVABLE):
- Structural recursion on PythonLTL AST
- Theorem: `translate-preserves-semantics : ∀ prop trace → evalPython trace prop ≡ checkTrace trace (translate prop)`
- Proof strategy: Induction on LTL structure (base cases + temporal induction)

**Implementation Tasks** (9-11 days):
1. **Python DSL API** (1-2 days):
   - `Signal` class: `equals()`, `less_than()`, `greater_than()`, `between()`, `changed_by()`
   - `Predicate` class: `always()`, `eventually()`, `within()`, `never()`
   - `Property` class: `and_()`, `or_()`, `implies()`, `until()`
   - JSON serialization via `to_dict()`

2. **Update PythonLTL AST** (LTL/DSL/Python.agda) (1 day):
   - Add `Between`, `ChangedBy` to expressions
   - Add `Never`, `Until` to temporal operators
   - Ensure complete Phase 2A coverage

3. **DSL Parser** (LTL/DSL/Parser.agda) (2 days):
   - Parse YAML → PythonLTL AST
   - Reuse parser combinators from Phase 1
   - Test with hand-written YAML examples

4. **DSL Translator + Proof** (LTL/DSL/Translate.agda) (2-3 days):
   - `translate : PythonLTL → LTL SignalPredicate`
   - Prove `translate-preserves-semantics` by structural induction
   - Agda accepts proof due to structural recursion

5. **Protocol Integration** (1 day):
   - Add `CheckProperty` command to Protocol/Command.agda
   - Implement `handleCheckProperty` in Protocol/Handlers.agda
   - Wire to model checker

6. **End-to-End Testing** (2 days):
   - Test all 10 example properties
   - Validate with OpenDBC files (Hyundai, VW, Tesla)
   - Performance: <100ms for 1000-frame traces

**Example Properties to Test**:
- Speed limits: `Signal("Speed").less_than(220).always()`
- Braking: `brake_pressed.implies(speed_decreases.within(100))`
- Gear safety: `moving_forward.implies(in_reverse.never())`
- Battery range: `Signal("BatteryVoltage").between(11.5, 14.5).always()`
- VIN decoding: Multiplexed signal presence checks

**Week 6-7 Goals** (Validation):
- Integrate CheckProperty command into protocol
- Implement handleCheckProperty handler
- Test with real automotive CAN trace from OpenDBC
- Common properties: speed limits, signal bounds, temporal constraints
- Multiplexed signal handling (VIN decoding, power states)

**Deliverable**: Users can check LTL properties on real traces using Python DSL

### Phase 2B: Streaming Architecture & Async Python

**Timeline**: 6-9 days (expanded scope due to paradigm shift)
**Status**: Design phase complete, ready for implementation

**Overview**: Phase 2B represents a paradigm shift from finite-trace verification to streaming architecture with synchronous Python subprocess communication. The scope has expanded significantly to support real-world scenarios like mid-stream frame modification (Frame 153 debugging).

**Subdivision Rationale**: Three distinct sub-phases to track progress and provide clear checkpoints.

---

#### **Phase 2B.1: Core Protocol & Infrastructure** (Foundation)

**Timeline**: 2-3 days

**Goal**: Stable JSON protocol and multiplexing architecture working end-to-end

**Deliverables**:
1. **JSON Protocol Specification**
   - Complete message format specification (all message types)
   - JSON schema for validation (TypeScript-style or JSON Schema)
   - State machine definition (states, transitions, invariants, error conditions)

2. **Agda JSON Implementation**
   - JSON data types: `data JSON = JNull | JBool Bool | JNumber ℤ | JString String | JArray (List JSON) | JObject (List (String × JSON))`
   - JSON parser: `parseJSON : Parser JSON` (line-delimited)
   - JSON formatter: `formatJSON : JSON → String`
   - Lookup helpers: `lookupString`, `lookupInt`, `lookupArray`, etc.

3. **Agda Message Router**
   - Parse input messages, route by `type` field
   - Command router: dispatch to appropriate handler
   - Data router: send to LTL checker

4. **Agda Command Handlers**
   - `handleParseDBC : JSON → Response` - Parse and validate DBC, reset all state
   - `handleSetProperties : JSON → Response` - Parse and store LTL properties
   - `handleStartStream : JSON → Response` - Initialize LTL checker
   - `handleEncode : JSON → Response` - Encode signal value to CAN frame bytes
   - `handleDecode : JSON → Response` - Decode signal value from CAN frame bytes
   - `handleEndStream : JSON → Response` - Stop checking, emit pending results

5. **Agda State Machine**
   - `record StreamState` with DBC, properties, checker state
   - State validation: reject invalid command sequences (e.g., encode before parseDBC)
   - Error responses with clear messages

6. **Haskell Passthrough** (~15 lines, Option D: Truly Dumb)
   - Simple I/O loop: `forever (readLine >>= agdaProcess >>= writeLine)`
   - No threading, no queues, no multiplexing
   - Line buffering handled by `hGetLine` (reads until '\n')
   - Calls single MAlonzo function: `processJSONLine : String → String`
   - Sequential processing: one message in, one response out
   - **Latency**: ~100μs per message (acceptable for real-time and replay)

7. **Basic Python Client** (Sync API for testing)
   - Subprocess wrapper
   - Send command, read response (synchronous)
   - Validate JSON parsing works end-to-end

**Test Criteria**:
- Can send `parseDBC`, get success response
- Can send `encode`, get byte array response
- Can send `startStream` → data frame → `endStream`, get complete response
- Invalid command sequences return error (e.g., encode before parseDBC)

---

#### **Phase 2B.2: Streaming LTL + Async Python** (Core Feature)

**Timeline**: 2-3 days

**Goal**: Async streaming verification working, Frame 153 scenario functional

**Deliverables**:
1. **Agda Data Handler**
   - Integrate frame processing with LTL checker
   - Stream frames incrementally to checker
   - Return violations/satisfactions as immediate synchronous responses
   - Handle `endStream` to emit pending properties

2. **Synchronous Python Client API**
   - `StreamingClient` class using `subprocess.Popen`
   - Synchronous methods: `parse_dbc()`, `set_properties()`, `send_frame()`, etc.
   - Context manager support: `with StreamingClient() as client:`
   - Each method sends JSON → blocks → reads response
   - **Note**: Async/await interface deferred to Phase 5 for evaluation

3. **Subprocess Communication**
   - Single subprocess with stdin/stdout pipes
   - Line-buffered JSON protocol (one message per line)
   - Synchronous request-response pattern
   - Proper lifecycle: start subprocess, cleanup on exit

4. **Frame 153 Debugging Scenario**
   - User replays trace
   - At frame 153: call `client.build_frame(...)` to build modified frame
   - Inject modified frame into data stream
   - Continue streaming, verify fix works
   - Agda unaware stream was tampered with

5. **Integration Tests**
   - Real trace verification (100-1000 frames)
   - Multiple properties in single pass
   - Mid-stream modification (Frame 153 scenario)
   - Verify violations reported immediately (not batched)
   - Memory usage stays constant (no buffering)

**Test Criteria**:
- Frame 153 scenario works: modify frame, verify fix
- Can verify 1000-frame trace with 5 properties
- Violations appear immediately (within 1s of occurrence)
- Memory usage O(1) regardless of trace length

---

#### **Phase 2B.3: Counterexamples & Polish** (User Experience)

**Timeline**: 2-3 days

**Goal**: Production-ready streaming with excellent UX and documentation

**Deliverables**:
1. **Counterexample Generation**
   - Minimal violating trace (shrink to essential frames)
   - Include signal values at violation point
   - Clear error messages explaining violation
   - Python-friendly format (dict with timestamp, signals, reason)

2. **Rich Error Messages**
   - Command validation errors: "Cannot encode before parseDBC"
   - JSON parse errors: Line number, character position
   - DBC validation errors: Which message/signal is malformed
   - LTL property errors: Which operator is invalid

3. **DSL Extensions**
   - Custom user-defined predicates (Python lambda callbacks)
   - Standard library of common checks (bounds, monotonicity, etc.)
   - Composition helpers (and_then, or_else, when_then)

4. **Performance Tuning**
   - Profile on large traces (1M+ frames)
   - Optimize hot paths (JSON parsing, signal extraction, predicate evaluation)
   - Target: 100K frames/sec throughput

5. **USER_DOC.md** (Comprehensive User Documentation)
   - Async API reference with detailed examples
   - Frame 153 scenario tutorial (step-by-step)
   - Common patterns (read trace from file, real-time capture, etc.)
   - Error handling best practices
   - Cut-and-paste examples that just work
   - Troubleshooting guide

**Test Criteria**:
- User can understand and fix violations without asking us
- Examples in USER_DOC.md all run successfully
- Performance target met (100K frames/sec)
- Error messages are clear and actionable

---

**Phase 2B Total Deliverable**: Production-ready streaming LTL verification with synchronous Python subprocess communication, JSON protocol, and excellent UX. Users can verify properties on large traces, debug violations mid-stream, and extend with custom predicates.

### Phase 3: Verification + Performance

**Timeline**: 4-6 weeks

**Goals**: Prove correctness, optimize bottlenecks

**How Phase 2 Enables Verification**:

Phase 2 design decisions explicitly enable Phase 3 proofs:

1. **Decidable Comparisons** (Week 3):
   - Kept `_<?_` decidable: `⌊ x Rat.<? y ⌋`
   - Phase 3 theorem: `<-preserves-semantics : ∀ x y → (x <ℚ y ≡ true) ↔ (x < y)`
   - Proof witnesses extractable from `Dec` type

2. **Repeat-Last Semantics** (Week 3):
   - Coinductive traces with `fromListRepeat`
   - Phase 3 theorem: `repeat-last-soundness : ∀ xs φ → satisfiesAt xs φ ≡ (fromListRepeat xs ⊨ φ)`
   - Foundation already correct for verification

3. **Structural Recursion** (Phase 1):
   - Parser combinators structurally recursive on input length
   - Phase 3 theorem: `many-soundness : ∀ p input → ...`
   - Proofs straightforward due to structural termination

4. **Translation Correctness** (Week 4-5):
   - Translator structurally recursive on PythonLTL AST
   - Phase 3 theorem: `translate-preserves-semantics : ∀ prop trace → ...`
   - Proof by induction on LTL structure (Agda accepts immediately)

**Verification Targets**:
- ✅ Parser soundness (grammar formalization)
- ✅ LTL semantics correctness (matches standard definitions)
- ✅ Translation correctness (DSL → Core preserves meaning)
- ✅ Round-trip properties (parse ∘ print ≡ id)
- ⚠️ Replace runtime checks with proofs (NonZero for division)

**Performance Targets**:
- Profile on large traces (identify bottlenecks)
- Optimize hot paths (signal extraction, predicate evaluation)
- Benchmark goal: 1M frames/sec (10x current estimate)
- Optimizations enabled: Parser memoization, signal caching, predicate short-circuiting

**Deliverable**: Fully verified, production-performance system

### Phase 4: Production Hardening

**Timeline**: 3-4 weeks

**Goals**: Polish for real users

**UX**:
- Comprehensive error messages with line/column numbers
- User documentation (tutorials, examples, API reference)
- Standard library of common LTL checks
- Example gallery (real-world use cases from OpenDBC)

**Robustness**:
- Edge case handling and graceful degradation
- Logging and debugging support
- Integration with common tools (pandas, etc.)
- Signal overlap detection (safety check)
- Range validation (min ≤ max)

**Deliverable**: User-friendly, production-ready tool

### Phase 5: Optional Extensions

**Timeline**: Ongoing, based on user feedback

**Planned Enhancements**:
- 🟢 Value tables/enumerations (medium value, low cost)
- 🟢 Pretty-printer for DBC (medium value, low cost)
- 🟢 Additional DBC validation (signal overlap, range checks)
- 🟡 CAN-FD support (only if users request it - HIGH cost, 2-3 days minimum)
- 🔴 Extended features based on user feedback

**Dropped Features**:
- Real-time analysis (architectural limitation)
- Automatic property inference (research problem)
- GUI/visualization (use existing tools)
- J1939 protocol (different domain)

## Success Criteria

### Technical Excellence
- All core logic proven correct in Agda with `--safe` flag
- Zero postulates in production code paths
- Comprehensive test coverage (unit + integration)
- Performance: 1M frames/sec throughput

### Usability
- Python users can verify properties without knowing formal methods
- Clear error messages that users can act on
- Comprehensive documentation with examples
- Works with real-world DBC files from OpenDBC

### Reliability
- Robust DBC parsing with informative warnings
- Graceful handling of edge cases
- Transparent logging builds trust
- Build system is fast and reliable

## Module Structure

### Agda Modules (`src/Aletheia/`)

**32 total modules** organized into 9 packages. See [Module Safety Flags](../../CLAUDE.md#modules-not-using-safe-flag) in CLAUDE.md for detailed safety flag breakdown.

**Package Organization**:

#### **Parser/** (2 modules) - Parser combinators with structural recursion
- **Combinators.agda**: Structurally recursive parser type (functor/applicative/monad)
- **Properties.agda**: Determinism proofs, basic correctness properties

#### **CAN/** (6 modules) - CAN frame encoding, signal extraction, multiplexing
- **Frame.agda**: CANFrame type with bounded IDs (Standard 11-bit | Extended 29-bit)
- **Signal.agda**: SignalDef type (start bit, length, signed/unsigned, scaling)
- **Endianness.agda**: ByteOrder type with byte swap proof (involutive)
- **Encoding.agda**: Bit-level signal extraction/injection with scaling
- **ExtractionResult.agda**: Rich error types (Success, SignalNotInDBC, SignalNotPresent, ExtractionFailed)
- **SignalExtraction.agda**: High-level API with multiplexing support (checkMultiplexor, extractSignalWithContext)

#### **DBC/** (3 modules) - DBC database format (JSON, not YAML)
- **Types.agda**: DBCMessage, DBCSignal, SignalPresence (Always | When multiplexor)
- **JSONParser.agda**: JSON DBC parser with bounded value validation
- **Properties.agda**: Bounded ID/DLC/startBit proofs, determinism

#### **LTL/** (5 modules) - Linear Temporal Logic model checking
- **Syntax.agda**: LTL formula AST (Atomic, Not, And, Or, Next, Always, Eventually, Until)
- **Coinductive.agda**: Infinite trace semantics with coinductive streams (`--guardedness`)
- **Incremental.agda**: Streaming LTL checker with early termination
- **SignalPredicate.agda**: Signal predicates (Equals, LessThan, GreaterThan, Between, ChangedBy)
- **JSON.agda**: JSON LTL property parser (Python DSL → Agda AST)

#### **Trace/** (3 modules) - CAN trace representation
- **Stream.agda**: Generic stream utilities
- **CANTrace.agda**: TimedFrame type (timestamp + CANFrame)
- **Context.agda**: Trace context for debugging

#### **Protocol/** (4 modules) - JSON streaming protocol
- **JSON.agda**: Core JSON parser/formatter with rational support
- **Routing.agda**: Command routing (parseDBC, setProperties, startStream, endStream, dataFrame)
- **Response.agda**: Response types (Success, Error, Ack, PropertyViolation, Complete)
- **StreamState.agda**: Streaming state machine with coinductive checking (`--guardedness`)

#### **Data/** (2 modules) - Utility data structures
- **Message.agda**: Generic message type
- **DelayedColist.agda**: Thunk-based coinductive colist (`--guardedness`)

#### **Core**
- **Prelude.agda**: Common imports and utilities (findByPredicate, lookupByKey, CAN ID bounds)
- **Main.agda**: Entry point for MAlonzo compilation (`--sized-types`, calls processCommand)

## Development Workflow

See [CLAUDE.md](../../CLAUDE.md) for detailed workflows and contributing guidelines.

**Quick Reference**:
```bash
# Type-check Agda module (fast feedback)
cd src && agda +RTS -N32 -RTS Aletheia/YourModule.agda

# Full build
cabal run shake -- build

# Clean build
cabal run shake -- clean
cabal run shake -- build

# Install Python package (requires active venv)
source venv/bin/activate
cabal run shake -- install-python
```

## Parser Correctness Strategy

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

## Known Limitations (By Design)

### Phase 1 Limitations:

**Standard CAN Only** (no CAN-FD):
- Fixed 8-byte payload (`Vec Byte 8`)
- ✅ Both standard (11-bit) and extended (29-bit) CAN IDs supported
- DLC 0-8 only (CAN-FD has different encoding)
- **Rationale**: 100% of OpenDBC uses standard CAN, 0% CAN-FD
- **Risk**: Refactoring later would take 1+ week if LTL assumes fixed frames
- **Decision**: Accept constraint, defer CAN-FD to Phase 5

**No Signal Multiplexing** (until Phase 2A):
- All signals assumed always present
- **Phase to Add**: Phase 2A (2-3 days)
- **Impact**: Needed for VIN, diagnostics, power states

**No Value Tables** (enumerations):
- Signal values are numeric only
- **Phase to Add**: Phase 5 (additive feature)

**Simplified Protocol**:
- One command per binary invocation
- No protocol versioning yet
- **Phase to Enhance**: Phase 4 (streaming protocol)

## Documentation Structure

### Root Documentation
- **README.md**: Quick start and project overview
- **CLAUDE.md**: Project rules, development workflow, and contributing guidelines
- **PROJECT_STATUS.md**: Phase completion status, milestones, and roadmap

### docs/architecture/
- **DESIGN.md**: This document - design decisions and roadmap
- **PROTOCOL.md**: Complete JSON streaming protocol specification
- **ARCHITECTURAL_ANALYSIS.md**: Research findings on CAN protocols

### docs/development/
- **BUILDING.md**: Step-by-step build instructions
- **PYTHON_API.md**: Python client library API reference

---

**Document Status**: Living document, updated as project progresses

For up-to-date phase information, milestones, and completion status, see [PROJECT_STATUS.md](../../PROJECT_STATUS.md).

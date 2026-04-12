# Aletheia Streaming Protocol

**Purpose**: Complete specification of the FFI protocol for CAN frame analysis with LTL checking.
**Version**: 1.1.1
**Last Updated**: 2026-04-02

---

## Audience

This document is for:
- Python, C++, and Go developers integrating the Aletheia client with custom tooling
- Maintainers modifying the JSON protocol or FFI boundary
- System architects understanding the communication layer

**Prerequisites**: Familiarity with JSON and CAN bus basics. No Agda or Haskell knowledge needed.

> Most users don't need this document. See the [Interface Guide](../reference/INTERFACES.md) for Check API, YAML, and Excel workflows, or the [Python API Guide](../reference/PYTHON_API.md) for the `AletheiaClient` reference.

---

## Overview

Aletheia uses a JSON protocol for communication between language bindings (Python, C++, Go) and the Agda/Haskell core. Each message is a single JSON object passed as a string via FFI (Foreign Function Interface) function calls.

**Communication Model**:
- Two FFI entry points, both returning JSON response strings:
  - `aletheia_process()`: JSON string in — handles all commands (parseDBC, setProperties, startStream, etc.)
  - `aletheia_send_frame()`: Binary data in — streaming hot path for CAN data frames (no JSON parsing on input)
- One call per response (request-response)
- Sequential processing (no threading or queuing)
- No subprocess or IPC — everything runs in-process via `libaletheia-ffi.so`

**State Machine**:
```
WaitingForDBC → ParseDBC → ReadyToStream → SetProperties → ReadyToStream
                                          → StartStream → Streaming → SendFrame* → Streaming
                                                                     → EndStream → ReadyToStream
```

---

## Message Types

All messages have a `"type"` field that determines how they are processed.

### Type Tags
- `"command"`: Control commands (parseDBC, extractAllSignals, buildFrame, updateFrame, validateDBC, formatDBC, setProperties, startStream, endStream)

> **Note**: Data frames are sent via the binary `aletheia_send_frame()` entry point, not as JSON. See [Binary Frame Entry Point](#binary-frame-entry-point) below.

---

## Commands

### 1. ParseDBC

Load a DBC (Database CAN) structure from JSON format.

**Request**:
```json
{
  "type": "command",
  "command": "parseDBC",
  "dbc": {
    "version": "1.0",
    "messages": [
      {
        "id": 256,
        "name": "SpeedMessage",
        "dlc": 8,
        "extended": false,
        "sender": "ECU",
        "signals": [
          {
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
          }
        ]
      }
    ]
  }
}
```

**Response** (Success):
```json
{
  "status": "success",
  "message": "DBC parsed successfully"
}
```

**Response** (Error):
```json
{
  "status": "error",
  "message": "Missing required field: messages"
}
```

**Fields**:
- `dbc.version`: DBC format version (currently "1.0")
- `dbc.messages`: Array of CAN message definitions
  - `id`: CAN message ID (0-2047 for standard, 0-536870911 for extended)
  - `name`: Message name (string)
  - `dlc`: Data Length Code (0-15; DLC 0-8 map directly to byte counts, 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64 bytes for CAN-FD)
  - `extended`: Boolean, true for 29-bit IDs
  - `sender`: Node that sends this message
  - `signals`: Array of signal definitions
    - `name`: Signal name (must be unique within message)
    - `startBit`: Bit position in frame (0-511 for CAN-FD; 0-63 for standard CAN)
    - `length`: Signal length in bits (1-512 for CAN-FD; 1-64 for standard CAN)
    - `byteOrder`: "little_endian" or "big_endian"
    - `signed`: Boolean, true for signed integers
    - `factor`: Scaling factor (rational as decimal)
    - `offset`: Offset applied after scaling
    - `minimum`: Minimum physical value
    - `maximum`: Maximum physical value
    - `presence`: "always" for always-present signals (default if omitted); multiplexed signals use `multiplexor` and `multiplex_values` fields instead (see Multiplexing Support below)

**State Transition**: `WaitingForDBC` → `ReadyToStream`

---

### Multiplexing Support

Aletheia supports multiplexed signals (signals that are conditionally present based on a multiplexor signal's value).

**Signal Presence Formats**:

#### Always Present
```json
{"presence": "always"}
```
Signal is always present in the frame.

#### Conditional Presence (Multiplexed)

Multiplexed signals use flat `multiplexor` and `multiplex_values` fields instead of `presence`:

```json
{
  "multiplexor": "MuxSignal",
  "multiplex_values": [1]
}
```

Signal is only present when the multiplexor signal's value is in the `multiplex_values` array. Single-value mux uses a one-element array (e.g., `[1]`); extended mux (SG_MUL_VAL_) uses multiple values (e.g., `[0, 1, 3]`). The `presence` field is omitted for multiplexed signals.

**Example** (Multiplexed Message):
```json
{
  "id": 512,
  "name": "MultiplexedMessage",
  "dlc": 8,
  "extended": false,
  "sender": "ECU",
  "signals": [
    {
      "name": "MuxSignal",
      "startBit": 0,
      "length": 8,
      "byteOrder": "little_endian",
      "signed": false,
      "factor": 1.0,
      "offset": 0.0,
      "minimum": 0.0,
      "maximum": 3.0,
      "unit": "",
      "presence": "always"
    },
    {
      "name": "Signal_Mux0",
      "startBit": 8,
      "length": 16,
      "byteOrder": "little_endian",
      "signed": false,
      "factor": 1.0,
      "offset": 0.0,
      "minimum": 0.0,
      "maximum": 1000.0,
      "unit": "rpm",
      "multiplexor": "MuxSignal",
      "multiplex_values": [0]
    },
    {
      "name": "Signal_Mux1",
      "startBit": 8,
      "length": 16,
      "byteOrder": "little_endian",
      "signed": true,
      "factor": 0.1,
      "offset": 0.0,
      "minimum": -50.0,
      "maximum": 150.0,
      "unit": "°C",
      "multiplexor": "MuxSignal",
      "multiplex_values": [1]
    }
  ]
}
```

**Behavior**:
- When `MuxSignal == 0`, only `Signal_Mux0` is extracted
- When `MuxSignal == 1`, only `Signal_Mux1` is extracted
- Attempting to extract a signal that's not present returns an error
- Multiplexor signal must be defined in the same message and have `"presence": "always"`

**Implementation**: See [DESIGN.md](DESIGN.md) for the Agda module structure. The multiplexor logic is in the CAN signal extraction module; signal presence types are in the DBC types module.

---

### 2. ExtractAllSignals

Extract all signal values from a CAN frame without streaming.

**Request**:
```json
{
  "type": "command",
  "command": "extractAllSignals",
  "canId": 256,
  "dlc": 8,
  "extended": false,
  "data": [232, 3, 0, 0, 0, 0, 0, 0]
}
```

**Response** (Success):
```json
{
  "status": "success",
  "values": [
    {"name": "Speed", "value": 100.0}
  ],
  "errors": [],
  "absent": []
}
```

**Fields**:
- `canId`: CAN message ID (integer, must match a message in the loaded DBC)
- `dlc`: Data Length Code (0-15)
- `data`: Array of bytes (0-255), length must match `dlcToBytes(dlc)`
- Response `values`: Successfully extracted signals with physical values
- Response `errors`: Signals that failed extraction (with error message)
- Response `absent`: Multiplexed signals not present in this frame

**State Requirements**: Must have called `parseDBC`. Does NOT require streaming mode.

---

### 3. BuildFrame

Encode signal values into a new CAN frame (starting from all zeros).

**Request**:
```json
{
  "type": "command",
  "command": "buildFrame",
  "canId": 256,
  "dlc": 8,
  "extended": false,
  "signals": [
    {"name": "Speed", "value": 100.0}
  ]
}
```

**Response** (Success):
```json
{
  "status": "success",
  "data": [232, 3, 0, 0, 0, 0, 0, 0]
}
```

**Fields**:
- `canId`: CAN message ID (integer, must match a message in the loaded DBC)
- `dlc`: Data Length Code (0-15)
- `extended`: Whether to use 29-bit extended CAN ID (boolean)
- `signals`: Array of {name, value} objects to encode
- Response `data`: Encoded frame payload (length matches `dlcToBytes(dlc)`)

**State Requirements**: Must have called `parseDBC`. Does NOT require streaming mode.

---

### 4. UpdateFrame

Update specific signal values in an existing CAN frame.

**Request**:
```json
{
  "type": "command",
  "command": "updateFrame",
  "canId": 256,
  "dlc": 8,
  "extended": false,
  "data": [232, 3, 0, 0, 0, 0, 0, 0],
  "signals": [
    {"name": "Speed", "value": 200.0}
  ]
}
```

**Response** (Success):
```json
{
  "status": "success",
  "data": [208, 7, 0, 0, 0, 0, 0, 0]
}
```

**Fields**:
- `canId`: CAN message ID (integer, must match a message in the loaded DBC)
- `dlc`: Data Length Code (0-15)
- `data`: Existing frame to modify (array of bytes, length must match `dlcToBytes(dlc)`)
- `signals`: Array of {name, value} objects to update
- Response `data`: Updated frame payload (same length as input)

**State Requirements**: Must have called `parseDBC`. Does NOT require streaming mode.

---

### 5. ValidateDBC

Validate a DBC definition for structural correctness. Returns all issues found (not just the first). Does not modify client state.

**Request**:
```json
{
  "type": "command",
  "command": "validateDBC",
  "dbc": { ... }
}
```

**Response**:
```json
{
  "status": "validation",
  "has_errors": true,
  "issues": [
    {"severity": "error", "code": "signal_overlap", "detail": "..."},
    {"severity": "warning", "code": "empty_message", "detail": "..."}
  ]
}
```

**Fields**:
- `dbc`: Complete DBC definition (same schema as `parseDBC`)
- Response `has_errors`: true if any issue has severity "error"
- Response `issues`: Array of validation issues

**Issue Codes** (15 total):
- **Error** (9): `duplicate_message_id`, `duplicate_signal_name`, `factor_zero`, `multiplexor_not_found`, `multiplexor_cycle`, `global_name_collision`, `min_exceeds_max`, `signal_exceeds_dlc`, `signal_overlap`
- **Warning** (6): `bit_length_zero`, `duplicate_message_name`, `offset_scale_range`, `empty_message`, `start_bit_out_of_range`, `bit_length_excessive`

**State Requirements**: Does NOT require `parseDBC`. Does NOT modify client state (read-only probe).

---

### 6. FormatDBC

Export the currently-loaded DBC as JSON.

**Request**:
```json
{
  "type": "command",
  "command": "formatDBC"
}
```

**Response** (Success):
```json
{
  "status": "success",
  "dbc": {
    "version": "1.0",
    "messages": [...]
  }
}
```

**Response** (Error):
```json
{
  "status": "error",
  "message": "FormatDBC: No DBC loaded"
}
```

**Fields**:
- No input fields — uses the currently-loaded DBC
- Response `dbc`: Complete DBC definition in JSON format (same schema as the `parseDBC` input)

**State Requirements**: Must have called `parseDBC`. Does NOT modify client state (read-only).

---

### 7. SetProperties

Define LTL properties to check against the frame stream.

**Request**:
```json
{
  "type": "command",
  "command": "setProperties",
  "properties": [
    {
      "operator": "always",
      "formula": {
        "operator": "atomic",
        "predicate": {
          "predicate": "lessThan",
          "signal": "Speed",
          "value": 250
        }
      }
    }
  ]
}
```

**Response** (Success):
```json
{
  "status": "success",
  "message": "Properties set successfully"
}
```

**Response** (Error):
```json
{
  "status": "error",
  "message": "Signal 'Speed' not found in DBC"
}
```

**State Requirements**: Must be in `ReadyToStream` state (after parseDBC)
**State Transition**: `ReadyToStream` → `ReadyToStream` (idempotent)

See [LTL Property Format](#ltl-property-format) section below for complete schema.

---

### 8. StartStream

Begin streaming mode for processing data frames.

**Request**:
```json
{
  "type": "command",
  "command": "startStream"
}
```

**Response** (Success):
```json
{
  "status": "success",
  "message": "Streaming started"
}
```

**Response** (Error):
```json
{
  "status": "error",
  "message": "Must call ParseDBC before StartStream"
}
```

**State Requirements**: Must be in `ReadyToStream` state
**State Transition**: `ReadyToStream` → `Streaming`

---

### 9. EndStream

End streaming mode and return final results.

**Request**:
```json
{
  "type": "command",
  "command": "endStream"
}
```

**Response**:
```json
{
  "status": "complete",
  "results": [
    {"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}},
    {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 4523, "denominator": 1}, "reason": "Always violated"}
  ]
}
```

**State Requirements**: Must be in `Streaming` state
**State Transition**: `Streaming` → `ReadyToStream` (can stream again)

---

## Binary Frame Entry Point

### aletheia_send_frame

Send a CAN data frame for LTL analysis. This is the high-performance streaming entry point — frame components are passed as binary C values, bypassing JSON parsing on input.

**C signature** (see `aletheia.h`):
```c
char *aletheia_send_frame(void *state, unsigned long long timestamp,
                          unsigned int can_id, unsigned char extended,
                          unsigned char dlc, const unsigned char *data,
                          unsigned char data_len);
```

**Parameters**:
- `timestamp`: Frame timestamp in microseconds
- `can_id`: CAN message ID (must match a message in the loaded DBC)
- `extended`: 0 for standard 11-bit ID, 1 for extended 29-bit ID
- `dlc`: Data Length Code (0-15)
- `data`: Pointer to payload bytes
- `data_len`: Number of payload bytes (must equal `dlcToBytes(dlc)`)

**Response** (Acknowledged):
```json
{
  "status": "ack"
}
```

**Response** (Property Violation):
```json
{
  "type": "property",
  "status": "fails",
  "property_index": {"numerator": 0, "denominator": 1},
  "timestamp": {"numerator": 1000, "denominator": 1},
  "reason": "Always violated"
}
```

**Response** (Property Satisfaction):
```json
{
  "type": "property",
  "status": "holds",
  "property_index": {"numerator": 0, "denominator": 1}
}
```

**State Requirements**: Must be in `Streaming` state (after `startStream` command via `aletheia_process()`)

**Processing**:
1. Construct MAlonzo types directly from raw C values (no JSON parsing)
2. Extract all signals from frame using DBC
3. Evaluate all LTL properties
4. If violation or satisfaction detected, return property response immediately
5. Otherwise, return acknowledgment

**Why binary?** Eliminates JSON serialization/parsing overhead for the streaming hot path. Result: 4.3x throughput for CAN 2.0B, 9.1x for CAN-FD compared to the JSON path (see [PROJECT_STATUS.md](../../PROJECT_STATUS.md#key-metrics) for benchmark methodology and per-language numbers). All language bindings (Python, C++, Go) use this entry point for `send_frame()`.

---

## Response Types

### Success Response
```json
{
  "status": "success",
  "message": "Operation completed"
}
```

### Error Response
```json
{
  "status": "error",
  "message": "Descriptive error message"
}
```

### Acknowledgment Response
```json
{
  "status": "ack"
}
```
Used for data frames when no violation is detected.

### Property Response
```json
{
  "type": "property",
  "status": "fails",
  "property_index": {"numerator": 0, "denominator": 1},
  "timestamp": {"numerator": 300, "denominator": 1},
  "reason": "Always violated"
}
```

**Fields**:
- `status`: `"fails"` or `"holds"`
- `property_index`: Index of the property (rational)
- `timestamp`: Timestamp of the violation (rational, only present when `status` is `"fails"`)
- `reason`: Human-readable explanation (only present when `status` is `"fails"`)

### Complete Response
```json
{
  "status": "complete",
  "results": [
    {"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}},
    {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 4523, "denominator": 1}, "reason": "Always violated"}
  ]
}
```
Returned when streaming ends. The `results` array contains per-property finalization verdicts.

---

## LTL Property Format

### Signal Predicates (Atomic)

#### Equals
```json
{
  "predicate": "equals",
  "signal": "Speed",
  "value": 100
}
```

#### LessThan
```json
{
  "predicate": "lessThan",
  "signal": "Speed",
  "value": 250
}
```

#### GreaterThan
```json
{
  "predicate": "greaterThan",
  "signal": "RPM",
  "value": 0
}
```

#### Between
```json
{
  "predicate": "between",
  "signal": "Temperature",
  "min": 60,
  "max": 90
}
```

#### LessThanOrEqual
```json
{
  "predicate": "lessThanOrEqual",
  "signal": "Speed",
  "value": 250
}
```

#### GreaterThanOrEqual
```json
{
  "predicate": "greaterThanOrEqual",
  "signal": "RPM",
  "value": 800
}
```

#### ChangedBy
```json
{
  "predicate": "changedBy",
  "signal": "Speed",
  "delta": -10
}
```
Directional change detection. Positive delta: `curr - prev >= delta` (increased by at least delta). Negative delta: `curr - prev <= delta` (decreased by at least |delta|).

#### StableWithin
```json
{
  "predicate": "stableWithin",
  "signal": "Temperature",
  "tolerance": 2.0
}
```
Magnitude tolerance: `|curr - prev| <= tolerance`. Tests that a signal's value stayed within tolerance of its previous value.

---

### LTL Temporal Operators

#### Atomic (wraps a signal predicate)
```json
{
  "operator": "atomic",
  "predicate": {
    "predicate": "equals",
    "signal": "Speed",
    "value": 100
  }
}
```

#### Not
```json
{
  "operator": "not",
  "formula": {...}
}
```

#### And
```json
{
  "operator": "and",
  "left": {...},
  "right": {...}
}
```

#### Or
```json
{
  "operator": "or",
  "left": {...},
  "right": {...}
}
```

#### Next
```json
{
  "operator": "next",
  "formula": {...}
}
```
Property must hold in the next frame.

#### Always (Globally)
```json
{
  "operator": "always",
  "formula": {...}
}
```
Property must hold for all frames in the trace.

#### Eventually (Finally)
```json
{
  "operator": "eventually",
  "formula": {...}
}
```
Property must hold at some point in the trace.

#### Until
```json
{
  "operator": "until",
  "left": {...},
  "right": {...}
}
```
`left` must hold until `right` becomes true.

#### Release
```json
{
  "operator": "release",
  "left": {...},
  "right": {...}
}
```
Dual of Until: `right` must hold until `left` releases it (or `right` holds forever).

#### MetricEventually (Bounded Eventually)
```json
{
  "operator": "metricEventually",
  "timebound": 1000,
  "formula": {...}
}
```
Property must hold within `timebound` microseconds.

#### MetricAlways (Bounded Always)
```json
{
  "operator": "metricAlways",
  "timebound": 5000,
  "formula": {...}
}
```
Property must hold for the next `timebound` microseconds.

#### MetricUntil (Bounded Until)
```json
{
  "operator": "metricUntil",
  "timebound": 2000,
  "left": {...},
  "right": {...}
}
```
`left` must hold until `right` becomes true, within `timebound` microseconds.

#### MetricRelease (Bounded Release)
```json
{
  "operator": "metricRelease",
  "timebound": 2000,
  "left": {...},
  "right": {...}
}
```
Bounded dual of Until: `right` must hold until `left` releases it, within `timebound` microseconds.

---

### Complete Example

**Property**: "Speed must always be less than 250 km/h"

```json
{
  "operator": "always",
  "formula": {
    "operator": "atomic",
    "predicate": {
      "predicate": "lessThan",
      "signal": "Speed",
      "value": 250
    }
  }
}
```

---

## Rational Number Encoding

Rational numbers are represented in two formats:

### 1. Decimal Format (Input)
```json
{"value": 0.25}
```
Accepted in input, converted to rational internally.

### 2. Object Format (Output)
```json
{"numerator": 1, "denominator": 4}
```
Used in responses for exact representation.

**Why Two Formats?**
- Decimal format is convenient for users (e.g., `"factor": 0.1`)
- Object format preserves exact values (e.g., 1/3 has no finite decimal)
- Parser accepts both, formatter outputs object format

**Examples**:
- `0.25` → `{"numerator": 1, "denominator": 4}`
- `1.5` → `{"numerator": 3, "denominator": 2}`
- `100` → `{"numerator": 100, "denominator": 1}`

**Note**: The JSON format exposes the actual denominator for clarity, even though the internal representation may differ.

---

## Example Session

### 1. Parse DBC
```json
>>> {"type": "command", "command": "parseDBC", "dbc": {...}}
<<< {"status": "success", "message": "DBC parsed successfully"}
```

### 2. Set Properties
```json
>>> {"type": "command", "command": "setProperties", "properties": [{...}]}
<<< {"status": "success", "message": "Properties set successfully"}
```

### 3. Start Streaming
```json
>>> {"type": "command", "command": "startStream"}
<<< {"status": "success", "message": "Streaming started"}
```

### 4. Send Data Frames (via `aletheia_send_frame`)
```
>>> aletheia_send_frame(state, 100, 256, 0, 8, [0xE8,0x03,0,0,0,0,0,0], 8)
<<< {"status": "ack"}

>>> aletheia_send_frame(state, 200, 256, 0, 8, [0xD0,0x07,0,0,0,0,0,0], 8)
<<< {"status": "ack"}

>>> aletheia_send_frame(state, 300, 256, 0, 8, [0x28,0x0A,0,0,0,0,0,0], 8)
<<< {"type": "property", "status": "fails", "property_index": {"numerator": 0, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}
```

### 5. End Streaming
```json
>>> {"type": "command", "command": "endStream"}
<<< {"status": "complete", "results": [{"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}}, {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}]}
```

---

## Error Handling

### Common Errors

**Invalid JSON**:
```
<<< {"status": "error", "message": "Failed to parse JSON: unexpected token"}
```

**Missing Required Field**:
```
<<< {"status": "error", "message": "Missing required field: 'command'"}
```

**Invalid State Transition**:
```
<<< {"status": "error", "message": "Must call ParseDBC before StartStream"}
```

**Signal Not Found**:
```
<<< {"status": "error", "message": "Signal 'InvalidSignal' not found in DBC"}
```

**Message ID Not Found**:
```
<<< {"status": "error", "message": "Message ID 999 not found in DBC"}
```

---

## Implementation Notes

### FFI Entry Points
- **Commands**: JSON string via `aletheia_process(state, json_string)` — all non-data-frame operations
- **Data frames**: Binary via `aletheia_send_frame(state, timestamp, can_id, ...)` — streaming hot path
- Both return a JSON response string (freed with `aletheia_free_str`)
- No newline delimiters needed — each FFI call is one complete message
- State is managed via `StablePtr (IORef StreamState)` on the Haskell side

### Sequential Processing
- Calls are processed sequentially within the same process
- No threading or queuing
- Each FFI call blocks until complete and returns immediately
- Data frames return ack or violation immediately

### State Validation
- All state transitions are validated in Agda
- Invalid transitions return error responses
- State machine enforces correct protocol usage

### Type Safety
- JSON parsing happens in Agda (fully verified)
- Malformed JSON is rejected with error message
- All logic uses Agda's type system (`--safe --without-K`)

---

## See Also

- [DESIGN.md](DESIGN.md) - Overall architecture and design decisions
- [PROJECT_STATUS.md](../../PROJECT_STATUS.md) - Phase completion status and milestones
- [PYTHON_API.md](../reference/PYTHON_API.md) - Python client library

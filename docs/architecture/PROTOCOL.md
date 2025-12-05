# Aletheia JSON Streaming Protocol

**Purpose**: Complete specification of the JSON protocol for CAN frame analysis with LTL checking.
**Version**: 1.0 (Phase 2B.1)
**Last Updated**: 2025-12-02

---

## Overview

Aletheia uses a line-delimited JSON protocol for bidirectional communication between Python and the Agda/Haskell binary. Each message is a single JSON object on one line, terminated by a newline.

**Communication Model**:
- Python sends commands and data frames over stdin
- Binary sends responses over stdout
- One JSON object per line (line-delimited)
- Sequential processing (no threading or queuing)

**State Machine**:
```
WaitingForDBC → ParseDBC → ReadyToStream → SetProperties → ReadyToStream
                                          → StartStream → Streaming
                                          → DataFrame* → EndStream
```

---

## Message Types

All messages have a `"type"` field that determines how they are processed.

### Type Tags
- `"command"`: Control commands (parseDBC, setProperties, startStream, endStream)
- `"data"`: CAN data frames to be analyzed

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
  - `dlc`: Data Length Code (0-8 bytes)
  - `extended`: Boolean, true for 29-bit IDs
  - `sender`: Node that sends this message
  - `signals`: Array of signal definitions
    - `name`: Signal name (must be unique within message)
    - `startBit`: Bit position in frame (0-63)
    - `length`: Signal length in bits (1-64)
    - `byteOrder`: "little_endian" or "big_endian"
    - `signed`: Boolean, true for signed integers
    - `factor`: Scaling factor (rational as decimal)
    - `offset`: Offset applied after scaling
    - `minimum`: Minimum physical value
    - `maximum`: Maximum physical value
    - `presence`: "always" or multiplexed object (see Multiplexing Support below)

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
```json
{
  "presence": {
    "when": {
      "multiplexor": "MuxSignal",
      "value": 1
    }
  }
}
```

Signal is only present when the multiplexor signal equals the specified value.

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
      "presence": {"when": {"multiplexor": "MuxSignal", "value": 0}}
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
      "presence": {"when": {"multiplexor": "MuxSignal", "value": 1}}
    }
  ]
}
```

**Behavior**:
- When `MuxSignal == 0`, only `Signal_Mux0` is extracted
- When `MuxSignal == 1`, only `Signal_Mux1` is extracted
- Attempting to extract a signal that's not present returns an error
- Multiplexor signal must be defined in the same message and have `"presence": "always"`

**Implementation**: See `src/Aletheia/CAN/SignalExtraction.agda` (checkMultiplexor, checkSignalPresence) and `src/Aletheia/DBC/Types.agda` (SignalPresence type).

---

### 2. SetProperties

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

### 3. StartStream

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

### 4. EndStream

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
  "status": "complete"
}
```

**State Requirements**: Must be in `Streaming` state
**State Transition**: `Streaming` → `ReadyToStream` (can stream again)

---

## Data Frames

### DataFrame

Send a CAN frame for analysis.

**Request**:
```json
{
  "type": "data",
  "timestamp": 1000,
  "id": 256,
  "data": [0x10, 0x27, 0, 0, 0, 0, 0, 0]
}
```

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
  "status": "violation",
  "property_index": {"numerator": 0, "denominator": 1},
  "timestamp": {"numerator": 1000, "denominator": 1},
  "reason": "Always violated"
}
```

**Fields**:
- `timestamp`: Frame timestamp in microseconds (integer or rational)
- `id`: CAN message ID (must match a message in the loaded DBC)
- `data`: Array of 8 bytes (0-255)

**State Requirements**: Must be in `Streaming` state
**Processing**:
1. Extract all signals from frame using DBC
2. Evaluate all LTL properties
3. If violation detected, return property response immediately
4. Otherwise, return acknowledgment

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
  "status": "violation",
  "property_index": {"numerator": 0, "denominator": 1},
  "timestamp": {"numerator": 300, "denominator": 1},
  "reason": "Always violated"
}
```

**Fields**:
- `status`: "violation", "satisfied", or "pending"
- `property_index`: Index of the property that failed (rational)
- `timestamp`: Timestamp of the frame that caused the violation (rational)
- `reason`: Human-readable explanation

### Complete Response
```json
{
  "status": "complete"
}
```
Returned when streaming ends.

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

#### ChangedBy
```json
{
  "predicate": "changedBy",
  "signal": "Speed",
  "delta": 10
}
```
Checks if signal changed by more than `delta` from previous frame.

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

**Implementation Note**: Agda's `ℚ` type uses unnormalized rationals internally, storing `denominator - 1`. The JSON format exposes the actual denominator for clarity.

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

### 4. Send Data Frames
```json
>>> {"type": "data", "timestamp": 100, "id": 256, "data": [0xE8, 0x03, 0, 0, 0, 0, 0, 0]}
<<< {"status": "ack"}

>>> {"type": "data", "timestamp": 200, "id": 256, "data": [0xD0, 0x07, 0, 0, 0, 0, 0, 0]}
<<< {"status": "ack"}

>>> {"type": "data", "timestamp": 300, "id": 256, "data": [0x28, 0x0A, 0, 0, 0, 0, 0, 0]}
<<< {"type": "property", "status": "violation", "property_index": {"numerator": 0, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}
```

### 5. End Streaming
```json
>>> {"type": "command", "command": "endStream"}
<<< {"status": "complete"}
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

### Line-Delimited JSON
- Each message is exactly one line (no embedded newlines)
- Lines are terminated with `\n`
- Haskell uses `hGetLine` for buffering
- Python uses `readline()` and `write(json + "\n")`

### Sequential Processing
- Binary processes messages sequentially
- No threading or queuing
- Commands block until complete
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
- [CHANGELOG.md](CHANGELOG.md) - Phase 2B.1 implementation details
- [PYTHON_API.md](../development/PYTHON_API.md) - Python client library

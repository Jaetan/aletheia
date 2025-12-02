# Aletheia Python API Reference

**Purpose**: Complete guide to using Aletheia from Python for CAN frame analysis and LTL verification.
**Version**: 0.1.0 (Phase 2B.1)
**Last Updated**: 2025-12-02

---

## Quick Start

```python
from aletheia.streaming_client import StreamingClient

# Load DBC (Database CAN) with your vehicle's signal definitions
dbc_json = {
    "version": "1.0",
    "messages": [{
        "id": 256,
        "name": "SpeedMessage",
        "dlc": 8,
        "extended": False,
        "sender": "ECU",
        "signals": [{
            "name": "Speed",
            "startBit": 0,
            "length": 16,
            "byteOrder": "little_endian",
            "signed": False,
            "factor": 0.1,
            "offset": 0.0,
            "minimum": 0.0,
            "maximum": 300.0,
            "unit": "km/h",
            "presence": "always"
        }]
    }]
}

# Define LTL property: "Speed must always be less than 250 km/h"
property = {
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

# Check CAN frames against property
with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property])
    client.start_stream()

    # Send frames from your trace
    for frame in can_trace:
        response = client.send_frame(
            timestamp=frame.timestamp,
            can_id=frame.id,
            data=frame.data  # [byte0, byte1, ..., byte7]
        )

        if response.get("type") == "property":
            print(f"Violation detected at {response['timestamp']}")
            print(f"Reason: {response['reason']}")
            break

    client.end_stream()
```

---

## Installation

### Prerequisites

1. **Build the Aletheia binary** (required):
   ```bash
   cd /path/to/aletheia
   cabal run shake -- build
   ```

2. **Install Python package** (development mode):
   ```bash
   cd python
   pip install -e ".[dev]"
   ```

### Verify Installation

```python
from aletheia.streaming_client import get_binary_path

try:
    binary = get_binary_path()
    print(f"Aletheia binary found at: {binary}")
except FileNotFoundError as e:
    print(f"Error: {e}")
```

---

## StreamingClient (Primary API)

**Use Case**: Incremental LTL checking over large CAN traces.

### Class: `StreamingClient`

Provides JSON streaming interface for real-time CAN frame analysis.

**Protocol Flow**:
```
1. parse_dbc()      → Load signal definitions
2. set_properties() → Define LTL properties to check
3. start_stream()   → Begin streaming mode
4. send_frame()     → Process frames one at a time
   ↳ Returns ack or violation
5. end_stream()     → Finish and get final results
```

### Constructor

```python
client = StreamingClient()
```

Creates a client (subprocess starts when used as context manager).

### Context Manager

```python
with StreamingClient() as client:
    # Subprocess runs during this block
    client.parse_dbc(...)
    client.send_frame(...)
```

**Automatic cleanup**: Subprocess is terminated when exiting the `with` block.

---

### Methods

#### `parse_dbc(dbc_json: Dict) → Dict`

Load DBC structure from JSON dictionary.

**Parameters**:
- `dbc_json`: DBC structure as Python dictionary

**Returns**:
```python
{"status": "success", "message": "DBC parsed successfully"}
```

**Example**:
```python
dbc = {
    "version": "1.0",
    "messages": [
        {
            "id": 256,
            "name": "SpeedMessage",
            "dlc": 8,
            "extended": False,
            "sender": "ECU",
            "signals": [
                {
                    "name": "Speed",
                    "startBit": 0,
                    "length": 16,
                    "byteOrder": "little_endian",
                    "signed": False,
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

response = client.parse_dbc(dbc)
assert response["status"] == "success"
```

**Converting .dbc Files**:

Use `cantools` to convert `.dbc` files to JSON:

```python
import cantools
import json

# Load .dbc file
db = cantools.database.load_file("vehicle.dbc")

# Convert to Aletheia JSON format
dbc_json = {
    "version": "1.0",
    "messages": [
        {
            "id": msg.frame_id,
            "name": msg.name,
            "dlc": len(msg.signals[0].byte_order) if msg.signals else 8,
            "extended": msg.is_extended_frame,
            "sender": msg.senders[0] if msg.senders else "Unknown",
            "signals": [
                {
                    "name": sig.name,
                    "startBit": sig.start,
                    "length": sig.length,
                    "byteOrder": "little_endian" if sig.byte_order == "little_endian" else "big_endian",
                    "signed": sig.is_signed,
                    "factor": sig.scale,
                    "offset": sig.offset,
                    "minimum": sig.minimum if sig.minimum is not None else 0.0,
                    "maximum": sig.maximum if sig.maximum is not None else 0.0,
                    "unit": sig.unit or "",
                    "presence": "always"
                }
                for sig in msg.signals
            ]
        }
        for msg in db.messages
    ]
}
```

---

#### `set_properties(properties: List[Dict]) → Dict`

Define LTL properties to check against the trace.

**Parameters**:
- `properties`: List of LTL property definitions (JSON objects)

**Returns**:
```python
{"status": "success", "message": "Properties set successfully"}
```

**Example**:
```python
properties = [
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

response = client.set_properties(properties)
assert response["status"] == "success"
```

See [LTL Property Format](#ltl-property-format) for complete specification.

---

#### `start_stream() → Dict`

Begin streaming mode for processing data frames.

**Returns**:
```python
{"status": "success", "message": "Streaming started"}
```

**Example**:
```python
response = client.start_stream()
assert response["status"] == "success"
```

---

#### `send_frame(timestamp: int, can_id: int, data: List[int]) → Dict`

Send a CAN frame for incremental checking.

**Parameters**:
- `timestamp`: Frame timestamp in microseconds (integer)
- `can_id`: CAN message ID (0-2047 for standard, 0-536870911 for extended)
- `data`: 8-byte payload as list of integers `[0-255]`

**Returns** (Acknowledged):
```python
{"status": "ack"}
```

**Returns** (Violation):
```python
{
    "type": "property",
    "status": "violation",
    "property_index": {"numerator": 0, "denominator": 1},
    "timestamp": {"numerator": 1000, "denominator": 1},
    "reason": "Always violated"
}
```

**Example**:
```python
# Frame at timestamp 1000µs with speed = 100 km/h
# Raw value: 1000 (100 km/h / 0.1 factor)
# Little-endian: 0x03E8 → [0xE8, 0x03, 0, 0, 0, 0, 0, 0]
response = client.send_frame(
    timestamp=1000,
    can_id=256,
    data=[0xE8, 0x03, 0, 0, 0, 0, 0, 0]
)

if response.get("type") == "property":
    print(f"Property violation detected!")
    print(f"  Property index: {response['property_index']}")
    print(f"  Timestamp: {response['timestamp']}")
    print(f"  Reason: {response['reason']}")
else:
    print("Frame processed successfully")
```

**Error Handling**:
```python
try:
    response = client.send_frame(timestamp, can_id, data)
except ValueError as e:
    print(f"Invalid frame: {e}")
except RuntimeError as e:
    print(f"Communication error: {e}")
```

---

#### `end_stream() → Dict`

End streaming mode and return final results.

**Returns**:
```python
{"status": "complete"}
```

**Example**:
```python
response = client.end_stream()
assert response["status"] == "complete"
```

---

## LTL Property Format

### Signal Predicates (Atomic)

#### `equals`

Signal equals a specific value.

```python
{
    "predicate": "equals",
    "signal": "Speed",
    "value": 100
}
```

#### `lessThan`

Signal is less than a value.

```python
{
    "predicate": "lessThan",
    "signal": "Speed",
    "value": 250
}
```

#### `greaterThan`

Signal is greater than a value.

```python
{
    "predicate": "greaterThan",
    "signal": "RPM",
    "value": 0
}
```

#### `between`

Signal is between two values (inclusive).

```python
{
    "predicate": "between",
    "signal": "Temperature",
    "min": 60,
    "max": 90
}
```

#### `changedBy`

Signal changed by more than a threshold from previous frame.

```python
{
    "predicate": "changedBy",
    "signal": "Speed",
    "delta": 10
}
```

---

### Temporal Operators

#### `atomic`

Wraps a signal predicate (required for all predicates).

```python
{
    "operator": "atomic",
    "predicate": {
        "predicate": "lessThan",
        "signal": "Speed",
        "value": 250
    }
}
```

#### `always` (Globally)

Property must hold for all frames in the trace.

```python
{
    "operator": "always",
    "formula": {...}
}
```

#### `eventually` (Finally)

Property must hold at some point in the trace.

```python
{
    "operator": "eventually",
    "formula": {...}
}
```

#### `next`

Property must hold in the next frame.

```python
{
    "operator": "next",
    "formula": {...}
}
```

#### `until`

Left formula must hold until right formula becomes true.

```python
{
    "operator": "until",
    "left": {...},
    "right": {...}
}
```

#### `and`

Both formulas must hold.

```python
{
    "operator": "and",
    "left": {...},
    "right": {...}
}
```

#### `or`

At least one formula must hold.

```python
{
    "operator": "or",
    "left": {...},
    "right": {...}
}
```

#### `not`

Formula must not hold.

```python
{
    "operator": "not",
    "formula": {...}
}
```

---

## Complete Examples

### Example 1: Speed Limit Checking

Check that vehicle speed never exceeds 250 km/h.

```python
from aletheia.streaming_client import StreamingClient

# DBC with speed signal
dbc = {
    "version": "1.0",
    "messages": [{
        "id": 256,
        "name": "SpeedMessage",
        "dlc": 8,
        "extended": False,
        "sender": "ECU",
        "signals": [{
            "name": "Speed",
            "startBit": 0,
            "length": 16,
            "byteOrder": "little_endian",
            "signed": False,
            "factor": 0.1,  # Scale factor: raw * 0.1 = km/h
            "offset": 0.0,
            "minimum": 0.0,
            "maximum": 300.0,
            "unit": "km/h",
            "presence": "always"
        }]
    }]
}

# Property: "Speed < 250"
property = {
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

# Simulate CAN trace
frames = [
    (100, 256, [0xE8, 0x03, 0, 0, 0, 0, 0, 0]),  # 1000 * 0.1 = 100 km/h
    (200, 256, [0xD0, 0x07, 0, 0, 0, 0, 0, 0]),  # 2000 * 0.1 = 200 km/h
    (300, 256, [0x28, 0x0A, 0, 0, 0, 0, 0, 0]),  # 2600 * 0.1 = 260 km/h (VIOLATION!)
]

# Check property
with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property])
    client.start_stream()

    for timestamp, can_id, data in frames:
        response = client.send_frame(timestamp, can_id, data)

        if response.get("type") == "property":
            print(f"⚠️  Property violation at {timestamp}µs")
            print(f"   Reason: {response['reason']}")
            print(f"   Frame data: {data}")
            break
        else:
            print(f"✓ Frame at {timestamp}µs: OK")

    client.end_stream()
```

**Output**:
```
✓ Frame at 100µs: OK
✓ Frame at 200µs: OK
⚠️  Property violation at 300µs
   Reason: Always violated
   Frame data: [40, 10, 0, 0, 0, 0, 0, 0]
```

---

### Example 2: Multiple Properties

Check multiple properties simultaneously.

```python
properties = [
    # Property 1: Speed always < 250
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
    },
    # Property 2: Speed always >= 0
    {
        "operator": "always",
        "formula": {
            "operator": "atomic",
            "predicate": {
                "predicate": "greaterThan",
                "signal": "Speed",
                "value": 0
            }
        }
    }
]

with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties(properties)
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            prop_idx = response["property_index"]["numerator"]
            print(f"Property {prop_idx} violated at {response['timestamp']}")

    client.end_stream()
```

---

### Example 3: Reading CAN Trace from File

Process a CAN trace from a CSV file.

```python
import csv
from aletheia.streaming_client import StreamingClient

def parse_can_csv(filename):
    """Parse CAN trace from CSV: timestamp,id,data0,data1,...,data7"""
    frames = []
    with open(filename) as f:
        reader = csv.reader(f)
        next(reader)  # Skip header
        for row in reader:
            timestamp = int(row[0])
            can_id = int(row[1], 16) if row[1].startswith('0x') else int(row[1])
            data = [int(row[i], 16) if row[i].startswith('0x') else int(row[i]) for i in range(2, 10)]
            frames.append((timestamp, can_id, data))
    return frames

# Load trace
frames = parse_can_csv("trace.csv")

# Check property
with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property])
    client.start_stream()

    violations = []
    for timestamp, can_id, data in frames:
        response = client.send_frame(timestamp, can_id, data)

        if response.get("type") == "property":
            violations.append({
                "timestamp": response["timestamp"],
                "property": response["property_index"]["numerator"],
                "reason": response["reason"]
            })

    client.end_stream()

    # Report violations
    if violations:
        print(f"Found {len(violations)} violations:")
        for v in violations:
            print(f"  - Property {v['property']} at {v['timestamp']}µs: {v['reason']}")
    else:
        print("✓ All properties satisfied")
```

---

## Error Handling

### Common Errors

**Binary Not Found**:
```python
from aletheia.streaming_client import StreamingClient, get_binary_path

try:
    binary = get_binary_path()
except FileNotFoundError as e:
    print(f"Error: {e}")
    print("Build the binary with: cabal run shake -- build")
```

**Invalid Frame Data**:
```python
try:
    response = client.send_frame(1000, 256, [0xFF, 0xFF])  # Only 2 bytes!
except ValueError as e:
    print(f"Error: {e}")  # "Data must be exactly 8 bytes, got 2"
```

**Protocol Error**:
```python
try:
    response = client.send_frame(1000, 256, [0] * 8)
except RuntimeError as e:
    print(f"Communication error: {e}")
```

**Signal Not Found**:
```python
response = client.set_properties([{
    "operator": "always",
    "formula": {
        "operator": "atomic",
        "predicate": {
            "predicate": "lessThan",
            "signal": "InvalidSignal",  # Doesn't exist in DBC
            "value": 100
        }
    }
}])

if response.get("status") == "error":
    print(f"Error: {response['message']}")
```

---

## Performance Tips

### Large Traces

For traces with millions of frames:

1. **Use StreamingClient** (not batch processing)
2. **Process incrementally** (don't load full trace into memory)
3. **Early termination**: Stop on first violation if appropriate

```python
with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property])
    client.start_stream()

    for frame in read_trace_incrementally("huge_trace.log"):
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            print(f"First violation at {response['timestamp']}")
            break  # Early termination

    client.end_stream()
```

### Throughput

Current performance (Phase 2B.1):
- **Target**: 100K frames/sec
- **Phase 3 goal**: 1M frames/sec with optimizations

---

## See Also

- [PROTOCOL.md](../architecture/PROTOCOL.md) - Complete JSON protocol specification
- [DESIGN.md](../architecture/DESIGN.md) - System architecture
- [BUILDING.md](BUILDING.md) - Build instructions

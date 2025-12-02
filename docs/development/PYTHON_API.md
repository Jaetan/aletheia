# Aletheia Python DSL Guide

**Purpose**: Complete guide to using Aletheia's Python DSL for CAN frame analysis and LTL verification.
**Version**: 0.1.0 (Phase 2B.1)
**Last Updated**: 2025-12-02

---

## Quick Start

```python
from aletheia import StreamingClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC file (converts .dbc to JSON automatically)
dbc_json = dbc_to_json("vehicle.dbc")

# Define property using fluent DSL: "Speed must always be less than 250 km/h"
property = Signal("Speed").less_than(250).always()

# Check CAN frames against property
with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in can_trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            print(f"⚠️  Violation at {response['timestamp']}: {response['reason']}")
            break

    client.end_stream()
```

---

## Python DSL Reference

### Signal Predicates

The `Signal` class provides fluent methods for building atomic predicates.

#### Basic Comparisons

```python
from aletheia import Signal

# Equality
Signal("Gear").equals(0)                    # Gear is in park (0)

# Relational operators
Signal("Speed").less_than(220)              # Speed < 220 km/h
Signal("Speed").greater_than(0)             # Speed > 0
Signal("Speed").less_than_or_equal(200)     # Speed ≤ 200
Signal("Speed").greater_than_or_equal(60)   # Speed ≥ 60

# Range checking
Signal("BatteryVoltage").between(11.5, 14.5)  # 11.5 ≤ voltage ≤ 14.5
```

#### Change Detection

```python
# Signal changed by at least delta (absolute value)
Signal("Speed").changed_by(-10)  # Speed decreased by 10+ km/h
Signal("RPM").changed_by(500)    # RPM increased or decreased by 500+
```

**Note**: `changed_by` checks `|value_now - value_prev| ≥ |delta|`

---

### Temporal Operators

Build LTL formulas by chaining temporal operators on predicates.

#### Always (Globally)

Property must hold for all frames in the trace.

```python
# Speed must always stay below 220 km/h
Signal("Speed").less_than(220).always()

# Gear must always be between 0 and 6
Signal("Gear").between(0, 6).always()
```

#### Eventually (Finally)

Property must hold at some point in the trace.

```python
# Engine must eventually reach operating temperature
Signal("EngineTemp").greater_than(90).eventually()

# Door must eventually close
Signal("DoorClosed").equals(1).eventually()
```

#### Never

Property must never hold (always negated).

```python
# Error code must never be 0xFF
Signal("ErrorCode").equals(0xFF).never()

# Speed must never exceed 300 km/h
Signal("Speed").greater_than(300).never()
```

#### Bounded Temporal Operators

```python
# Must hold within time_ms milliseconds
brake_pressed.within(100)

# Must hold continuously for at least time_ms milliseconds
Signal("DoorClosed").equals(1).for_at_least(50)  # Debounced door sensor
```

---

### Logical Composition

Combine predicates and properties using logical operators.

#### Predicate Composition

```python
# Both conditions must hold
left_ok = Signal("LeftBrake").equals(1)
right_ok = Signal("RightBrake").equals(1)
both_brakes = left_ok.and_(right_ok).always()

# At least one condition must hold
error1 = Signal("Error1").equals(1)
error2 = Signal("Error2").equals(1)
any_error = error1.or_(error2).never()

# Negation
enabled = Signal("Enabled").equals(1).not_()
```

#### Property Composition

```python
# AND: both properties must hold
speed_ok = Signal("Speed").less_than(220).always()
voltage_ok = Signal("Voltage").between(11, 14).always()
all_ok = speed_ok.and_(voltage_ok)

# OR: at least one property must hold
charging = Signal("Charging").equals(1).always()
engine_running = Signal("EngineRPM").greater_than(0).always()
powered = charging.or_(engine_running)
```

#### Implication

```python
# If brake pressed, then speed must decrease within 100ms
brake_pressed = Signal("BrakePedal").greater_than(0)
speed_decreasing = Signal("Speed").changed_by(-5)

brake_pressed.implies(speed_decreasing.within(100))
```

#### Until

```python
# Power mode transition: Start button never active until ACC mode
power_off = Signal("PowerMode").equals(0)
power_acc = Signal("PowerMode").equals(2)
power_start = Signal("StartButton").equals(1)

power_off.implies(
    power_start.never().until(power_acc)
)
```

---

## Complete Examples

### Example 1: Speed Limit Checking

```python
from aletheia import StreamingClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC
dbc = dbc_to_json("vehicle.dbc")

# Property: Speed must always stay below 250 km/h
property = Signal("Speed").less_than(250).always()

# Check CAN trace
with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for timestamp, can_id, data in frames:
        response = client.send_frame(timestamp, can_id, data)

        if response.get("type") == "property":
            print(f"⚠️  Speed limit exceeded at {timestamp}µs")
            print(f"   Reason: {response['reason']}")
            break
        else:
            print(f"✓ Frame at {timestamp}µs: OK")

    client.end_stream()
```

---

### Example 2: Multiple Properties

```python
properties = [
    # P1: Speed always in valid range
    Signal("Speed").between(0, 300).always(),

    # P2: Voltage always stable
    Signal("BatteryVoltage").between(11.5, 14.5).always(),

    # P3: No critical errors
    Signal("CriticalError").equals(1).never(),

    # P4: Engine eventually reaches operating temp
    Signal("EngineTemp").greater_than(90).eventually()
]

with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([p.to_dict() for p in properties])
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            prop_idx = response["property_index"]["numerator"]
            print(f"Property {prop_idx} violated at {response['timestamp']}")

    client.end_stream()
```

---

### Example 3: Brake Safety Property

```python
# Safety property: If brake pedal pressed, speed must decrease within 100ms

brake_pressed = Signal("BrakePedal").greater_than(0)
speed_decreasing = Signal("Speed").changed_by(-5)  # Decreased by at least 5 km/h

property = brake_pressed.implies(speed_decreasing.within(100))

with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    violations = []
    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            violations.append({
                "timestamp": response["timestamp"],
                "reason": response["reason"]
            })

    client.end_stream()

    if violations:
        print(f"⚠️  Brake safety violations: {len(violations)}")
        for v in violations:
            print(f"   - {v['timestamp']}µs: {v['reason']}")
    else:
        print("✓ Brake safety property satisfied")
```

---

### Example 4: Power Mode State Machine

```python
# Property: From power-off, start button can't activate until ACC mode reached

power_off = Signal("PowerMode").equals(0)
power_acc = Signal("PowerMode").equals(2)
power_start = Signal("StartButton").equals(1)

property = power_off.implies(
    power_start.never().until(power_acc)
)

with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            print("⚠️  Invalid power mode transition detected")
            print(f"   Timestamp: {response['timestamp']}")
            print(f"   Reason: {response['reason']}")
            break

    client.end_stream()
```

---

## StreamingClient API

### Context Manager

```python
with StreamingClient() as client:
    # Subprocess runs during this block
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)
        # Process response...

    client.end_stream()
# Subprocess automatically cleaned up
```

### Methods

#### `parse_dbc(dbc_json: Dict) → Dict`

Load DBC structure from JSON dictionary.

```python
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("vehicle.dbc")  # Convert .dbc file to JSON
response = client.parse_dbc(dbc)
assert response["status"] == "success"
```

#### `set_properties(properties: List[Dict]) → Dict`

Set LTL properties to check (use `.to_dict()` on DSL properties).

```python
properties = [
    Signal("Speed").less_than(250).always(),
    Signal("Voltage").between(11, 14).always()
]

response = client.set_properties([p.to_dict() for p in properties])
assert response["status"] == "success"
```

#### `start_stream() → Dict`

Begin streaming mode.

```python
response = client.start_stream()
assert response["status"] == "success"
```

#### `send_frame(timestamp: int, can_id: int, data: List[int]) → Dict`

Send a CAN frame for incremental checking.

**Parameters**:
- `timestamp`: Microseconds (integer)
- `can_id`: 0-2047 (standard) or 0-536870911 (extended)
- `data`: 8-byte payload `[0-255]`

**Returns** (acknowledged):
```python
{"status": "ack"}
```

**Returns** (violation):
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
response = client.send_frame(
    timestamp=1000,
    can_id=256,
    data=[0xE8, 0x03, 0, 0, 0, 0, 0, 0]
)

if response.get("type") == "property":
    print(f"Violation: {response['reason']}")
```

#### `end_stream() → Dict`

End streaming and get final results.

```python
response = client.end_stream()
assert response["status"] == "complete"
```

---

## Converting .dbc Files

Use `cantools` to convert `.dbc` files:

```bash
pip install cantools
```

```python
from aletheia.dbc_converter import dbc_to_json

# Convert .dbc file to Aletheia JSON format
dbc_json = dbc_to_json("vehicle.dbc")
```

**Manual conversion** (if dbc_converter unavailable):

```python
import cantools
import json

db = cantools.database.load_file("vehicle.dbc")

dbc_json = {
    "version": "1.0",
    "messages": [
        {
            "id": msg.frame_id,
            "name": msg.name,
            "dlc": 8,
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

## Error Handling

### Binary Not Found

```python
from aletheia.streaming_client import get_binary_path

try:
    binary = get_binary_path()
except FileNotFoundError as e:
    print(f"Error: {e}")
    print("Build the binary with: cabal run shake -- build")
```

### Invalid Frame Data

```python
try:
    response = client.send_frame(1000, 256, [0xFF, 0xFF])  # Only 2 bytes!
except ValueError as e:
    print(f"Error: {e}")  # "Data must be exactly 8 bytes, got 2"
```

### Signal Not Found

```python
property = Signal("InvalidSignal").less_than(100).always()

response = client.set_properties([property.to_dict()])

if response.get("status") == "error":
    print(f"Error: {response['message']}")
```

---

## Performance Tips

### Large Traces

For traces with millions of frames:

1. **Use StreamingClient** (incremental processing)
2. **Don't load full trace into memory**
3. **Early termination** on first violation

```python
with StreamingClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in read_trace_incrementally("huge_trace.log"):
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("type") == "property":
            print(f"First violation at {response['timestamp']}")
            break  # Early termination

    client.end_stream()
```

### Current Performance

- **Phase 2B**: 100K frames/sec target
- **Phase 3 goal**: 1M frames/sec with optimizations

---

## DSL Class Reference

### Signal

```python
class Signal:
    def __init__(self, name: str)

    # Comparisons
    def equals(self, value: float) -> Predicate
    def less_than(self, value: float) -> Predicate
    def greater_than(self, value: float) -> Predicate
    def less_than_or_equal(self, value: float) -> Predicate
    def greater_than_or_equal(self, value: float) -> Predicate
    def between(self, min_val: float, max_val: float) -> Predicate

    # Change detection
    def changed_by(self, delta: float) -> Predicate
```

### Predicate

```python
class Predicate:
    # Temporal operators
    def always(self) -> Property
    def eventually(self) -> Property
    def never(self) -> Property
    def within(self, time_ms: int) -> Property
    def for_at_least(self, time_ms: int) -> Property

    # Logical operators
    def and_(self, other: Predicate) -> Predicate
    def or_(self, other: Predicate) -> Predicate
    def not_(self) -> Predicate
    def implies(self, other: Union[Property, Predicate]) -> Property
```

### Property

```python
class Property:
    # Logical operators
    def and_(self, other: Property) -> Property
    def or_(self, other: Property) -> Property
    def implies(self, other: Union[Property, Predicate]) -> Property
    def until(self, other: Property) -> Property

    # Serialization
    def to_dict(self) -> Dict[str, Any]
```

---

## See Also

- [PROTOCOL.md](../architecture/PROTOCOL.md) - JSON protocol specification
- [DESIGN.md](../architecture/DESIGN.md) - System architecture
- [BUILDING.md](BUILDING.md) - Build instructions

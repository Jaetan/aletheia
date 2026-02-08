# Aletheia Python DSL Guide

**Purpose**: Reference for Aletheia's Python DSL (Signal, Predicate, Property) and AletheiaClient.
**Version**: 0.3.2
**Last Updated**: 2026-02-07

> **Higher-level interfaces**: If you don't need full LTL control, see the
> [Interface Guide](INTERFACES.md) for the Check API, YAML, and Excel loaders.

---

## Quick Start

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC file (converts .dbc to JSON automatically)
dbc_json = dbc_to_json("vehicle.dbc")

# Define property using fluent DSL: "Speed must always be less than 250 km/h"
property = Signal("Speed").less_than(250).always()

# Check CAN frames against property
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in can_trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("status") == "violation":
            ts = response['timestamp']['numerator']
            print(f"Violation at {ts}us")
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
Signal("Speed").less_than_or_equal(200)     # Speed <= 200
Signal("Speed").greater_than_or_equal(60)   # Speed >= 60

# Range checking
Signal("BatteryVoltage").between(11.5, 14.5)  # 11.5 <= voltage <= 14.5
```

#### Change Detection

```python
# Signal changed by at least delta (absolute value)
Signal("Speed").changed_by(-10)  # Speed decreased by 10+ km/h
Signal("RPM").changed_by(500)    # RPM increased or decreased by 500+
```

**Note**: `changed_by` checks `|value_now - value_prev| >= |delta|`

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

#### Next Operator (Use with Caution)

The `Next` operator evaluates a formula at the next frame:

```python
# Next: property must hold at next frame
Signal("Speed").less_than(100).next()
```

**WARNING: Next is rarely appropriate for CAN analysis**

**Why Next is problematic:**

1. **Timing Uncertainty**: CAN frames don't arrive at fixed intervals
   - Variable network load and ECU processing jitter (1-10ms typical)
   - Priority-based arbitration introduces delays
   - "Next frame" is ambiguous (next from same ECU? any ECU?)

2. **Brittle Properties**: Next-based properties are fragile
   - Break with minor timing changes
   - False positives from normal jitter
   - Don't capture intended temporal semantics

3. **Non-deterministic Ordering**:
   - What if a frame is missed or dropped?
   - Retransmissions complicate frame ordering
   - Multi-ECU systems have unpredictable interleaving

**Recommended Alternatives:**

| Use Case | Instead of Next | Use This |
|----------|----------------|----------|
| Time-bounded response | `brake.next()` | `brake.within(100)` - Within 100ms |
| State transition timing | `state_a.next()` | `state_a.metric_until(100, state_b)` |
| Sequence verification | `a.next()` then `b.next()` | `a.until(b)` - a holds until b |
| Eventual occurrence | `signal.next()` | `signal.eventually()` |

**When Next might be acceptable:**
- Analyzing synthetic traces with fixed timesteps (testing only)
- Frame-by-frame debugging (not production verification)
- Comparing against LTL textbook examples (educational)

**Bottom line:** Always prefer metric operators (`.within()`, `.metric_until()`) over Next for real CAN traces.

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

### Advanced Temporal Operators

#### Release Operator

The Release operator is the dual of Until: `phi R psi` means psi holds until phi releases it (or forever if phi never holds).

```python
# Brake must stay engaged until ignition turns on
ignition_on = Signal("Ignition").equals(1).eventually()
brake_engaged = Signal("Brake").equals(1).always()
property = ignition_on.release(brake_engaged)
```

**Semantics**: The right-hand side (brake_engaged) must remain true until the left-hand side (ignition_on) becomes true and "releases" the obligation. If the left side never holds, the right side must hold forever.

#### Metric Until

Time-bounded Until: `phi U_{<=t} psi` means phi holds until psi becomes true within t milliseconds.

```python
# Speed must stay above 50 until brake pressed (within 1 second)
speed_ok = Signal("Speed").greater_than(50).always()
brake = Signal("Brake").equals(1).eventually()
property = speed_ok.metric_until(1000, brake)
```

**Use case**: State transitions with time constraints. The left property must hold continuously until the right property becomes true, and this must happen within the specified time bound.

#### Metric Release

Time-bounded Release: `phi R_{<=t} psi` means psi holds until phi releases it within t milliseconds.

```python
# Safety: Brake engaged until ignition on (within 5 seconds)
ignition = Signal("Ignition").equals(1).eventually()
brake = Signal("Brake").equals(1).always()
property = ignition.metric_release(5000, brake)
```

**Use case**: Safety properties with maximum delay constraints. The right property must hold until the left property releases it, with a maximum time bound.

---

## Complete Examples

### Example 1: Speed Limit Checking

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC
dbc = dbc_to_json("vehicle.dbc")

# Property: Speed must always stay below 250 km/h
property = Signal("Speed").less_than(250).always()

# Check CAN trace
with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for timestamp, can_id, data in frames:
        response = client.send_frame(timestamp, can_id, data)

        if response.get("status") == "violation":
            ts = response['timestamp']['numerator']
            print(f"Speed limit exceeded at {ts}us")
            break

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

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([p.to_dict() for p in properties])
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("status") == "violation":
            prop_idx = response["property_index"]["numerator"]
            ts = response["timestamp"]["numerator"]
            print(f"Property {prop_idx} violated at {ts}us")

    client.end_stream()
```

---

### Example 3: Brake Safety Property

```python
# Safety property: If brake pedal pressed, speed must decrease within 100ms

brake_pressed = Signal("BrakePedal").greater_than(0)
speed_decreasing = Signal("Speed").changed_by(-5)  # Decreased by at least 5 km/h

property = brake_pressed.implies(speed_decreasing.within(100))

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    violations = []
    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("status") == "violation":
            violations.append(response["timestamp"]["numerator"])

    client.end_stream()

    if violations:
        print(f"Brake safety violations: {len(violations)}")
        for ts in violations:
            print(f"   - {ts}us")
    else:
        print("Brake safety property satisfied")
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

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("status") == "violation":
            ts = response['timestamp']['numerator']
            print(f"Invalid power mode transition at {ts}us")
            break

    client.end_stream()
```

---

## AletheiaClient API

`AletheiaClient` is the unified client for streaming LTL checking and signal operations. It loads `libaletheia-ffi.so` via ctypes and calls the Agda/Haskell core directly via FFI.

### Context Manager

```python
with AletheiaClient() as client:
    # Shared library loaded, GHC RTS initialized
    client.parse_dbc(dbc_json)

    # Signal operations work anytime after DBC loaded
    result = client.extract_signals(can_id=0x100, data=frame_bytes)

    # Streaming LTL checking
    client.set_properties([property.to_dict()])
    client.start_stream()
    for frame in trace:
        response = client.send_frame(frame.timestamp, frame.id, frame.data)
    client.end_stream()
# State freed, RTS reference released
```

### Methods

#### `parse_dbc(dbc_json: Dict) -> Dict`

Load DBC structure from JSON dictionary. Must be called first.

```python
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("vehicle.dbc")  # Convert .dbc file to JSON
response = client.parse_dbc(dbc)
assert response["status"] == "success"
```

#### `set_properties(properties: List[Dict]) -> Dict`

Set LTL properties to check (use `.to_dict()` on DSL properties).

```python
properties = [
    Signal("Speed").less_than(250).always(),
    Signal("Voltage").between(11, 14).always()
]

response = client.set_properties([p.to_dict() for p in properties])
assert response["status"] == "success"
```

#### `start_stream() -> Dict`

Begin streaming mode for LTL checking.

```python
response = client.start_stream()
assert response["status"] == "success"
```

#### `send_frame(timestamp: int, can_id: int, data: List[int]) -> Dict`

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
    "reason": "Always violated"   # optional, may be absent
}
```

**Note**: `property_index` and `timestamp` are rational numbers (Agda `ℚ`). Access the integer value via `["numerator"]` — the denominator is always 1.

#### `end_stream() -> Dict`

End streaming and get final results.

```python
response = client.end_stream()
assert response["status"] == "complete"
```

---

## Signal Operations

Signal operations work anytime after DBC is loaded - both inside and outside streaming mode.

#### `extract_signals(can_id: int, data: List[int]) -> SignalExtractionResult`

Extract all signals from a CAN frame.

```python
result = client.extract_signals(can_id=0x100, data=[0x20, 0x1C, 0, 0, 0, 0, 0, 0])
speed = result.get("VehicleSpeed", default=0.0)
print(f"Speed: {speed} kph")

# Check for errors
if result.has_errors():
    print(f"Errors: {result.errors}")

# Check absent signals (multiplexed signals not present in this frame)
print(f"Absent: {result.absent}")
```

#### `update_frame(can_id: int, frame: List[int], signals: Dict[str, float]) -> List[int]`

Update specific signals in an existing frame. Returns a new frame (immutable).

```python
original = [0x20, 0x1C, 0, 0, 0, 0, 0, 0]
modified = client.update_frame(
    can_id=0x100,
    frame=original,
    signals={"VehicleSpeed": 130.0}
)
# original unchanged, modified has new speed value
```

#### `build_frame(can_id: int, signals: Dict[str, float]) -> List[int]`

Build a CAN frame from signal values (starts with zero-filled frame).

```python
frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})
# Returns 8-byte frame with VehicleSpeed encoded
```

---

## Converting .dbc Files

`cantools` is installed automatically as a dependency:

```python
from aletheia.dbc_converter import dbc_to_json

# Convert .dbc file to Aletheia JSON format
dbc_json = dbc_to_json("vehicle.dbc")
```

---

## Error Handling

### Shared Library Not Found

```python
# AletheiaClient auto-discovers libaletheia-ffi.so.
# If not found, it raises FileNotFoundError:
try:
    with AletheiaClient() as client:
        pass
except FileNotFoundError as e:
    print(f"Error: {e}")
    print("Build with: cabal run shake -- build")
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

1. **Use AletheiaClient** (incremental processing)
2. **Don't load full trace into memory**
3. **Early termination** on first violation

```python
with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for frame in read_trace_incrementally("huge_trace.log"):
        response = client.send_frame(frame.timestamp, frame.id, frame.data)

        if response.get("status") == "violation":
            ts = response['timestamp']['numerator']
            print(f"First violation at {ts}us")
            break  # Early termination

    client.end_stream()
```

### Current Performance

- **Streaming LTL (3 properties)**: 9,229 fps (108 us/frame)
- **Signal Extraction**: 8,184 fps
- **Frame Building**: 5,868 fps

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
    def always(self) -> Property        # G(p)
    def eventually(self) -> Property    # F(p)
    def never(self) -> Property         # G(not p)
    def next(self) -> Property          # X(p) — rarely useful, see warning above
    def within(self, time_ms: int) -> Property       # F_{<=t}(p)
    def for_at_least(self, time_ms: int) -> Property  # G_{<=t}(p)

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
    def not_(self) -> Property
    def implies(self, other: Union[Property, Predicate]) -> Property

    # Temporal operators (for nesting: G(F(p)), F(G(p)), etc.)
    def always(self) -> Property
    def eventually(self) -> Property
    def next(self) -> Property  # For nested formulas - see Next Operator warning
    def until(self, other: Property) -> Property
    def release(self, other: Property) -> Property
    def metric_until(self, time_ms: int, other: Property) -> Property
    def metric_release(self, time_ms: int, other: Property) -> Property

    # Serialization
    def to_dict(self) -> LTLFormula
```

---

## See Also

- **[Interface Guide](INTERFACES.md)** - Check API, YAML loader, Excel loader (higher-level interfaces)
- [PROTOCOL.md](../architecture/PROTOCOL.md) - JSON protocol specification
- [DESIGN.md](../architecture/DESIGN.md) - System architecture
- [BUILDING.md](BUILDING.md) - Build instructions

# Aletheia Python API Guide

**Purpose**: Reference for Aletheia's Python API — the raw DSL (Signal, Predicate, Property) and `AletheiaClient`. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

> **Higher-level interfaces**: If you don't need full LTL control, see the
> [Interface Guide](INTERFACES.md) for the Check API, YAML, and Excel loaders.
> **CLI**: See the [CLI Reference](CLI.md) for command-line usage.
> **Other bindings**: This guide documents the Python binding. C++ and Go ship
> the same verified core with equivalent APIs — see `cpp/include/aletheia/*.hpp`
> for C++ (especially `check.hpp`, `client.hpp`, `ltl.hpp`) and
> `go doc github.com/aletheia-automotive/aletheia-go/aletheia` for Go. The
> [Interface Guide § Binding parity](INTERFACES.md#binding-parity) summarizes
> feature availability per binding.

---

## Quick Start

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from aletheia.can_log import iter_can_log   # `pip install aletheia[can]`

# Load DBC file (converts .dbc to JSON automatically)
dbc_json = dbc_to_json("vehicle.dbc")

# Define property using fluent DSL: "Speed must always be less than 250 km/h"
property = Signal("Speed").less_than(250).always()

# `data` must be a `bytes` / `bytearray` of the correct length for the DLC.
# Three common ways to produce it:
#   1. From a recorded trace file (.blf / .asc / .log / .mf4):
#        for ts, can_id, dlc, data in iter_can_log("drive.blf"):
#   2. From a hex string (useful for hand-written test cases):
#        ts, can_id, dlc, data = 0, 0x100, 8, bytes.fromhex("E803000000000000")
#   3. From a literal byte sequence:
#        ts, can_id, dlc, data = 0, 0x100, 8, bytes([0xE8, 0x03, 0, 0, 0, 0, 0, 0])

with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([property.to_dict()])
    client.start_stream()

    for ts, can_id, dlc, data in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, dlc, data)

        if response.get("status") == "fails":
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
# Directional change — sign of delta determines direction
Signal("Speed").changed_by(-10)  # Speed decreased by 10+ km/h
Signal("RPM").changed_by(500)    # RPM increased by 500+
```

**Note**: `changed_by` is directional: positive delta checks `curr - prev >= delta`, negative delta checks `curr - prev <= delta`.

#### Stability

```python
# Signal stayed within tolerance of previous value
Signal("Temperature").stable_within(2.0)  # Temperature stable within +/-2
```

**Note**: `stable_within` checks `|value_now - value_prev| <= tolerance`

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

#### Nested Temporal Helpers

Standalone helper functions for common nested LTL patterns. Importable directly from `aletheia`.

```python
from aletheia import infinitely_often, eventually_always, never
```

**`infinitely_often(formula)`** — G(F(phi)): property holds infinitely many times (liveness).

```python
# Speed exceeds 100 infinitely often (repeated acceleration)
infinitely_often(Signal("Speed").greater_than(100))

# Equivalent fluent form:
Signal("Speed").greater_than(100).eventually().always()
```

**`eventually_always(formula)`** — F(G(phi)): property eventually holds forever (stability).

```python
# Temperature eventually stabilizes below 70 degrees
eventually_always(Signal("Temperature").less_than(70))

# Equivalent fluent form:
Signal("Temperature").less_than(70).always().eventually()
```

**`never(formula)`** — G(not(phi)): property never holds (strongest safety).

```python
# Critical fault never occurs
never(Signal("FaultCode").equals(0xFF))

# Equivalent fluent form:
Signal("FaultCode").equals(0xFF).never()
```

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

    for timestamp, can_id, dlc, data in frames:
        response = client.send_frame(timestamp, can_id, dlc, data)

        if response.get("status") == "fails":
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

    for ts, can_id, dlc, data in trace:
        response = client.send_frame(ts, can_id, dlc, data)

        if response.get("status") == "fails":
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
    for ts, can_id, dlc, data in trace:
        response = client.send_frame(ts, can_id, dlc, data)

        if response.get("status") == "fails":
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

    for ts, can_id, dlc, data in trace:
        response = client.send_frame(ts, can_id, dlc, data)

        if response.get("status") == "fails":
            vts = response['timestamp']['numerator']
            print(f"Invalid power mode transition at {vts}us")
            break

    client.end_stream()
```

---

## AletheiaClient API

`AletheiaClient` is the unified client for streaming LTL checking and signal operations. It loads `libaletheia-ffi.so` via ctypes and calls the Agda/Haskell core directly via FFI.

### Constructor

```python
AletheiaClient(default_checks=None, rts_cores=1)
```

**Parameters**:
- `default_checks` (`list[CheckResult] | None`): Checks prepended to every `add_checks()` call. Useful for organization-wide safety baselines.
- `rts_cores` (`int`): Number of GHC RTS capabilities (default 1). Only relevant for advanced multi-bus scenarios.

### Context Manager

```python
with AletheiaClient(default_checks=safety_checks) as client:
    # Shared library loaded, GHC RTS initialized
    client.parse_dbc(dbc_json)

    # Signal operations work anytime after DBC loaded
    result = client.extract_signals(can_id=0x100, dlc=8, data=frame_bytes)

    # Streaming LTL checking
    client.add_checks(session_checks)  # merges defaults + session
    client.start_stream()
    for ts, can_id, dlc, data in trace:
        response = client.send_frame(ts, can_id, dlc, data)
    client.end_stream()
# State freed, RTS reference released
```

### Methods

#### `close() -> None`

Explicitly free state and release RTS reference. Called automatically when using the context manager (`with` block).

```python
# Preferred: context manager handles close() automatically
with AletheiaClient() as client:
    client.parse_dbc(dbc)
    # ... work ...
# close() called automatically on exit
```

#### `parse_dbc(dbc: DBCDefinition) -> SuccessResponse | ErrorResponse`

Load DBC structure from JSON dictionary. Must be called first.

```python
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("vehicle.dbc")  # Convert .dbc file to JSON
response = client.parse_dbc(dbc)
assert response["status"] == "success"
```

#### `validate_dbc(dbc: DBCDefinition) -> ValidationResponse`

Validate a DBC definition for structural issues (overlapping signals, zero-length signals, etc.). Can be called anytime — does not require `parse_dbc()` and does not modify client state.

```python
result = client.validate_dbc(dbc)
if result["has_errors"]:
    for issue in result["issues"]:
        print(f"[{issue['severity']}] {issue['code']}: {issue['detail']}")
```

**Returns**: `{"status": "validation", "has_errors": bool, "issues": [{"severity": str, "code": str, "detail": str}, ...]}`

#### `format_dbc() -> DBCDefinition`

Export the currently-loaded DBC as a JSON dict. Requires a prior `parse_dbc()` call.

```python
dbc_out = client.format_dbc()
# dbc_out matches the DBCDefinition schema
```

#### `add_checks(checks: list[CheckResult]) -> SuccessResponse | ErrorResponse`

Set LTL checks, merging with default checks from the constructor. Calls `set_properties()` which auto-derives enrichment diagnostics.

```python
from aletheia import Check

checks = [
    Check.signal("Speed").never_exceeds(220),
    Check.signal("Voltage").stays_between(11.5, 14.5),
]
response = client.add_checks(checks)
assert response["status"] == "success"
```

This is the preferred way to set checks when using the Check API or YAML/Excel loaders.

#### `set_properties(properties: list[LTLFormula]) -> SuccessResponse | ErrorResponse`

Set LTL properties to check (use `.to_dict()` on DSL properties).

```python
properties = [
    Signal("Speed").less_than(250).always(),
    Signal("Voltage").between(11, 14).always()
]

response = client.set_properties([p.to_dict() for p in properties])
assert response["status"] == "success"
```

#### `start_stream() -> SuccessResponse | ErrorResponse`

Begin streaming mode for LTL checking.

```python
response = client.start_stream()
assert response["status"] == "success"
```

#### `send_frame(timestamp: int, can_id: int, dlc: int, data: bytearray, *, extended: bool = False) -> AckResponse | PropertyViolationResponse | ErrorResponse`

Send a CAN frame for incremental checking.

**Parameters**:
- `timestamp`: Microseconds (integer)
- `can_id`: 0-2047 (standard) or 0-536870911 (extended)
- `dlc`: DLC code (0-8 for CAN 2.0B, 0-15 for CAN-FD)
- `data`: Payload as `bytearray` (must match `dlc_to_bytes(dlc)`; mismatch raises `ProcessError` client-side)
- `extended`: `True` for 29-bit extended CAN IDs (default `False`)

**Returns** (acknowledged):
```text
{"status": "ack"}
```

**Returns** (violation): A property response with `status`, `property_index`, `timestamp`, and `reason`. When checks are registered via `add_checks()`, violations are automatically enriched with signal values and formula descriptions. See [Enriched Violations](#enriched-violations) for the full response schema.

#### `send_frames(frames: list[CANFrameTuple]) -> list[AckResponse | PropertyViolationResponse]`

Send multiple CAN frames in a batch. Processing stops at the first error, raising `BatchError` with `partial_results` and `frame_index`.

```python continuation
from aletheia import CANFrameTuple

frames = [
    CANFrameTuple(1000, 0x100, 8, bytearray(b'\x20\x1C\x00\x00\x00\x00\x00\x00'), False),
    CANFrameTuple(2000, 0x100, 8, bytearray(b'\x40\x1C\x00\x00\x00\x00\x00\x00'), False),
]
responses = client.send_frames(frames)
violations = [r for r in responses if r["status"] == "fails"]
```

**Parameters**: List of `CANFrameTuple(timestamp, can_id, dlc, data, extended)`.
**Returns**: List of responses in same order as input frames.

#### `end_stream() -> CompleteResponse | ErrorResponse`

End streaming and get final results.

```python continuation
response = client.end_stream()
assert response["status"] == "complete"
```

---

## Signal Operations

Signal operations work anytime after DBC is loaded - both inside and outside streaming mode.

#### `extract_signals(can_id: int, dlc: int, data: bytearray, *, extended: bool = False) -> SignalExtractionResult`

Extract all signals from a CAN frame.

```python
result = client.extract_signals(can_id=0x100, dlc=8, data=bytearray([0x20, 0x1C, 0, 0, 0, 0, 0, 0]))
speed = result.get("VehicleSpeed", default=0.0)
print(f"Speed: {speed} kph")

# Check for errors
if result.has_errors():
    print(f"Errors: {result.errors}")

# Check absent signals (multiplexed signals not present in this frame)
print(f"Absent: {result.absent}")
```

#### `update_frame(can_id: int, dlc: int, frame: bytearray, signals: dict[str, float], *, extended: bool = False) -> bytearray`

Update specific signals in an existing frame. Returns a new frame (immutable).

```python
original = bytearray([0x20, 0x1C, 0, 0, 0, 0, 0, 0])
modified = client.update_frame(
    can_id=0x100,
    dlc=8,
    frame=original,
    signals={"VehicleSpeed": 130.0}
)
# original unchanged, modified has new speed value
```

#### `build_frame(can_id: int, dlc: int, signals: dict[str, float], *, extended: bool = False) -> bytearray`

Build a CAN frame from signal values (starts with zero-filled frame).

```python
frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 72.0})
# Returns frame with VehicleSpeed encoded
```

---

## Converting .dbc Files

`dbc_to_json` is a thin wrapper over the verified Agda DBC parser; no
third-party dependency is required.

```python
from aletheia.dbc_converter import dbc_to_json

# Convert .dbc file to Aletheia JSON format
dbc_json = dbc_to_json("vehicle.dbc")
```

#### `convert_dbc_file(dbc_path, output_path=None) -> str`

Convert a `.dbc` file to Aletheia JSON format and optionally write it to a file. Returns the JSON string.

```python
from aletheia.dbc_converter import convert_dbc_file

# Convert and write to file
convert_dbc_file("vehicle.dbc", "vehicle.json")

# Or just get the JSON string
json_str = convert_dbc_file("vehicle.dbc")
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
# Data length vs DLC mismatch is caught client-side before FFI call
try:
    client.send_frame(1000, 256, dlc=8, data=bytearray([0xFF, 0xFF]))  # Only 2 bytes, DLC expects 8
except ProcessError as e:
    print(f"Error: {e}")  # payload length 2 does not match DLC 8
```

### Signal Not Found

```python
from aletheia import ProtocolError

property = Signal("InvalidSignal").less_than(100).always()

try:
    client.set_properties([property.to_dict()])
except ProtocolError as e:
    print(f"Error: {e}")
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

    for ts, can_id, dlc, data in iter_can_log("huge_trace.log"):
        response = client.send_frame(ts, can_id, dlc, data)

        if response.get("status") == "fails":
            ts = response['timestamp']['numerator']
            print(f"First violation at {ts}us")
            break  # Early termination

    client.end_stream()
```

### Current Performance

See [BENCHMARKS.md](../development/BENCHMARKS.md) for the benchmark suite (cross-language runner + per-binding scripts) and [PROJECT_STATUS.md § Key Metrics](../../PROJECT_STATUS.md#key-metrics) for the canonical throughput numbers.

---

## DSL Class Reference

### Signal

```text
class Signal:
    def __init__(self, name: str)

    # Comparisons
    def equals(self, value: float) -> Predicate
    def less_than(self, value: float) -> Predicate
    def greater_than(self, value: float) -> Predicate
    def less_than_or_equal(self, value: float) -> Predicate
    def greater_than_or_equal(self, value: float) -> Predicate
    def between(self, min_val: float, max_val: float) -> Predicate

    # Change detection (directional)
    def changed_by(self, delta: float) -> Predicate

    # Stability (magnitude tolerance)
    def stable_within(self, tolerance: float) -> Predicate
```

### Predicate

```text
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

```text
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
<!-- Pseudo-signatures above are intentionally class-body-shape, not runnable Python;
     see CLAUDE.md § Doc-example harness. -->

---

## CAN Log Reader

Read industry-standard CAN log files directly into Aletheia.

### `load_can_log(path, **kwargs) -> list[CANFrameTuple]`

Load all CAN frames from a log file into memory.

```python
from aletheia.can_log import load_can_log

frames = load_can_log("drive.blf")
# frames is list[(timestamp_us, arbitration_id, dlc, data)]
```

### `iter_can_log(path, **kwargs) -> Iterator[CANFrameTuple]`

Lazily iterate CAN frames from a log file (O(1) memory).

```python
from aletheia.can_log import iter_can_log

for ts, can_id, dlc, data in iter_can_log("highway.asc"):
    response = client.send_frame(ts, can_id, dlc, data)
```

**Parameters** (both functions):
- `path`: Path to CAN log file (.asc, .blf, .csv, .db, .log, .mf4, .trc)
- `skip_error_frames`: Skip CAN error frames (default `True`)
- `skip_remote_frames`: Skip remote transmission requests (default `True`)
- `on_error`: `"skip"` (default) or `"raise"` for corrupt frames

**Supported formats**: `.asc`, `.blf`, `.csv`, `.db`, `.log`, `.mf4`, `.trc` (via python-can).

**Compressed files**: Gz-compressed log files (e.g., `.asc.gz`, `.blf.gz`) are supported transparently — the format is detected from the inner extension.

---

## Enriched Violations

When checks are registered via `set_properties()` (or `add_checks()`), violation responses from `send_frame()` are automatically enriched with signal data:

```python
{
    "type": "property",
    "status": "fails",
    "property_index": {"numerator": 0, "denominator": 1},
    "timestamp": {"numerator": 4523000, "denominator": 1},
    "reason": "Always violated",  # core_reason (raw Agda string)
    "enrichment": {
        "signals": {"VehicleSpeed": 225.5},                    # extracted signal values
        "formula_desc": "always(VehicleSpeed < 220)",           # formula description
        "enriched_reason": "VehicleSpeed = 225.5 (formula: always(VehicleSpeed < 220))",
        "core_reason": "Always violated"                        # original Agda reason
    }
}
```

Access the enriched fields via `response["enrichment"]["enriched_reason"]`, etc.
Without registered checks, only `property_index`, `timestamp`, and `reason` are present (no `enrichment` field).

---

## Structured Logging

The Python binding emits structured log records on the standard `logging.getLogger("aletheia")` logger — attach a handler to that name (or any ancestor) to capture them. No `WithLogger` constructor hook is needed; the binding simply follows Python's `logging` conventions.

Every record carries:

- `record.msg` — a short event name like `stream.started` or `cache.miss` (human-greppable).
- `record.event` — the same name as a structured attribute, so JSON/OTel handlers can parse it.
- Additional `LogRecord` attributes for the event's fields (e.g. `frames`, `properties`, `reason`).

The event set is the source of truth in `aletheia.client._log.LogEvent` (15 values) and is kept identical across Python, C++ (`aletheia::Logger`), and Go (`slog`) so a single log pipeline can consume all three bindings.

```python
import logging

# Capture Aletheia events — route to stdout in this example.
aletheia_logger = logging.getLogger("aletheia")
aletheia_logger.setLevel(logging.INFO)
aletheia_logger.addHandler(logging.StreamHandler())

# Now AletheiaClient lifecycle events (dbc.parsed, properties.set, stream.started,
# stream.ended) appear at INFO. Per-frame events (frame.processed, cache.hit /
# cache.miss) are at DEBUG and stay silent unless the level is lowered.
```

**Performance note**: `log_event` short-circuits on `logger.isEnabledFor(level)` before allocating the `extra` dict, so the default (no DEBUG handler attached) costs a single method call per frame. A missing guard here was the root cause of the R12 Stream LTL regression, fixed in commit `1e40b4d`.

For the full event vocabulary and field list, see the `LogEvent` enum and its docstring in `aletheia/client/_log.py`.

---

## Exceptions

All Aletheia exceptions inherit from a common base class:

```
AletheiaError (base)
├── ProcessError     # FFI or shared library errors (library not found, init failure)
├── ProtocolError    # Protocol errors (invalid JSON, missing response, bad state)
└── BatchError       # send_frames stopped mid-batch; carries .partial_results
```

```python
from aletheia.client import AletheiaError, ProcessError, ProtocolError, BatchError

try:
    client.parse_dbc(dbc)
except ProcessError:
    # Shared library failed to load or initialize
    ...
except ProtocolError:
    # JSON parse error or invalid state transition
    ...
except AletheiaError:
    # Catch-all for any Aletheia error
    ...
```

---

## Utility Functions

These are importable from the top-level `aletheia` package.

#### `dlc_to_bytes(dlc: int) -> int`

Convert a DLC code (0-15) to payload byte count. CAN 2.0B: DLC 0-8 maps directly. See [PROTOCOL.md](../architecture/PROTOCOL.md#1-parsedbc) for the CAN-FD DLC-to-bytes mapping.

#### `bytes_to_dlc(byte_count: int) -> int`

Convert a byte count to the corresponding DLC code. Inverse of `dlc_to_bytes()`.

#### `dbc_to_text(dbc: DBCDefinition) -> str`

Convert a `DBCDefinition` dict to DBC file text format.

#### DBC Query Helpers

Operate on `DBCMessage` / `DBCDefinition` TypedDicts from `aletheia.protocols`:

```python
from aletheia import message_by_id, is_multiplexed, always_present_signals

msg = message_by_id(dbc, 0x100)
if msg and is_multiplexed(msg):
    print(always_present_signals(msg))
```

| Function | Signature | Description |
|----------|-----------|-------------|
| `is_multiplexed` | `(msg) -> bool` | True if message has multiplexed signals |
| `always_present_signals` | `(msg) -> list[DBCSignal]` | Signals present in every frame |
| `multiplexed_signals` | `(msg) -> list[DBCSignal]` | Conditionally-present signals |
| `multiplexor_names` | `(msg) -> list[str]` | Distinct multiplexor signal names |
| `mux_values` | `(msg, multiplexor) -> list[int]` | Multiplex values for a multiplexor |
| `signals_for_mux_value` | `(msg, multiplexor, value) -> list[DBCSignal]` | Signals present for a given mux value |
| `message_by_id` | `(dbc, can_id, *, extended=False) -> DBCMessage \| None` | Look up message by CAN ID |
| `message_by_name` | `(dbc, name) -> DBCMessage \| None` | Look up message by name |
| `signal_by_name` | `(msg, name) -> DBCSignal \| None` | Look up signal by name |

---

## See Also

- **[Interface Guide](INTERFACES.md)** - Check API, YAML loader, Excel loader (higher-level interfaces)
- **[CLI Reference](CLI.md)** - Command-line interface
- [PROTOCOL.md](../architecture/PROTOCOL.md) - JSON protocol specification
- [DESIGN.md](../architecture/DESIGN.md) - System architecture
- [BUILDING.md](../development/BUILDING.md) - Build instructions

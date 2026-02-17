# Tutorials

End-to-end walkthroughs for each audience. Pick the path that matches your role.

| Path | Audience | Tools | Time |
|------|----------|-------|------|
| [Path 1: Technician](#path-1-technician-excel--cli) | Test technician | Excel + CLI | 15 min |
| [Path 2: Test Engineer](#path-2-test-engineer-yaml--cli) | Test engineer | YAML + CLI | 15 min |
| [Path 3: Python Scripter](#path-3-python-scripter-check-api) | Python developer | Check API | 20 min |
| [Path 4: Developer](#path-4-developer-full-dsl) | Software developer | Full DSL | 30 min |

**Prerequisites for all paths**: Aletheia built and installed.
See [Building Guide](../development/BUILDING.md) and [Quick Start](QUICKSTART.md).

---

## Path 1: Technician (Excel + CLI)

Define checks in a spreadsheet, run them from the command line.
No Python coding required.

### Step 1: Create a Template

```bash
python -c "from aletheia import create_template; create_template('checks.xlsx')"
```

This creates an Excel workbook with three sheets: **DBC**, **Checks**, **When-Then**.

### Step 2: Fill in the DBC Sheet

Add one row per signal. Example:

| Message ID | Message Name | DLC | Signal | Start Bit | Length | Byte Order | Signed | Factor | Offset | Min | Max | Unit |
|-----------|-------------|-----|--------|-----------|--------|-----------|--------|--------|--------|-----|-----|------|
| 0x100 | EngineData | 8 | EngineSpeed | 0 | 16 | little_endian | FALSE | 0.25 | 0 | 0 | 8000 | rpm |
| 0x100 | EngineData | 8 | EngineTemp | 16 | 8 | little_endian | TRUE | 1 | -40 | -40 | 215 | C |
| 0x200 | BrakeStatus | 8 | BrakePressure | 0 | 16 | little_endian | FALSE | 0.1 | 0 | 0 | 6553.5 | bar |

Multiple rows with the same Message ID are grouped into one message.
If you have a `.dbc` file from your customer, use `--dbc` instead (skip this sheet).

### Step 3: Fill in the Checks Sheet

| Check Name | Signal | Condition | Value | Min | Max | Time (ms) | Severity |
|-----------|--------|-----------|-------|-----|-----|-----------|----------|
| Speed limit | EngineSpeed | never_exceeds | 8000 | | | | safety |
| Temp range | EngineTemp | stays_between | | -40 | 215 | | warning |

Available conditions: `never_exceeds`, `never_below`, `never_equals`, `equals`,
`stays_between`, `settles_between` (requires Time).

### Step 4: Fill in the When-Then Sheet (Optional)

For causal checks like "when X happens, Y must follow within T ms":

| Check Name | When Signal | When Condition | When Value | Then Signal | Then Condition | Then Value | Then Min | Then Max | Within (ms) | Severity |
|-----------|-----------|---------------|-----------|-----------|--------------|-----------|---------|---------|------------|----------|
| Brake response | BrakePressure | exceeds | 500 | BrakeLight | equals | 1 | | | 100 | safety |

### Step 5: Run Checks

```bash
python -m aletheia check --excel checks.xlsx drive.blf
```

The `--excel` flag loads DBC, Checks, and When-Then from the same workbook.

### Step 6: Read Results

```
Aletheia — CAN Signal Verification

DBC:    checks.xlsx
Checks: checks.xlsx (3 checks)
Log:    drive.blf

Streaming 5000 frames...

RESULT: all checks passed

Summary: 0 violations in 3 checks, 5000 frames processed
```

Exit code `0` = all passed, `1` = violations found.
Add `--json` for machine-readable output.

---

## Path 2: Test Engineer (YAML + CLI)

Write checks in version-controllable YAML. Integrate into CI/CD.

### Step 1: Write a YAML Checks File

Create `checks.yaml`:

```yaml
checks:
  # Simple signal bounds
  - name: "Speed limit"
    signal: VehicleSpeed
    condition: never_exceeds
    value: 220
    severity: safety

  - name: "Battery range"
    signal: BatteryVoltage
    condition: stays_between
    min: 11.5
    max: 14.5
    severity: warning

  # Forbidden value
  - name: "No critical faults"
    signal: FaultCode
    condition: never_equals
    value: 255
    severity: safety

  # Time-bounded settling
  - name: "Coolant settling"
    signal: CoolantTemp
    condition: settles_between
    min: 80
    max: 100
    within_ms: 5000
    severity: info

  # Causal check: when/then
  - name: "Brake response"
    when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
    severity: safety
```

### Step 2: Use a DBC File

Get the `.dbc` file from your customer or ECU vendor. Alternatively, define DBC
in an Excel workbook (see Path 1).

### Step 3: Run Checks

```bash
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

### Step 4: JSON Output for CI/CD

```bash
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf --json
```

```json
{
  "status": "pass",
  "total_frames": 8200,
  "total_violations": 0,
  "violations": []
}
```

Use exit codes in CI: `0` = pass, `1` = violations, `2` = error.

```bash
# In CI script:
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf --json > results.json
if [ $? -ne 0 ]; then echo "Verification failed"; exit 1; fi
```

### Step 5: List Signals (Debugging)

```bash
# See what signals are available in the DBC
python -m aletheia signals --dbc vehicle.dbc

# Decode a single frame
python -m aletheia extract --dbc vehicle.dbc 0x100 401F820000000000
```

---

## Path 3: Python Scripter (Check API)

Use the fluent Check API for programmatic verification.

### Step 1: Import and Define Checks

```python
from aletheia import AletheiaClient, Check
from aletheia.dbc_converter import dbc_to_json
from aletheia.can_log import iter_can_log

# Define checks using industry vocabulary
checks = [
    Check.signal("VehicleSpeed").never_exceeds(220)
        .named("Speed limit").severity("safety"),

    Check.signal("BatteryVoltage").stays_between(11.5, 14.5)
        .named("Battery range").severity("warning"),

    Check.signal("FaultCode").never_equals(255)
        .named("No critical faults").severity("safety"),
]
```

### Step 2: Simple Signal Checks

```python
# Upper bound
Check.signal("Speed").never_exceeds(220)        # G(speed < 220)

# Lower bound
Check.signal("Voltage").never_below(11.0)       # G(voltage >= 11.0)

# Range
Check.signal("Temp").stays_between(80, 100)     # G(80 <= temp <= 100)

# Equality
Check.signal("Fault").never_equals(255)         # G(not(fault == 255))

# Settling (time-bounded range)
Check.signal("Temp").settles_between(80, 100).within(5000)
```

### Step 3: When/Then Causal Checks

```python
# Brake light must activate within 100ms of pedal press
Check.when("BrakePedal").exceeds(50) \
     .then("BrakeLight").equals(1) \
     .within(100)

# Engine must start within 2s of ignition
Check.when("Ignition").equals(1) \
     .then("EngineRPM").exceeds(500) \
     .within(2000)
```

### Step 4: Stream CAN Frames

```python
dbc = dbc_to_json("vehicle.dbc")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([c.to_dict() for c in checks])
    client.set_check_diagnostics(checks)   # enables enriched violations
    client.start_stream()

    for ts, can_id, data in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, data)
        if response.get("status") == "violation":
            name = response.get("signal_name", "?")
            value = response.get("actual_value")
            cond = response.get("condition", "")
            print(f"VIOLATION: {name} = {value} ({cond})")

    client.end_stream()
```

### Step 5: Handle Enriched Violations

When `set_check_diagnostics()` is called, violation responses include extra fields:

```python
{
    "status": "violation",
    "property_index": {"numerator": 0, "denominator": 1},
    "timestamp": {"numerator": 4523000, "denominator": 1},
    "reason": "Always violated",
    "signal_name": "VehicleSpeed",      # enriched
    "actual_value": 225.5,              # enriched
    "condition": "never_exceeds(220)"   # enriched
}
```

---

## Path 4: Developer (Full DSL)

Full LTL control with Signal, Predicate, and Property types.

### Step 1: Signal Predicates

```python
from aletheia import Signal

# Equality
Signal("Gear").equals(0)

# Comparisons
Signal("Speed").less_than(220)
Signal("Speed").greater_than(0)
Signal("Speed").less_than_or_equal(200)
Signal("Speed").greater_than_or_equal(60)

# Range
Signal("Voltage").between(11.5, 14.5)

# Change detection: |now - prev| >= |delta|
Signal("Speed").changed_by(-10)    # decreased by 10+
```

### Step 2: Temporal Operators

```python
# Always (globally): must hold for all frames
Signal("Speed").less_than(220).always()           # G(speed < 220)

# Eventually: must hold at some point
Signal("EngineTemp").greater_than(90).eventually() # F(temp > 90)

# Never: must never hold
Signal("Fault").equals(0xFF).never()               # G(not(fault == 0xFF))

# Time-bounded: within T milliseconds
Signal("DoorClosed").equals(1).within(100)         # F_{<=100}(door == 1)

# Duration: hold for at least T milliseconds
Signal("DoorClosed").equals(1).for_at_least(50)    # G_{<=50}(door == 1)
```

### Step 3: Logical Composition

```python
# AND two predicates
left_brake = Signal("LeftBrake").equals(1)
right_brake = Signal("RightBrake").equals(1)
both_brakes = left_brake.and_(right_brake).always()

# OR
error1 = Signal("Error1").equals(1)
error2 = Signal("Error2").equals(1)
any_error = error1.or_(error2).never()

# Implication: if brake pressed, speed must decrease within 100ms
brake = Signal("BrakePedal").greater_than(0)
decel = Signal("Speed").changed_by(-5)
brake.implies(decel.within(100))

# Until: start button never active until ACC mode
power_off = Signal("PowerMode").equals(0)
power_acc = Signal("PowerMode").equals(2)
start_btn = Signal("StartButton").equals(1)
power_off.implies(start_btn.never().until(power_acc))
```

### Step 4: Advanced Operators

```python
# Release: dual of Until
# Brake must stay engaged until ignition releases it
ignition = Signal("Ignition").equals(1).eventually()
brake = Signal("Brake").equals(1).always()
ignition.release(brake)

# Metric Until: time-bounded until
speed_ok = Signal("Speed").greater_than(50).always()
brake_evt = Signal("Brake").equals(1).eventually()
speed_ok.metric_until(1000, brake_evt)    # within 1 second

# Metric Release: time-bounded release
ignition.metric_release(5000, brake)      # within 5 seconds
```

### Step 5: Signal Operations

```python
with AletheiaClient() as client:
    client.parse_dbc(dbc)

    # Extract signals from a frame
    result = client.extract_signals(can_id=0x100, data=frame_bytes)
    speed = result.get("VehicleSpeed", default=0.0)

    # Build a frame from signal values
    frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})

    # Update specific signals in an existing frame
    modified = client.update_frame(
        can_id=0x100, frame=frame, signals={"VehicleSpeed": 130.0}
    )
```

### Step 6: Mixing Tiers

All tiers compile to the same LTL formulas. Mix freely:

```python
from aletheia import Check, load_checks, Signal

# Load base checks from YAML
checks = load_checks("checks.yaml")

# Add a Check API check
checks.append(Check.signal("Speed").never_exceeds(220))

# Add a raw DSL property (wrap in CheckResult for metadata)
from aletheia.checks import CheckResult
prop = Signal("Temp").between(-40, 215).always()
checks.append(CheckResult(prop, name="Temp range"))

# All used the same way
client.set_properties([c.to_dict() for c in checks])
```

---

## See Also

- **[Quick Start](QUICKSTART.md)** — 5-minute path from zero to working verification
- **[Cookbook](COOKBOOK.md)** — Problem-driven recipes
- **[Interface Guide](../reference/INTERFACES.md)** — Complete Check API, YAML, Excel reference
- **[Python API Guide](../reference/PYTHON_API.md)** — Full DSL and AletheiaClient reference
- **[CLI Reference](../reference/CLI.md)** — All subcommands and flags

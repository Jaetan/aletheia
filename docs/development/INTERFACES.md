# Aletheia Interface Guide

**Purpose**: Guide to defining signal checks using the Check API, YAML, and Excel interfaces.
**Version**: 0.3.2
**Last Updated**: 2026-02-07

> **Full LTL control**: For the raw DSL (Signal, Predicate, Property) and AletheiaClient,
> see the [Python API Guide](PYTHON_API.md).

---

## Overview

Aletheia provides four interface tiers. All compile to the same verified LTL
formulas — only the syntax differs.

| Tier | Audience | When to use |
|------|----------|-------------|
| **Excel** | Technician | Fill in spreadsheet templates, no code |
| **YAML** | Test engineer | Declarative config, version-controllable, CI/CD |
| **Check API** | Python scripter | `Check.signal("Speed").never_exceeds(220)` |
| **DSL** | Developer | Full LTL: `Signal("Speed").less_than(220).always()` |

Choose the simplest tier that covers your needs. You can mix tiers freely —
load DBC from Excel, checks from YAML, and additional checks from the
Check API, all in the same session.

---

## Check API

The Check API wraps the DSL with industry vocabulary. Each method returns a
`CheckResult` that can be named, given a severity, and serialized to the
same JSON that the verified Agda core processes.

```python
from aletheia import Check
```

### Simple Signal Checks

```python
# Value bounds
Check.signal("VehicleSpeed").never_exceeds(220)      # G(speed < 220)
Check.signal("BatteryVoltage").never_below(11.0)     # G(voltage >= 11.0)

# Range
Check.signal("BatteryVoltage").stays_between(11.5, 14.5)  # G(11.5 <= v <= 14.5)

# Equality
Check.signal("FaultCode").never_equals(255)           # G(not(fault == 255))
Check.signal("ParkingBrake").equals(1).always()        # G(brake == 1)

# Settling (time-bounded range)
Check.signal("CoolantTemp").settles_between(80, 100).within(5000)
# G_{<=5000}(80 <= temp <= 100)
```

### When/Then Causal Checks

Express response-time requirements: "when X happens, Y must follow within T ms."

```python
# Brake light must activate within 100ms of pedal press
Check.when("BrakePedal").exceeds(50) \
     .then("BrakeLight").equals(1) \
     .within(100)

# Engine must start within 2s of ignition
Check.when("Ignition").equals(1) \
     .then("EngineRPM").exceeds(500) \
     .within(2000)

# Fuel warning must activate within 50ms of low fuel
Check.when("FuelLevel").drops_below(10) \
     .then("FuelWarning").stays_between(1, 1) \
     .within(50)
```

### When Conditions

| Method | Fires when |
|--------|-----------|
| `.exceeds(value)` | signal > value |
| `.equals(value)` | signal == value |
| `.drops_below(value)` | signal < value |

### Then Conditions

| Method | Requires |
|--------|---------|
| `.equals(value)` | signal == value |
| `.exceeds(value)` | signal > value |
| `.stays_between(lo, hi)` | lo <= signal <= hi |

### Metadata

Every check can carry a name and severity for reporting. Metadata does not
affect the LTL formula.

```python
check = (
    Check.signal("VehicleSpeed").never_exceeds(220)
    .named("Speed limit")
    .severity("safety")
)

check.name            # "Speed limit"
check.check_severity  # "safety"
check.to_dict()       # LTL formula (same with or without metadata)
```

### Using Checks with AletheiaClient

```python
from aletheia import AletheiaClient, Check
from aletheia.dbc_converter import dbc_to_json

checks = [
    Check.signal("VehicleSpeed").never_exceeds(220),
    Check.signal("BatteryVoltage").stays_between(11.5, 14.5),
    Check.when("BrakePedal").exceeds(50)
         .then("BrakeLight").equals(1).within(100),
]

dbc = dbc_to_json("vehicle.dbc")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([c.to_dict() for c in checks])
    client.start_stream()

    for timestamp, can_id, data in can_trace:
        response = client.send_frame(timestamp, can_id, data)
        if response.get("status") == "violation":
            idx = response["property_index"]["numerator"]
            print(f"Check {idx} violated at {response['timestamp']}")

    client.end_stream()
```

### Check API Reference

```python
class Check:
    @staticmethod
    def signal(name: str) -> CheckSignal
    @staticmethod
    def when(signal_name: str) -> WhenSignal

class CheckResult:
    def named(self, name: str) -> CheckResult
    def severity(self, level: str) -> CheckResult
    def to_dict(self) -> LTLFormula
    def to_property(self) -> Property
    name: str | None
    check_severity: str | None
```

---

## YAML Loader

Define checks in YAML files for version control and CI/CD integration.

```python
from aletheia import load_checks
```

### Loading Checks

```python
# From a file
checks = load_checks("checks.yaml")

# From a YAML string
checks = load_checks("""
checks:
  - signal: VehicleSpeed
    condition: never_exceeds
    value: 220
    severity: safety
""")

# Use with AletheiaClient
client.set_properties([c.to_dict() for c in checks])
```

### YAML Schema

#### Simple Checks

```yaml
checks:
  - name: "Speed limit"           # optional display name
    signal: VehicleSpeed
    condition: never_exceeds       # see condition table below
    value: 220                     # for value-based conditions
    severity: safety               # optional severity level
```

**Value-based conditions** (require `value`):

| Condition | LTL | Meaning |
|-----------|-----|---------|
| `never_exceeds` | G(s < v) | Signal always below value |
| `never_below` | G(s >= v) | Signal never drops below value |
| `never_equals` | G(not(s == v)) | Signal never equals value |
| `equals` | G(s == v) | Signal always equals value |

**Range-based conditions** (require `min` and `max`):

| Condition | LTL | Meaning |
|-----------|-----|---------|
| `stays_between` | G(min <= s <= max) | Signal always in range |
| `settles_between` | G_{<=t}(min <= s <= max) | Signal in range for duration (also requires `within_ms`) |

```yaml
checks:
  - name: "Battery range"
    signal: BatteryVoltage
    condition: stays_between
    min: 11.5
    max: 14.5

  - name: "Coolant settling"
    signal: CoolantTemp
    condition: settles_between
    min: 80
    max: 100
    within_ms: 5000               # required for settles_between
```

#### When/Then Checks

```yaml
checks:
  - name: "Brake response"
    when:
      signal: BrakePedal
      condition: exceeds           # exceeds | equals | drops_below
      value: 50
    then:
      signal: BrakeLight
      condition: equals            # equals | exceeds | stays_between
      value: 1
    within_ms: 100                 # response deadline in ms
    severity: safety
```

For `then` condition `stays_between`, use `min` and `max` instead of `value`:

```yaml
    then:
      signal: FuelWarning
      condition: stays_between
      min: 1
      max: 1
```

### Complete Example File

```yaml
checks:
  # Simple checks
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

  # Causal check
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

### Error Messages

Errors reference the check name (or `<unnamed>` if no name is set):

```
Check 'Speed limit': missing or invalid 'value' (expected number)
Check '<unnamed>': unknown condition 'bogus'
Check 'Brake response': when/then checks require 'within_ms'
```

---

## Excel Loader

Load checks and DBC definitions from Excel workbooks (.xlsx).

```python
from aletheia import load_checks_from_excel, load_dbc_from_excel, create_template
```

### End-to-End Workflow

**1. Create a template:**

```python
from aletheia import create_template
create_template("vehicle_checks.xlsx")
```

This creates a workbook with three sheets (DBC, Checks, When-Then), each
with bold headers. Open it in Excel or LibreOffice.

**2. Fill in the DBC sheet** (one row per signal):

| Message ID | Message Name | DLC | Signal | Start Bit | Length | Byte Order | Signed | Factor | Offset | Min | Max | Unit |
|-----------|-------------|-----|--------|-----------|--------|-----------|--------|--------|--------|-----|-----|------|
| 0x100 | EngineData | 8 | EngineSpeed | 0 | 16 | little_endian | FALSE | 0.25 | 0 | 0 | 8000 | rpm |
| 0x100 | EngineData | 8 | EngineTemp | 16 | 8 | little_endian | TRUE | 1 | -40 | -40 | 215 | C |
| 0x200 | BrakeStatus | 8 | BrakePressure | 0 | 16 | little_endian | FALSE | 0.1 | 0 | 0 | 6553.5 | bar |

Multiple rows with the same Message ID are grouped into one message.
Message IDs can be hex strings (`0x100`) or decimal (`256`).

**3. Fill in the Checks sheet** (one row per simple check):

| Check Name | Signal | Condition | Value | Min | Max | Time (ms) | Severity |
|-----------|--------|-----------|-------|-----|-----|-----------|----------|
| Speed limit | EngineSpeed | never_exceeds | 8000 | | | | safety |
| Temp range | EngineTemp | stays_between | | -40 | 215 | | warning |
| Settling | EngineTemp | settles_between | | 80 | 100 | 5000 | info |

Leave cells empty (not zero) for fields that don't apply to a condition.

**4. Fill in the When-Then sheet** (one row per causal check):

| Check Name | When Signal | When Condition | When Value | Then Signal | Then Condition | Then Value | Then Min | Then Max | Within (ms) | Severity |
|-----------|-----------|---------------|-----------|-----------|--------------|-----------|---------|---------|------------|----------|
| Brake response | BrakePressure | exceeds | 500 | BrakeLight | equals | 1 | | | 100 | safety |

**5. Load and run:**

```python
from aletheia import AletheiaClient, load_checks_from_excel, load_dbc_from_excel

# Load DBC and checks from the same workbook (or separate ones)
dbc = load_dbc_from_excel("vehicle_checks.xlsx")
checks = load_checks_from_excel("vehicle_checks.xlsx")

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.set_properties([c.to_dict() for c in checks])
    client.start_stream()

    for timestamp, can_id, data in can_trace:
        response = client.send_frame(timestamp, can_id, data)
        if response.get("status") == "violation":
            idx = response["property_index"]["numerator"]
            print(f"Check '{checks[idx].name}' violated")

    client.end_stream()
```

### DBC Sheet Columns

| Column | Type | Required | Notes |
|--------|------|----------|-------|
| Message ID | int or hex string | yes | `0x100` or `256` |
| Message Name | string | yes | |
| DLC | int | yes | 1-8 |
| Signal | string | yes | Signal name |
| Start Bit | int | yes | 0-63 |
| Length | int | yes | Bit length |
| Byte Order | string | yes | `little_endian` or `big_endian` |
| Signed | bool | yes | TRUE or FALSE |
| Factor | float | yes | Scale factor |
| Offset | float | yes | Signal offset |
| Min | float | yes | Minimum value |
| Max | float | yes | Maximum value |
| Unit | string | no | e.g. `km/h`, `V` |
| Multiplexor | string | no | Multiplexor signal name (both or neither) |
| Multiplex Value | int | no | Multiplexor value (both or neither) |

If both Multiplexor and Multiplex Value are provided, the signal is
multiplexed. If both are empty, the signal is always-present.

### Checks Sheet Columns

| Column | Type | Required | Notes |
|--------|------|----------|-------|
| Check Name | string | no | Display name |
| Signal | string | yes | Signal name |
| Condition | string | yes | See condition table in YAML section |
| Value | float | conditional | For value-based conditions |
| Min | float | conditional | For range-based conditions |
| Max | float | conditional | For range-based conditions |
| Time (ms) | int | conditional | Required for `settles_between` |
| Severity | string | no | e.g. `critical`, `warning`, `safety` |

### When-Then Sheet Columns

| Column | Type | Required | Notes |
|--------|------|----------|-------|
| Check Name | string | no | Display name |
| When Signal | string | yes | Trigger signal |
| When Condition | string | yes | `exceeds`, `equals`, `drops_below` |
| When Value | float | yes | Trigger threshold |
| Then Signal | string | yes | Response signal |
| Then Condition | string | yes | `equals`, `exceeds`, `stays_between` |
| Then Value | float | conditional | For `equals`/`exceeds` |
| Then Min | float | conditional | For `stays_between` |
| Then Max | float | conditional | For `stays_between` |
| Within (ms) | int | yes | Response deadline |
| Severity | string | no | |

### Error Messages

Errors reference row numbers (1-indexed, counting from the header):

```
Row 5: unknown condition 'bogus'
Row 3: condition 'stays_between' requires 'Min' and 'Max'
Row 7: invalid 'Message ID' — expected integer or hex string (e.g. 0x100)
```

### API Reference

```python
def load_checks_from_excel(
    path: str | Path,
    *,
    checks_sheet: str = "Checks",       # sheet name override
    when_then_sheet: str = "When-Then",  # sheet name override
) -> list[CheckResult]

def load_dbc_from_excel(
    path: str | Path,
    *,
    sheet: str = "DBC",                  # sheet name override
) -> DBCDefinition

def create_template(path: str | Path) -> None
# Raises FileExistsError if file already exists
```

---

## Condition Reference

All three interfaces (Check API, YAML, Excel) support the same conditions:

### Simple Conditions

| Condition | Check API | LTL |
|-----------|-----------|-----|
| `never_exceeds` | `.never_exceeds(v)` | G(s < v) |
| `never_below` | `.never_below(v)` | G(s >= v) |
| `never_equals` | `.never_equals(v)` | G(not(s == v)) |
| `equals` | `.equals(v).always()` | G(s == v) |
| `stays_between` | `.stays_between(lo, hi)` | G(lo <= s <= hi) |
| `settles_between` | `.settles_between(lo, hi).within(t)` | G_{<=t}(lo <= s <= hi) |

### When Conditions

| Condition | Check API | Meaning |
|-----------|-----------|---------|
| `exceeds` | `.exceeds(v)` | s > v |
| `equals` | `.equals(v)` | s == v |
| `drops_below` | `.drops_below(v)` | s < v |

### Then Conditions

| Condition | Check API | Meaning |
|-----------|-----------|---------|
| `equals` | `.equals(v)` | s == v |
| `exceeds` | `.exceeds(v)` | s > v |
| `stays_between` | `.stays_between(lo, hi)` | lo <= s <= hi |

---

## Equivalence

All four tiers produce identical LTL formulas. This check:

```python
# Check API
Check.signal("VehicleSpeed").never_exceeds(220)
```

```yaml
# YAML
checks:
  - signal: VehicleSpeed
    condition: never_exceeds
    value: 220
```

```
# Excel (Checks sheet row)
| | VehicleSpeed | never_exceeds | 220 | | | | |
```

```python
# DSL
Signal("VehicleSpeed").less_than(220).always()
```

All produce:

```json
{
  "operator": "always",
  "formula": {
    "operator": "atomic",
    "predicate": {
      "predicate": "lessThan",
      "signal": "VehicleSpeed",
      "value": 220
    }
  }
}
```

---

## See Also

- **[Python API Guide](PYTHON_API.md)** - Raw DSL (Signal, Predicate, Property) and AletheiaClient
- **[Demo scripts](../../examples/demo/)** - Runnable demos for each interface tier
- [BUILDING.md](BUILDING.md) - Build instructions

# Cookbook

Problem-driven recipes. Each recipe is self-contained: title, code, done.

---

## Signal Bound Checks

### Signal never exceeds a value

```python
Check.signal("VehicleSpeed").never_exceeds(220)
```

```yaml
- signal: VehicleSpeed
  condition: never_exceeds
  value: 220
```

### Signal never drops below a value

```python
Check.signal("BatteryVoltage").never_below(11.0)
```

```yaml
- signal: BatteryVoltage
  condition: never_below
  value: 11.0
```

### Signal stays in a range

```python
Check.signal("BatteryVoltage").stays_between(11.5, 14.5)
```

```yaml
- signal: BatteryVoltage
  condition: stays_between
  min: 11.5
  max: 14.5
```

### Signal never equals a forbidden value

```python
Check.signal("FaultCode").never_equals(255)
```

```yaml
- signal: FaultCode
  condition: never_equals
  value: 255
```

### Signal settles into range within time

```python
Check.signal("CoolantTemp").settles_between(80, 100).within(5000)
```

```yaml
- signal: CoolantTemp
  condition: settles_between
  min: 80
  max: 100
  within_ms: 5000
```

---

## Causal / Response-Time Checks

### When A happens, B must follow within T ms

```python
Check.when("BrakePedal").exceeds(50) \
     .then("BrakeLight").equals(1) \
     .within(100)
```

```yaml
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
```

### Engine must start within T ms of ignition

```python
Check.when("Ignition").equals(1) \
     .then("EngineRPM").exceeds(500) \
     .within(2000)
```

### Signal settles after trigger

```python
Check.when("FuelLevel").drops_below(10) \
     .then("FuelWarning").stays_between(1, 1) \
     .within(50)
```

---

## Working with CAN Logs

### Read a BLF file and check it (CLI)

```bash
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

### Read a CAN log in Python (eager)

```python
from aletheia.can_log import load_can_log

frames = load_can_log("drive.blf")
# frames is list[(timestamp_us, arbitration_id, bytearray)]
```

### Process a large log lazily (streaming)

```python
from aletheia.can_log import iter_can_log

for ts, can_id, data in iter_can_log("highway.asc"):
    response = client.send_frame(ts, can_id, data)
```

### Skip error/remote frames (default) or include them

```python
# Default: error and remote frames are skipped
frames = load_can_log("drive.blf")

# Include everything
frames = load_can_log("drive.blf", skip_error_frames=False, skip_remote_frames=False)

# Strict DLC: raise ValueError for non-8-byte frames
frames = load_can_log("drive.blf", strict_dlc=True)
```

### Supported CAN log formats

`.asc`, `.blf`, `.csv`, `.log`, `.mf4`, `.trc` (via python-can).

---

## Working with DBC

### Load DBC from a .dbc file

```python
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("vehicle.dbc")
client.parse_dbc(dbc)
```

### Define DBC in Excel

```python
from aletheia import load_dbc_from_excel

dbc = load_dbc_from_excel("vehicle_checks.xlsx")
client.parse_dbc(dbc)
```

### List all signals in a DBC (CLI)

```bash
python -m aletheia signals --dbc vehicle.dbc
```

### List signals as JSON

```bash
python -m aletheia signals --dbc vehicle.dbc --json
```

---

## Signal Operations

### Extract all signals from a frame

```python
result = client.extract_signals(can_id=0x100, data=frame_bytes)
speed = result.get("VehicleSpeed", default=0.0)

# Check for errors and absent (multiplexed) signals
if result.has_errors():
    print(f"Errors: {result.errors}")
print(f"Absent: {result.absent}")
```

### Extract signals from CLI

```bash
python -m aletheia extract --dbc vehicle.dbc 0x100 401F820000000000
```

### Build a frame from signal values

```python
frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})
# Returns bytearray with VehicleSpeed encoded
```

### Inject modified signals during streaming

```python
client.start_stream()
for ts, can_id, data in iter_can_log("drive.blf"):
    # Modify speed to test property with altered values
    modified = client.update_frame(
        can_id=can_id, frame=data, signals={"VehicleSpeed": 130.0}
    )
    response = client.send_frame(ts, can_id, modified)
client.end_stream()
```

---

## CLI Recipes

### Run checks in CI/CD (exit codes + JSON)

```bash
python -m aletheia check \
    --dbc vehicle.dbc \
    --checks checks.yaml \
    --json \
    drive.blf > results.json

# Exit code: 0=pass, 1=violations, 2=error
echo "Exit code: $?"
```

### Decode a single frame

```bash
python -m aletheia extract --dbc vehicle.dbc 0x100 "40 1F 82 00 00 00 00 00"
```

### Use Excel workbook for everything

```bash
# DBC + checks from the same .xlsx
python -m aletheia check --excel vehicle_checks.xlsx drive.blf
```

### Mix DBC from .dbc with checks from .yaml

```bash
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

---

## Enriched Violations

### Enable enriched diagnostics

```python
client.set_properties([c.to_dict() for c in checks])
client.set_check_diagnostics(checks)  # call AFTER set_properties()
```

### Get signal name, value, and condition from violations

```python
response = client.send_frame(ts, can_id, data)
if response.get("status") == "violation":
    signal = response.get("signal_name", "unknown")
    value = response.get("actual_value")
    condition = response.get("condition", "")
    print(f"{signal} = {value} violated {condition}")
```

### Custom violation formatting

```python
violations = []
for ts, can_id, data in iter_can_log("drive.blf"):
    response = client.send_frame(ts, can_id, data)
    if response.get("status") == "violation":
        violations.append(response)

for v in violations:
    ts_ms = v["timestamp"]["numerator"] / 1000
    idx = v["property_index"]["numerator"]
    name = checks[idx].name or f"Check #{idx}"
    signal = v.get("signal_name", "?")
    value = v.get("actual_value")
    print(f"[{ts_ms:.1f}ms] {name}: {signal}={value}")
```

---

## Mixing Interface Tiers

### Load checks from multiple sources

```python
from aletheia import Check, load_checks, load_checks_from_excel

checks = []
checks.extend(load_checks("base_checks.yaml"))           # YAML
checks.extend(load_checks_from_excel("extra_checks.xlsx")) # Excel
checks.append(Check.signal("Speed").never_exceeds(220))   # Check API

client.set_properties([c.to_dict() for c in checks])
```

### Create an Excel template

```python
from aletheia import create_template
create_template("vehicle_checks.xlsx")
# Opens with three sheets: DBC, Checks, When-Then
```

---

## See Also

- **[Quick Start](QUICKSTART.md)** — 5-minute tutorial
- **[Tutorials](TUTORIAL.md)** — End-to-end walkthroughs by role
- **[Interface Guide](../reference/INTERFACES.md)** — Complete schema reference
- **[Python API Guide](../reference/PYTHON_API.md)** — Full DSL reference
- **[CLI Reference](../reference/CLI.md)** — All subcommands and flags

# Cookbook

Problem-driven recipes. Each recipe is self-contained: title, code, done.

**Prerequisites**: A built Aletheia installation and a loaded DBC. See [Building Guide](../development/BUILDING.md) for setup.

### Use-Case Index

| I want to... | Recipe |
|--------------|--------|
| Check a signal stays within limits | [Signal Bound Checks](#signal-bound-checks) |
| Detect signal changes or check stability | [Change Detection & Stability](#change-detection--stability) |
| Verify "when A then B within T ms" | [Causal / Response-Time Checks](#causal--response-time-checks) |
| Read a CAN log file (.blf, .asc, etc.) | [Working with CAN Logs](#working-with-can-logs) |
| Load a DBC from .dbc or Excel | [Working with DBC](#working-with-dbc) |
| Extract / build / modify CAN frames | [Signal Operations](#signal-operations) |
| Run checks in CI/CD or from the CLI | [CLI Recipes](#cli-recipes) |
| Enrich violations with signal names & values | [Enriched Violations](#enriched-violations) |
| Mix Check API, YAML, and Excel together | [Mixing Interface Tiers](#mixing-interface-tiers) |

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

## Change Detection & Stability

These predicates use frame-to-frame delta tracking and are available via the DSL only (not YAML/Excel).

### Flag when a signal drops by at least N

```python
# Speed must never drop by 10+ in a single frame (violations = detections)
Signal("VehicleSpeed").changed_by(-10).never()
```

Positive delta means "increased by at least delta"; negative means "decreased by at least |delta|".

### Require that a signal increases by at least N

```python
# RPM must jump up by 500+ at some point (e.g., engine must start)
Signal("EngineRPM").changed_by(500).eventually()
```

### Check signal stays stable within tolerance

```python
# Temperature stable within ±2 degrees frame-to-frame
Signal("CoolantTemp").stable_within(2.0).always()
```

### Combine stability with a time window

```python
# After warmup, temperature must stabilize within ±1 degree
Signal("CoolantTemp").stable_within(1.0).within(30000)
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
python3 -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

### Read a CAN log in Python (eager)

```python
from aletheia.can_log import load_can_log

frames = load_can_log("drive.blf")
# frames is list[(timestamp_us, arbitration_id, dlc, data)]
```

### Process a large log lazily (streaming)

```python
from aletheia.can_log import iter_can_log

for ts, can_id, dlc, data in iter_can_log("highway.asc"):
    response = client.send_frame(ts, can_id, dlc, data)
```

### Skip error/remote frames (default) or include them

```python
# Default: error and remote frames are skipped
frames = load_can_log("drive.blf")

# Include everything
frames = load_can_log("drive.blf", skip_error_frames=False, skip_remote_frames=False)

# Strict mode: raise on corrupt frames instead of skipping
frames = load_can_log("drive.blf", on_error="raise")
```

### Supported CAN log formats

See [CLI Reference](../reference/CLI.md#input-formats) for the full list of supported CAN log formats (via python-can).

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
python3 -m aletheia signals --dbc vehicle.dbc
```

### List signals as JSON

```bash
python3 -m aletheia signals --dbc vehicle.dbc --json
```

---

## Signal Operations

### Extract all signals from a frame

```python
result = client.extract_signals(can_id=0x100, dlc=8, data=frame_bytes)
speed = result.get("VehicleSpeed", default=0.0)

# Check for errors and absent (multiplexed) signals
if result.has_errors():
    print(f"Errors: {result.errors}")
print(f"Absent: {result.absent}")
```

### Extract signals from CLI

```bash
python3 -m aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
```

### Build a frame from signal values

```python
frame = client.build_frame(can_id=0x100, signals={"VehicleSpeed": 72.0})
# Returns bytearray with VehicleSpeed encoded
```

### Inject modified signals during streaming

```python
client.start_stream()
for ts, can_id, dlc, data in iter_can_log("drive.blf"):
    # Modify speed to test property with altered values
    modified = client.update_frame(
        can_id=can_id, dlc=dlc, frame=data, signals={"VehicleSpeed": 130.0}
    )
    response = client.send_frame(ts, can_id, dlc, modified)
client.end_stream()
```

---

## CLI Recipes

### Run checks in CI/CD (exit codes + JSON)

```bash
python3 -m aletheia check \
    --dbc vehicle.dbc \
    --checks checks.yaml \
    --json \
    drive.blf > results.json

# Exit code: 0=pass, 1=violations, 2=error
echo "Exit code: $?"
```

### Decode a single frame

```bash
python3 -m aletheia extract --dbc vehicle.dbc 0x100 "40 1F 7D 00 00 00 00 00"
```

### Use Excel workbook for everything

```bash
# DBC + checks from the same .xlsx
python3 -m aletheia check --excel vehicle_checks.xlsx drive.blf
```

### Mix DBC from .dbc with checks from .yaml

```bash
python3 -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

---

## Enriched Violations

### Enable enriched diagnostics

Enrichment is automatic when checks are registered via `add_checks()`:

```python
client.add_checks(checks)
```

### Get signal values and formula from violations

```python
response = client.send_frame(ts, can_id, dlc, data)
if response.get("status") == "fails":
    signals = response.get("signals", {})
    formula = response.get("formula", "")
    reason = response.get("enriched_reason", "")
    print(f"{reason}  signals={signals}")
```

### Custom violation formatting

```python
# Assumes: client in streaming mode with checks registered (see recipes above)
from aletheia import iter_can_log

violations = []
for ts, can_id, dlc, data in iter_can_log("drive.blf"):
    response = client.send_frame(ts, can_id, dlc, data)
    if response.get("status") == "fails":
        violations.append(response)

for v in violations:
    ts_ms = v["timestamp"]["numerator"] / 1000  # µs → ms
    idx = v["property_index"]["numerator"]
    name = checks[idx].name or f"Check #{idx}"
    reason = v.get("enriched_reason", "?")
    print(f"[{ts_ms:.1f}ms] {name}: {reason}")
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

client.add_checks(checks)
```

### Create an Excel template

```python
from aletheia import create_template
create_template("vehicle_checks.xlsx")
# Creates a file with three sheets: DBC, Checks, When-Then
```

---

## See Also

- **[Quick Start](QUICKSTART.md)** — 5-minute tutorial
- **[Tutorials](TUTORIAL.md)** — End-to-end walkthroughs by role
- **[Interface Guide](../reference/INTERFACES.md)** — Complete schema reference
- **[Python API Guide](../reference/PYTHON_API.md)** — Full DSL reference
- **[CLI Reference](../reference/CLI.md)** — All subcommands and flags

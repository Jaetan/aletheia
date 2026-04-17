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

for ts, can_id, dlc, data, _extended in iter_can_log("highway.asc"):
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

### Capture CAN traffic on Linux (candump)

For simulations running on Linux with a SocketCAN interface (real `canN` or virtual `vcanN`), `candump` from `can-utils` writes the `.log` format Aletheia reads natively — no conversion step.

> **Prerequisites.** `candump` ships in the `can-utils` package (`sudo apt install can-utils` on Debian/Ubuntu, or the equivalent for your distro). The `vcan` kernel module is in-tree on every supported Linux kernel; `modprobe vcan` is enough on a fresh system. Real CAN hardware does not need `vcan` — replace `vcan0` with the interface name your driver exposes (`can0`, etc.).

```bash
# One-time: set up a virtual CAN interface (skip if using real CAN hardware)
sudo modprobe vcan
sudo ip link add dev vcan0 type vcan
sudo ip link set up vcan0

# Capture
candump -L vcan0 > drive.log

# Replay through Aletheia
python3 -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.log
```

See [CLI Reference § Capturing CAN traffic on Linux](../reference/CLI.md#capturing-can-traffic-on-linux) for rotating captures and the `vcan` setup details.

### Supported CAN log formats

See [CLI Reference § Input Formats](../reference/CLI.md#input-formats) for the full list of supported CAN log formats, their typical sources, and which commercial toolchains produce them natively.

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

## Validating a DBC

### Check a DBC for structural issues (CLI)

```bash
python3 -m aletheia validate --dbc vehicle.dbc
```

The CLI exits **non-zero** when the DBC contains at least one `error`-severity
issue, **zero** when only `warning`-severity issues are present, and zero when
the DBC is clean. This makes `aletheia validate` safe to drop into CI as a
gating step.

### Interpret validation errors

```bash
python3 -m aletheia validate --dbc vehicle.dbc --json | jq '.issues[]'
```

```json
{
  "code": "signal_overlaps_another",
  "severity": "error",
  "message": "EngineSpeed [bits 0:16] overlaps Throttle [bits 8:8] in EngineCmd",
  "context": {"message": "EngineCmd", "signals": ["EngineSpeed", "Throttle"]}
}
```

The most common codes you'll see:

| Code | Meaning | Severity |
|---|---|---|
| `signal_overlaps_another` | Two signals share at least one bit. | error |
| `signal_exceeds_message_size` | Signal's bit range extends past `DLC` bytes. | error |
| `multiplexor_value_conflict` | Multiplexor value claimed by two distinct signals. | error |
| `signal_factor_zero` | `factor=0` makes physical-value extraction undefined. | error |
| `duplicate_message_id` | Two messages share the same CAN ID. | error |
| `unused_signal` | Signal defined but no message references it. | warning |

The full list lives in [`PROTOCOL.md`](../architecture/PROTOCOL.md#common-error-codes). The structured `code` field
is the stable contract — `message` text is for humans and may change between
releases.

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
frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 72.0})
# Returns bytearray with VehicleSpeed encoded
```

### Inject modified signals during streaming

```python
client.start_stream()
for ts, can_id, dlc, data, _extended in iter_can_log("drive.blf"):
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
    enrichment = response.get("enrichment", {})
    signals = enrichment.get("signals", {})
    formula = enrichment.get("formula_desc", "")
    reason = enrichment.get("enriched_reason", "")
    print(f"{reason}  signals={signals}")
```

### Custom violation formatting

```python
# Assumes: client in streaming mode with checks registered (see recipes above)
from aletheia import iter_can_log

violations = []
for ts, can_id, dlc, data, _extended in iter_can_log("drive.blf"):
    response = client.send_frame(ts, can_id, dlc, data)
    if response.get("status") == "fails":
        violations.append(response)

for v in violations:
    ts_ms = v["timestamp"]["numerator"] / 1000  # µs → ms
    idx = v["property_index"]["numerator"]
    name = checks[idx].name or f"Check #{idx}"
    reason = v.get("enrichment", {}).get("enriched_reason", "?")
    print(f"[{ts_ms:.1f}ms] {name}: {reason}")
```

### Debug a single violation end-to-end

When a check fires unexpectedly, the goal is usually: which frame, which
signals, which sub-formula? The enriched response carries all three.

```python
import logging
from aletheia import AletheiaClient, Check, iter_can_log
from aletheia.dbc_converter import dbc_to_json

# Surface backend lifecycle + violation events. The `aletheia` logger emits
# 15 structured event types — see PROTOCOL.md § Structured Logging.
logging.basicConfig(level=logging.INFO, format="%(name)s %(levelname)s %(message)s")

dbc = dbc_to_json("vehicle.dbc")
checks = [Check.signal("Speed").never_exceeds(220).named("speed_limit")]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(checks)
    client.start_stream()

    for ts, can_id, dlc, data, _extended in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("status") != "fails":
            continue

        # Three things to look at, in order:
        e = response["enrichment"]

        # 1. Which signals contributed (their decoded physical values).
        print("signals at violation:", e["signals"])

        # 2. Which sub-formula tripped (human-readable reconstruction).
        print("formula:", e["formula_desc"])

        # 3. The enriched_reason combines (1) + (2) into one sentence,
        #    typically the right thing to surface in a CI report.
        print("reason:", e["enriched_reason"])

        # Stop on first violation if you only want the smoking gun.
        break

    client.end_stream()
```

The `enrichment` block is only populated for checks registered via
`add_checks(...)`; the lower-level `set_properties(...)` path returns the
verdict but not the human-readable signal/formula context. If `enrichment` is
missing on a `fails` response, that's the cause.

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

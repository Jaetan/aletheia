# Quick Start

Get to a working CAN verification in 5 minutes.

**Prerequisites**: Built library and Python venv active.
See [Building Guide](../development/BUILDING.md) if you haven't built yet.

---

## 1. Define Checks (YAML)

Create `checks.yaml`:

```yaml
checks:
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
```

## 2. Run Against a CAN Log

```bash
python -m aletheia check --dbc vehicle.dbc --checks checks.yaml drive.blf
```

## 3. Interpret Results

```
Aletheia — CAN Signal Verification

DBC:    vehicle.dbc
Checks: checks.yaml (2 checks)
Log:    drive.blf

Streaming 8200 frames...

RESULT: 1 violations found

  1. [t=4523.000ms] Speed limit (safety)
     Always violated

Summary: 1 violations in 2 checks, 8200 frames processed
```

Exit code `1` means violations were found. Exit code `0` means all checks passed.

Add `--json` for machine-readable output (CI/CD integration).

## 4. Alternatively: Use Python

```python
from aletheia import AletheiaClient, Check
from aletheia.dbc_converter import dbc_to_json
from aletheia.can_log import iter_can_log

dbc = dbc_to_json("vehicle.dbc")
checks = [
    Check.signal("VehicleSpeed").never_exceeds(220).severity("safety"),
    Check.signal("BatteryVoltage").stays_between(11.5, 14.5),
]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(checks)
    client.start_stream()

    for ts, can_id, dlc, data in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("status") == "fails":
            print(f"Violation: {response.get('enriched_reason')}")

    client.end_stream()
```

---

## Next Steps

- **More check types**: [Interface Guide](../reference/INTERFACES.md) (YAML schema, Excel, Check API)
- **Full DSL**: [Python API Guide](../reference/PYTHON_API.md) (LTL operators, signal operations)
- **Recipes**: [Cookbook](COOKBOOK.md) (common patterns, copy-paste solutions)
- **Walkthroughs**: [Tutorials](TUTORIAL.md) (end-to-end paths by role)
- **CLI reference**: [CLI](../reference/CLI.md) (all subcommands and flags)

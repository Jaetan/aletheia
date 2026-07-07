# Quick Start

Get to a working CAN verification in 5 minutes.

## 0. Prerequisites & first build

Before the five-minute walkthrough below, the Agda → Haskell shared library needs to exist and the Python package needs to be importable:

1. **Toolchain**: GHC ≥ 9.4, cabal ≥ 3.12, Agda 2.8.0, Python ≥ 3.14, `libgmp-dev`. See [Building Guide §1 Prerequisites](../development/BUILDING.md#prerequisites) for the exact versions and the install command for your platform. Quick check that the right versions are on `PATH`:
   ```bash
   ghc --version       # expect: The Glorious Glasgow Haskell Compilation System, version 9.4 or newer
   cabal --version     # expect: cabal-install version 3.12 or newer
   agda --version      # expect: Agda version 2.8.0
   python3 --version   # expect: Python 3.14 or newer
   ```
   If any of these are missing or older, install the recommended version before continuing — older toolchains have produced library-mismatch failures at FFI load time.
2. **First build** (~60s the first time, cached after):
   ```bash
   cabal run shake -- build        # builds libaletheia-ffi.so from Agda
   cd python && python3 -m venv .venv && source .venv/bin/activate
   pip install -e . && cd ..        # editable install of the Python binding
   ```
3. **Verify**: `python3 -c "from aletheia import AletheiaClient"` — no output means the `.so` was found and the binding loaded.

If any of those steps fail, the [Building Guide](../development/BUILDING.md) has a dedicated Troubleshooting section; the commands on this page assume a successful build.

---

## 1. Define Checks (YAML)

The demo ships `examples/demo/vehicle_checks.yaml` — three checks matched to the
signals in `examples/demo/vehicle.dbc`:

```yaml
checks:
  - name: "Speed limit"
    signal: VehicleSpeed
    condition: never_exceeds
    value: 120
    severity: safety

  - name: "Brake pressure in range"
    signal: BrakePressure
    condition: stays_between
    min: 0.0
    max: 6553.5
    severity: warning

  - name: "Acceleration bounded"
    signal: Acceleration
    condition: stays_between
    min: -32.768
    max: 32.767
    severity: warning
```

## 2. Run Against a CAN Log

```bash
cd examples/demo
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

## 3. Interpret Results

```
Aletheia — CAN Signal Verification

DBC:    vehicle.dbc
Checks: vehicle_checks.yaml (3 checks)
Log:    drive.log

Streaming 134 frames...

RESULT: 18 violations found

  1. [t=4710.000ms] Speed limit (safety)
     VehicleSpeed = 126 (formula: always(VehicleSpeed <= 120)) [core: Atomic: predicate failed]

  ... (18 violations total)

Summary: 18 violations, 0 unresolved in 3 checks, 134 frames processed
```

The overspeed segment of `drive.log` pushes `VehicleSpeed` past the 120 kph
limit, so the run reports 18 timestamped violations and exits `1`.

Exit codes: `0` = all passed, `1` = violations found, `2` = error.

Add `--json` for machine-readable output (CI/CD integration).

## 4. Alternatively: Use Python

```python
from fractions import Fraction

from aletheia import AletheiaClient, checks
from aletheia.dbc import dbc_to_json
from aletheia.can_log import iter_can_log

dbc = dbc_to_json("vehicle.dbc")
check_list = [
    checks.signal("VehicleSpeed").never_exceeds(120).severity("safety"),
    checks.signal("BrakePressure").stays_between(Fraction("0"), Fraction("6553.5")),
]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(check_list)
    client.start_stream()

    for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.log"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("type") == "property_batch":
            for entry in response["results"]:
                if entry.get("status") == "fails":
                    enrichment = entry.get("enrichment", {})
                    print(f"Violation: {enrichment.get('enriched_reason')}")

    client.end_stream()
```

---

## Next Steps

- **More check types**: [Interface Guide](../reference/INTERFACES.md) (YAML schema, Excel, Check API)
- **Full DSL**: [Python API Guide](../reference/PYTHON_API.md) (LTL operators, signal operations)
- **Recipes**: [Cookbook](COOKBOOK.md) (common patterns, copy-paste solutions)
- **Walkthroughs**: [Tutorials](TUTORIAL.md) (end-to-end paths by role)
- **CLI reference**: [CLI](../reference/CLI.md) (all subcommands and flags)

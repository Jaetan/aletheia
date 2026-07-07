# Cookbook

Problem-driven recipes. Each recipe is self-contained: title, code, done.

**Prerequisites**: A built Aletheia installation and a loaded DBC. See [Building Guide](../development/BUILDING.md) for setup. New to CAN / DBC / LTL terminology? Every term links back to the [Glossary](../GLOSSARY.md).

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
| Diagnose an error or unexpected result | [FAQ / Troubleshooting](#faq--troubleshooting) |

---

## Signal Bound Checks

### Signal never exceeds a value

```python
checks.signal("VehicleSpeed").never_exceeds(120)
```

```yaml
- signal: VehicleSpeed
  condition: never_exceeds
  value: 120
```

### Signal never drops below a value

```python
checks.signal("Acceleration").never_below(-30)
```

```yaml
- signal: Acceleration
  condition: never_below
  value: -30.0
```

### Signal stays in a range

```python
from fractions import Fraction

checks.signal("BrakePressure").stays_between(Fraction("0"), Fraction("6553.5"))
```

```yaml
- signal: BrakePressure
  condition: stays_between
  min: 0.0
  max: 6553.5
```

### Signal never equals a forbidden value

```python
# 655.35 kph is the 0xFFFF saturation reading — flag a pegged sensor.
checks.signal("VehicleSpeed").never_equals(Fraction("655.35"))
```

```yaml
- signal: VehicleSpeed
  condition: never_equals
  value: 655.35
```

### Signal settles into range within time

```python
checks.signal("Acceleration").settles_between(-1, 1).within(5000)
```

```yaml
- signal: Acceleration
  condition: settles_between
  min: -1.0
  max: 1.0
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
Signal("CoolantTemp").stable_within(2).always()
```

### Combine stability with a time window

```python
# After warmup, temperature must stabilize within ±1 degree
Signal("CoolantTemp").stable_within(1).within(30000)
```

---

## Causal / Response-Time Checks

### When A happens, B must follow within T ms

```python
checks.when("BrakePressure").exceeds(500) \
     .then("BrakeActive").equals(1) \
     .within(100)
```

```yaml
- name: "Brake response"
  when:
    signal: BrakePressure
    condition: exceeds
    value: 500
  then:
    signal: BrakeActive
    condition: equals
    value: 1
  within_ms: 100
```

### Engine must start within T ms of ignition

Illustrative — assumes a DBC that defines `Ignition` and `EngineRPM`; swap in
your own signals to run it against your bus.

```python
checks.when("Ignition").equals(1) \
     .then("EngineRPM").exceeds(500) \
     .within(2000)
```

### Signal settles after trigger

Illustrative — assumes a DBC that defines `FuelLevel` and `FuelWarning`.

```python
checks.when("FuelLevel").drops_below(10) \
     .then("FuelWarning").stays_between(1, 1) \
     .within(50)
```

---

## Working with CAN Logs

### Read a CAN log and check it (CLI)

```bash
cd examples/demo
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

Aletheia reads `.blf`, `.asc`, `.mf4`, `.csv`, `.db`, `.trc`, and candump `.log`
recordings — swap `drive.log` for your own capture (see
[Input Formats](../reference/CLI.md#input-formats)).

### Read a CAN log in Python (eager)

```python
from aletheia.can_log import load_can_log

frames = load_can_log("drive.log")
# frames is list[CANFrameTuple]; each entry is the 7-tuple
# (timestamp_us, can_id, dlc, data, extended, brs, esi).
```

### Process a large log lazily (streaming)

```python
from aletheia.can_log import iter_can_log

for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.log"):
    response = client.send_frame(ts, can_id, dlc, data)
```

### Skip error/remote frames (default) or include them

```python
# Default: error and remote frames are skipped
frames = load_can_log("drive.log")

# Include everything
frames = load_can_log("drive.log", skip_error_frames=False, skip_remote_frames=False)

# Strict mode: raise on corrupt frames instead of skipping
frames = load_can_log("drive.log", on_error="raise")
```

### Capture CAN traffic on Linux (candump)

For simulations running on Linux with a SocketCAN interface (real `canN` or virtual `vcanN`), `candump` from `can-utils` writes the `.log` format Aletheia reads natively — no conversion step.

> **Prerequisites.** `candump` ships in the `can-utils` package (`sudo apt install can-utils` on Debian/Ubuntu, or the equivalent for your distro). The `vcan` kernel module is in-tree on every supported Linux kernel; `modprobe vcan` is enough on a fresh system. Real CAN hardware does not need `vcan` — replace `vcan0` with the interface name your driver exposes (`can0`, etc.).

For the exact `modprobe` / `ip link` / `candump` sequence (and how to rotate captures into timestamped files), see [CLI Reference § Capturing CAN traffic on Linux](../reference/CLI.md#capturing-can-traffic-on-linux). Once you have a `.log`, replay it straight through Aletheia:

```bash
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

### Supported CAN log formats

See [CLI Reference § Input Formats](../reference/CLI.md#input-formats) for the full list of supported CAN log formats, their typical sources, and which commercial toolchains produce them natively.

---

## Working with DBC

### Load DBC from a .dbc file

```python
from aletheia.dbc import dbc_to_json

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
aletheia signals --dbc vehicle.dbc
```

### List signals as JSON

```bash
aletheia signals --dbc vehicle.dbc --json
```

---

## Validating a DBC

### Check a DBC for structural issues (CLI)

```bash
aletheia validate --dbc vehicle.dbc
```

The CLI exits **non-zero** when the DBC contains at least one `error`-severity
issue, **zero** when only `warning`-severity issues are present, and zero when
the DBC is clean. This makes `aletheia validate` safe to drop into CI as a
gating step.

### Interpret validation errors

```bash
aletheia validate --dbc vehicle.dbc --json | jq '.issues[]'
```

```json
{
  "severity": "error",
  "code": "signal_overlap",
  "detail": "EngineSpeed [bits 0:16] overlaps Throttle [bits 8:8] in EngineCmd"
}
```

The most common codes you'll see:

| Code | Meaning | Severity |
|---|---|---|
| `signal_overlap` | Two signals share at least one bit. | error |
| `signal_exceeds_dlc` | Signal's bit range extends past `DLC` bytes. | error |
| `multiplexor_not_found` | Multiplexed signal references an absent multiplexor. | error |
| `factor_zero` | `factor=0` makes physical-value extraction undefined. | error |
| `duplicate_message_id` | Two messages share the same CAN ID. | error |
| `unknown_message_sender` | `BU_` sender declared but not in node list. | warning |

The 21 IssueCode names are the authoritative cross-binding identifiers — see
`python/aletheia/codes/_issue.py` (mirror) or `src/Aletheia/DBC/Types.agda`
(SSOT) for the full enum. The full list lives in
[`PROTOCOL.md`](../architecture/PROTOCOL.md#error-code-reference). The structured `code` field
is the stable contract — `detail` text is for humans and may change between
releases.

---

## Signal Operations

### Extract all signals from a frame

```python
result = client.extract_signals(can_id=0x100, dlc=8, data=frame_bytes)
speed = result.get("VehicleSpeed")  # Fraction — extraction values are exact

# Check for errors and absent (multiplexed) signals
if result.has_errors():
    print(f"Errors: {result.errors}")
print(f"Absent: {result.absent}")
```

### Extract signals from CLI

```bash
aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
```

### Build a frame from signal values

```python
frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 72})
# Returns bytearray with VehicleSpeed encoded
```

### Inject modified signals during streaming

```python
client.start_stream()
for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.log"):
    # Modify speed to test property with altered values
    modified = client.update_frame(
        can_id=can_id, dlc=dlc, frame=data, signals={"VehicleSpeed": 130}
    )
    response = client.send_frame(ts, can_id, dlc, modified)
client.end_stream()
```

---

## CLI Recipes

### Run checks in CI/CD (exit codes + JSON)

```bash
aletheia check \
    --dbc vehicle.dbc \
    --checks vehicle_checks.yaml \
    --json \
    drive.log > results.json

# Exit code: 0=pass, 1=violations, 2=error
echo "Exit code: $?"
```

### Gate a merge on CAN checks (GitHub Actions)

Drop this workflow into `.github/workflows/can-checks.yml`. It installs Aletheia
from PyPI, runs the checks, and lets the exit code decide the job: `aletheia
check` returns `1` on a violation (and `2` on an error), and a non-zero step
fails the job automatically — so a regression in the recorded CAN behaviour
blocks the merge. The results are always uploaded, pass or fail, so you can
open `results.json` from the run's artifacts.

```yaml
name: CAN signal checks
on: [push, pull_request]

jobs:
  aletheia-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: actions/setup-python@v5
        with:
          python-version: "3.14"

      - name: Install Aletheia
        run: pip install aletheia   # ships the verified core; no build step needed

      - name: Run LTL checks
        run: |
          aletheia check \
            --json \
            --dbc vehicle.dbc \
            --checks checks.yaml \
            drive.log > results.json
        # Exit 0 = all passed; 1 = violations (fails the job); 2 = error (fails the job).

      - name: Upload results
        if: always()   # publish results.json even when the check step failed
        uses: actions/upload-artifact@v4
        with:
          name: aletheia-results
          path: results.json
```

### Decode a single frame

```bash
aletheia extract --dbc vehicle.dbc 0x100 "40 1F 7D 00 00 00 00 00"
```

### Use Excel workbook for everything

```bash
# DBC + checks from the same .xlsx
aletheia check --excel vehicle_checks.xlsx drive.log
```

### Mix DBC from .dbc with checks from .yaml

```bash
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

---

## Enriched Violations

### Enable enriched diagnostics

Enrichment is automatic when checks are registered via `add_checks()`:

```python
client.add_checks(check_list)
```

### Get signal values and formula from violations

```python
response = client.send_frame(ts, can_id, dlc, data)
if response.get("type") == "property_batch":
    for entry in response["results"]:
        if entry.get("status") == "fails":
            enrichment = entry.get("enrichment", {})
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
for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.log"):
    response = client.send_frame(ts, can_id, dlc, data)
    if response.get("type") == "property_batch":
        violations.extend(e for e in response["results"] if e.get("status") == "fails")

for entry in violations:
    ts_ms = entry["timestamp"] / 1000  # µs → ms (timestamp is a plain int)
    idx = entry["property_index"]        # plain int — registration order
    name = check_list[idx].name or f"Check #{idx}"
    reason = entry.get("enrichment", {}).get("enriched_reason", "?")
    print(f"[{ts_ms:.1f}ms] {name}: {reason}")
```

### Debug a single violation end-to-end

When a check fires unexpectedly, the goal is usually: which frame, which
signals, which sub-formula? The enriched response carries all three.

```python
import logging
from aletheia import AletheiaClient, checks, iter_can_log
from aletheia.dbc import dbc_to_json

# Surface backend lifecycle + violation events. The `aletheia` logger emits
# 16 structured event types — see PROTOCOL.md § Structured Logging.
logging.basicConfig(level=logging.INFO, format="%(name)s %(levelname)s %(message)s")

dbc = dbc_to_json("vehicle.dbc")
check_list = [checks.signal("Speed").never_exceeds(220).named("speed_limit")]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(check_list)
    client.start_stream()

    for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.log"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("type") != "property_batch":
            continue
        fails = [entry for entry in response["results"] if entry.get("status") == "fails"]
        if not fails:
            continue

        # Three things to look at, in order (first fails entry):
        e = fails[0]["enrichment"]

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
from pathlib import Path

from aletheia import checks, load_checks, load_checks_from_excel

check_list = []
check_list.extend(load_checks(Path("base_checks.yaml")))         # YAML (Path → file)
check_list.extend(load_checks_from_excel("extra_checks.xlsx"))   # Excel
check_list.append(checks.signal("Speed").never_exceeds(220))      # Check API

client.add_checks(check_list)
```

### Create an Excel template

```python
from aletheia import create_template
create_template("vehicle_checks.xlsx")
# Creates a file with three sheets: DBC, Checks, When-Then
```

---

## FAQ / Troubleshooting

*(draft — extend with real field questions.)* The failure modes below are the
ones users hit first. Unfamiliar terms (unresolved, arbitration ID, DLC, …) are
defined in the [Glossary](../GLOSSARY.md).

### `aletheia check` exited `2` — what does that mean?

Exit codes are uniform across every subcommand:

- `0` — success, or all checks passed (unresolved checks do **not** change this — see below).
- `1` — the run completed but found something: violations for `check`, or an `error`-severity issue for `validate`.
- `2` — Aletheia could not run at all: bad arguments, a missing or unreadable file, or a parse failure in the DBC, the check list, or the log.

So `2` means "fix the inputs", while `1` means "the inputs were fine but the CAN
data failed a rule". Full table: [CLI Reference § Overview](../reference/CLI.md#overview).

### A check shows up as "unresolved"

*Unresolved* means the stream ended while that check's verdict was still
*Unknown* — almost always because a signal it names was never observed in the
log (wrong DBC, wrong message ID, or the signal simply never transmitted).
Unresolved checks are neither passes nor violations: they are reported
separately and do not affect the exit code (still `0`). If you expected the
signal, confirm the DBC's message ID matches the log and that the log actually
carries that ID. Detail: [CLI Reference § Unresolved outcome](../reference/CLI.md#unresolved-outcome).

### `TypeError: a float is not exact …` when I build a check

Aletheia works in **exact rationals** — a Python `float` such as `0.1` is not
exact (it is really `0.1000000000000000055…`), so the API rejects it rather
than silently rounding your threshold. The message is:

```text
TypeError: a float is not exact; pass an int, a Fraction, or
from_decimal('...') for an exact decimal (the float principle)
```

Pass an `int` (already exact) or an exact `Fraction`:

```python
from fractions import Fraction

# Whole numbers are already exact:
checks.signal("VehicleSpeed").never_exceeds(120)

# For a decimal threshold, use Fraction("…") — NOT 0.1:
checks.signal("BrakePressure").never_below(Fraction("0.1"))
```

The same rule holds for YAML and Excel check files (a cell written `11.5` is
parsed as the exact decimal) and for every binding.

### The `.so` won't load

Symptoms: `aletheia_init() returned null`, an `hs_init` failure, or a
`FileNotFoundError` / `OSError` naming `libaletheia-ffi.so`. The binding could
not find or load the verified core. From a PyPI install (`pip install
aletheia`) the library ships inside the package and this should not happen. From
a **source checkout** you must build it first:

```bash
cabal run shake -- build       # produces build/libaletheia-ffi.so
```

Then either install it (`cabal run shake -- install`) or point every binding at
it explicitly with `ALETHEIA_LIB` — the same override the C++, Go, and Rust
bindings honour:

```bash
export ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

More causes and fixes: [Building Guide § Troubleshooting](../development/BUILDING.md#troubleshooting).

### `error: no such subcommand 'messages'`

The CLI has exactly six subcommands: `check`, `validate`, `extract`, `signals`,
`format-dbc`, `mux-query`. There is no `messages`, `decode`, or `run`. To list
what a DBC defines use `signals`; to decode a single frame use `extract`; to
inspect multiplexing use `mux-query`. Full reference:
[CLI Reference](../reference/CLI.md). (The C++ and Go host CLIs ship five of the
six — `check` is deferred there, pending a verified CAN-log reader — and the
Rust binding has a typed client but no CLI yet.)

---

## See Also

- **[Glossary](../GLOSSARY.md)** — plain-language CAN / DBC / LTL definitions
- **[Quick Start](QUICKSTART.md)** — 5-minute tutorial
- **[Tutorials](TUTORIAL.md)** — End-to-end walkthroughs by role
- **[Interface Guide](../reference/INTERFACES.md)** — Complete schema reference
- **[Python API Guide](../reference/PYTHON_API.md)** — Full DSL reference
- **[CLI Reference](../reference/CLI.md)** — All subcommands and flags

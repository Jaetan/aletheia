# Aletheia Interface Guide

**Purpose**: Guide to defining signal checks using the Check API, YAML, and Excel interfaces. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

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

Choose the simplest tier that covers your needs. The tiers compose without
restriction within a single session — for example, you can load DBC from an
Excel workbook, load a baseline check set from YAML, and append per-test
properties built with the Check API or raw DSL, all against the same
`AletheiaClient`. The bindings do not enforce any preferred ordering, and a
property loaded from one source is indistinguishable from one built in code.

### Binding parity

All three bindings (Python, C++, Go) share the same verified Agda core and the
same JSON protocol. Code snippets in this guide are in Python for brevity, but
the Check API, YAML loader, and DSL are available in every binding. The
following table summarizes feature availability per binding:

| Feature | Python | C++ | Go |
|---|---|---|---|
| Check API (`Check.signal(...).never_exceeds(...)`) | ✅ | ✅ (`aletheia::check::signal(...)`) | ✅ (`aletheia.CheckSignal(...)`) |
| Raw DSL / LTL property construction | ✅ | ✅ (`aletheia::ltl::...`) | ✅ (`aletheia.Always{Inner: ...}` struct literals) |
| YAML loader | ✅ (`load_checks`) | ✅ (`aletheia::yaml::load_checks`) | ✅ (`yaml.LoadChecks`) |
| Excel loader | ✅ (`load_checks_from_excel`) | ✅ (`aletheia::excel::...`) | ✅ (separate `go/excel/` module) |
| DBC JSON input (`dbc_to_json`) | ✅ | ✅ | ✅ |
| DBC text (`.dbc`) parsing | ✅ (via `cantools`) | ❌ (see workaround below) | ❌ (see workaround below) |
| Streaming `send_frame` / binary FFI | ✅ | ✅ | ✅ |

The same call, side by side across the three bindings:

**Check API** — "Speed must never exceed 220":
```python
Check.signal("Speed").never_exceeds(220)
```
```cpp
aletheia::check::signal("Speed").never_exceeds(aletheia::PhysicalValue{220});
```
```go
aletheia.CheckSignal("Speed").NeverExceeds(220)
```

**Raw DSL** — the same property built directly in LTL:
```python
Signal("Speed").less_than(220).always()
```
```cpp
aletheia::ltl::always(aletheia::ltl::less_than("Speed", aletheia::PhysicalValue{220}));
```
```go
aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.PhysicalValue(220)}}}
```

**YAML loader** — load a check file:
```python
checks = load_checks("checks.yaml")
```
```cpp
auto checks = aletheia::yaml::load_checks("checks.yaml");
```
```go
checks, err := yaml.LoadChecks("checks.yaml")
```

**Excel loader** — load checks from a workbook:
```python
checks = load_checks_from_excel("checks.xlsx")
```
```cpp
auto checks = aletheia::excel::load_checks("checks.xlsx");
```
```go
// requires the separate go/excel/ module
checks, err := excel.LoadChecks("checks.xlsx")
```

**Streaming** — feed a frame to the verified core:
```python
response = client.send_frame(ts, can_id, dlc, data)
```
```cpp
auto response = client.send_frame(ts, can_id, dlc, data);
```
```go
response, err := client.SendFrame(ts, canID, dlc, data)
```

These pairs are deliberately line-by-line equivalent — a regression in one binding that diverges from the others is a parity bug, not a design choice. See the [Distribution Guide § Loading the FFI library](../development/DISTRIBUTION.md) for the constructor boilerplate (`make_ffi_backend` / `NewFFIBackend` / `AletheiaClient(ffi_path=...)`) that sits one layer below these calls.

**`.dbc` text-format workaround for C++/Go.** Only Python parses `.dbc` text directly (via the `cantools` library). C++ and Go consume DBC content as a JSON document instead. Two routes are supported:

1. **Convert ahead of time with Python**:
   ```bash
   python3 -m aletheia signals --dbc vehicle.dbc --json > vehicle.json
   ```
   then load `vehicle.json` from C++ or Go and pass the parsed object to `parse_dbc(...)`.

2. **Use the Excel loader** (`.xlsx` workbook with a DBC sheet) — supported natively by all three bindings, no Python detour required.

Native `.dbc` parsing in C++ and Go is on the roadmap; until then, route through one of the above.

For language-specific entry points, see:

- **Python**: [`docs/reference/PYTHON_API.md`](PYTHON_API.md) for the full DSL reference and `AletheiaClient` usage.
- **C++**: header-level docs in `cpp/include/aletheia/*.hpp`, especially `check.hpp`, `client.hpp`, `ltl.hpp`, `yaml.hpp`, `excel.hpp`. The integration snippets in [`docs/development/DISTRIBUTION.md`](../development/DISTRIBUTION.md) show how to wire `make_ffi_backend` into a project.
- **Go**: run `go doc github.com/aletheia-automotive/aletheia-go/aletheia` for the package overview and per-type docs; the constructor is `NewFFIBackend` from `go/aletheia/ffi.go`.

---

## Check API

The Check API wraps the DSL with industry vocabulary. Each method returns a
`CheckResult` that can be named, given a severity, and serialized to the
same JSON that the verified Agda core processes.

```python
from aletheia import Check            # re-exported from aletheia.checks
```

Each `Check.…` call returns a `CheckResult` object; in real programs, collect the results into a list and pass them to `client.add_checks(...)`. The snippets below show one call per line so the fluent API surface is obvious; see the end-to-end example in the next section for how to wire them together.

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
# G_{<=5000ms}(80 <= temp <= 100)
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

**Semantics**: The timer starts when the 'when' condition transitions from false to true (rising edge). If 'then' becomes true within the deadline, the check passes for that window. If the 'when' condition triggers again later, a new independent window starts.

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
    client.add_checks(checks)
    client.start_stream()

    for timestamp, can_id, dlc, data in can_trace:
        response = client.send_frame(timestamp, can_id, dlc, data)
        if response.get("status") == "fails":
            enrichment = response.get("enrichment", {})
            print(f"Violation: {enrichment.get('enriched_reason')}")

    client.end_stream()
```

### Check API Reference

```python
class Check:
    @staticmethod
    def signal(name: str) -> CheckSignal
    @staticmethod
    def when(signal_name: str) -> WhenSignal

class CheckSignal:
    def never_exceeds(self, value: float) -> CheckResult
    def never_below(self, value: float) -> CheckResult
    def never_equals(self, value: float) -> CheckResult
    def stays_between(self, lo: float, hi: float) -> CheckResult
    def equals(self, value: float) -> CheckSignalPredicate
    def settles_between(self, lo: float, hi: float) -> SettlesBuilder

class CheckSignalPredicate:
    def always(self) -> CheckResult

class SettlesBuilder:
    def within(self, time_ms: int) -> CheckResult

class WhenSignal:
    def exceeds(self, value: float) -> WhenCondition
    def equals(self, value: float) -> WhenCondition
    def drops_below(self, value: float) -> WhenCondition

class WhenCondition:
    def then(self, signal_name: str) -> ThenSignal

class ThenSignal:
    def equals(self, value: float) -> ThenCondition
    def exceeds(self, value: float) -> ThenCondition
    def stays_between(self, lo: float, hi: float) -> ThenCondition

class ThenCondition:
    def within(self, time_ms: int) -> CheckResult

class CheckResult:
    def named(self, name: str) -> CheckResult
    def severity(self, level: str) -> CheckResult
    def to_dict(self) -> LTLFormula
    def to_property(self) -> Property
    name: str
    check_severity: str
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
client.add_checks(checks)
```

**String auto-detection**: `load_checks()` accepts either a file path or an inline YAML string. If the string is an existing file path, the file is loaded (file takes priority). Otherwise, it detects inline YAML when the input contains a newline (`\n`) or starts with `checks:`, `-`, `{`, or `[`. Strings that match neither are treated as a missing file path (`FileNotFoundError`).

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
| 0x100 | EngineData | 8 | EngineTemp | 16 | 8 | little_endian | FALSE | 1 | -40 | -40 | 215 | C |
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
    client.add_checks(checks)
    client.start_stream()

    for timestamp, can_id, dlc, data in can_trace:
        response = client.send_frame(timestamp, can_id, dlc, data)
        if response.get("status") == "fails":
            enrichment = response.get("enrichment", {})
            print(f"Violation: {enrichment.get('enriched_reason')}")

    client.end_stream()
```

### DBC Sheet Columns

| Column | Type | Required | Notes |
|--------|------|----------|-------|
| Message ID | int or hex string | yes | `0x100` or `256` |
| Message Name | string | yes | |
| DLC | int | yes | 0-15 (see [PROTOCOL.md](../architecture/PROTOCOL.md#1-parsedbc) for CAN-FD DLC-to-bytes mapping) |
| Signal | string | yes | Signal name |
| Start Bit | int | yes | 0-511 (CAN-FD) or 0-63 (standard CAN) |
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

**Sheet-name parameters**: Override the default sheet names when your workbook uses a different layout.

| Parameter | Default | Description |
|-----------|---------|-------------|
| `checks_sheet` | `"Checks"` | Sheet containing simple checks (one row per check) |
| `when_then_sheet` | `"When-Then"` | Sheet containing causal/response-time checks |
| `sheet` | `"DBC"` | Sheet containing signal definitions (for `load_dbc_from_excel`) |

---

## Condition Reference

All three interfaces (Check API, YAML, Excel) support the same conditions.

> **Note**: The LTL column shows the underlying formula for developers. If you're using the Check API, YAML, or Excel interface, you can ignore it — the condition name and Check API columns are all you need.

All conditions are documented in the [YAML Schema](#yaml-schema) section above. The Check API method names match the YAML condition names (e.g., YAML `never_exceeds` → Check API `.never_exceeds(v)`).

> **DSL-only predicates**: The full DSL provides additional predicates (`changed_by`, `stable_within`) not available as YAML/Excel conditions. These require frame-to-frame delta tracking and are accessed via `Signal("S").changed_by(delta)` and `Signal("S").stable_within(tolerance)`. See [Python API Guide — Change Detection](PYTHON_API.md#change-detection).

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

## Structured Logging

See [PROTOCOL.md § Structured Logging](../architecture/PROTOCOL.md#structured-logging) for the canonical event taxonomy (category × level × event-name table) — this section covers only the per-binding wiring.

**Python** — attach a handler to the `aletheia` logger:
```python
import logging
logging.getLogger("aletheia").setLevel(logging.INFO)
logging.getLogger("aletheia").addHandler(logging.StreamHandler())
```

**C++** — pass a `Logger` to `AletheiaClient`'s constructor (callback-based, zero-cost when absent):
```cpp
auto logger = aletheia::Logger{[](const aletheia::LogRecord& r) {
    std::cerr << r.event;
    for (const auto& f : r.fields) std::cerr << ' ' << f.key << '=' << f.value;
    std::cerr << '\n';
}};
auto client = aletheia::AletheiaClient{std::move(backend), std::move(logger)};
```

**Go** — `WithLogger` on `NewClient` for stream events; `WithFFILogger` on `NewFFIBackend` for FFI/RTS events:
```go
backend, _ := aletheia.NewFFIBackend(libPath, aletheia.WithFFILogger(slog.Default()))
client, _  := aletheia.NewClient(backend,  aletheia.WithLogger(slog.Default()))
```

**Emission point of `rts.cores_mismatch`.**  All three bindings emit the warning the second (and subsequent) time a process initialises the GHC RTS with a different `-N` value than the first call.  The exact moment differs by binding:

- **Go** — emitted from `NewFFIBackend` via the `WithFFILogger` slog handler.  Fires before any `Client` exists.
- **Python** — emitted from `LibraryHandle.acquire`, which runs during `AletheiaClient.__init__` (the FFI is acquired lazily on first client construction).  Goes through the module-level `aletheia` logger, so a Python application sees it via the standard `logging` configuration without per-client wiring.
- **C++** — captured at `make_ffi_backend()` time but emitted from the `AletheiaClient` constructor through the `Logger` passed to that constructor (the FFI backend has no logger of its own).  Wire one up to the client to observe it.

The wire format (`active_cores` and `requested_cores` as integer fields, level `WARNING`) is identical across bindings.  The choice of emission point is a layering trade-off: Go gives the FFI layer its own logger so backend-level events are observable without a client; Python relies on the global logging tree; C++ keeps the backend logger-free and routes everything through the client.

---

## See Also

- **[Python API Guide](PYTHON_API.md)** - Raw DSL (Signal, Predicate, Property) and AletheiaClient
- **[Demo scripts](../../examples/demo/)** - Runnable demos for each interface tier
- [BUILDING.md](../development/BUILDING.md) - Build instructions

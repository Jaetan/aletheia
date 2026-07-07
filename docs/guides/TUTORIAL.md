# Tutorials

End-to-end walkthroughs for each audience. Pick the path that matches your role.

| Path | Audience | Tools | Time |
|------|----------|-------|------|
| [Path 1: Technician](#path-1-technician-excel--cli) | Test technician | Excel + CLI | 15 min |
| [Path 2: Test Engineer](#path-2-test-engineer-yaml--cli) | Test engineer | YAML + CLI | 15 min |
| [Path 3: Python Scripter](#path-3-python-scripter-check-api) | Python developer | Check API | 20 min |
| [Path 4: Developer](#path-4-developer-full-dsl) | Software developer | Full DSL | 30 min |
| [Path 5: C++ Developer](#path-5-c-developer-client-api) | C++ developer | AletheiaClient (C++) | 30 min |
| [Path 6: Go Developer](#path-6-go-developer-client-api) | Go developer | Client (Go) | 30 min |
| [Path 7: Rust Developer](#path-7-rust-developer-client-api) | Rust developer | Client (Rust) | 30 min |

Paths 1–4 use the Python binding and CLI; Paths 5–7 cover the C++, Go, and Rust
bindings. All four are first-class — Python, C++, Go, and Rust ship the same
verified core with feature-equivalent APIs.

**Prerequisites for all paths**: Aletheia built and installed.
See [Building Guide](../development/BUILDING.md) and [Quick Start](QUICKSTART.md).

---

## Path 1: Technician (Excel + CLI)

Define checks in a spreadsheet, run them from the command line.
No Python coding required.

### Step 1: Create a Template

```bash
python3 -c "from aletheia import create_template; create_template('checks.xlsx')"
```

This creates an Excel workbook with three sheets: **DBC**, **Checks**, **When-Then**.

### Step 2: Fill in the DBC Sheet

Add one row per signal. Example:

| Message ID | Message Name | DLC | Signal | Start Bit | Length | Byte Order | Signed | Factor | Offset | Min | Max | Unit |
|-----------|-------------|-----|--------|-----------|--------|-----------|--------|--------|--------|-----|-----|------|
| 0x100 | VehicleDynamics | 8 | VehicleSpeed | 0 | 16 | little_endian | FALSE | 0.01 | 0 | 0 | 655.35 | kph |
| 0x100 | VehicleDynamics | 8 | Acceleration | 16 | 16 | little_endian | TRUE | 0.001 | 0 | -32.768 | 32.767 | m/s2 |
| 0x200 | BrakeStatus | 8 | BrakePressure | 0 | 16 | little_endian | FALSE | 0.1 | 0 | 0 | 6553.5 | kPa |
| 0x200 | BrakeStatus | 8 | BrakeActive | 16 | 1 | little_endian | FALSE | 1 | 0 | 0 | 1 | |

Multiple rows with the same Message ID are grouped into one message.
If you have a `.dbc` file from your customer, use `--dbc` instead (skip this sheet).

### Step 3: Fill in the Checks Sheet

| Check Name | Signal | Condition | Value | Min | Max | Time (ms) | Severity |
|-----------|--------|-----------|-------|-----|-----|-----------|----------|
| Speed limit | VehicleSpeed | never_exceeds | 120 | | | | safety |
| Brake pressure in range | BrakePressure | stays_between | | 0 | 6553.5 | | warning |

See [Interface Guide — Condition Reference](../reference/INTERFACES.md#condition-reference) for the full list of available conditions.

### Step 4: Fill in the When-Then Sheet (Optional)

The When-Then sheet is optional — leave it empty if you only need simple signal bounds.

For causal checks like "when X happens, Y must follow within T ms":

| Check Name | When Signal | When Condition | When Value | Then Signal | Then Condition | Then Value | Then Min | Then Max | Within (ms) | Severity |
|-----------|-----------|---------------|-----------|-----------|--------------|-----------|---------|---------|------------|----------|
| Brake response | BrakePressure | exceeds | 500 | BrakeActive | equals | 1 | | | 100 | safety |

### Step 5: Run Checks

The `--excel` flag loads DBC, Checks, and When-Then from the same workbook:

```bash
aletheia check --excel checks.xlsx drive.log
```

To see a full violating run end-to-end without authoring a workbook first, the
repository ships the equivalent split out into a plain `.dbc` plus a YAML checks
file — run that shipped demo trio directly:

```bash
cd examples/demo
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

### Step 6: Read Results

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

The overspeed segment of `drive.log` breaks the 120 kph `VehicleSpeed` limit, so
the run reports 18 timestamped violations and exits `1`.

Exit codes: `0` = all passed, `1` = violations found, `2` = error.
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
    value: 120
    severity: safety

  - name: "Brake pressure in range"
    signal: BrakePressure
    condition: stays_between
    min: 0.0
    max: 6553.5
    severity: warning

  # Bounded both sides (a signed signal)
  - name: "Acceleration bounded"
    signal: Acceleration
    condition: stays_between
    min: -32.768
    max: 32.767
    severity: warning

  # Time-bounded settling
  - name: "Acceleration settles"
    signal: Acceleration
    condition: settles_between
    min: -1.0
    max: 1.0
    within_ms: 5000
    severity: info

  # Causal check: when/then
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
    severity: safety
```

These checks name only the four signals in `examples/demo/vehicle.dbc`
(`VehicleSpeed`, `BrakePressure`, `Acceleration`, `BrakeActive`), so the whole
path runs end-to-end against the shipped demo.

### Step 2: Use a DBC File

Get the `.dbc` file from your customer or ECU vendor. Alternatively, define DBC
in an Excel workbook (see Path 1).

### Step 3: Run Checks

```bash
aletheia check --dbc vehicle.dbc --checks checks.yaml drive.log
```

The demo ships `examples/demo/vehicle.dbc` and `examples/demo/drive.log`; drop
your `checks.yaml` beside them (or use the shipped `vehicle_checks.yaml`) and run
from that directory.

### Step 4: JSON Output for CI/CD

```bash
aletheia check --dbc vehicle.dbc --checks checks.yaml drive.log --json
```

```json
{
  "status": "violations",
  "total_frames": 134,
  "total_violations": 18,
  "total_unresolved": 0,
  "violations": [
    {
      "check_index": 0,
      "check_name": "Speed limit",
      "severity": "safety",
      "timestamp_us": 4710000,
      "reason": "VehicleSpeed = 126 (formula: always(VehicleSpeed <= 120)) [core: Atomic: predicate failed]",
      "signal_name": "VehicleSpeed",
      "actual_value": 126,
      "condition": "always(VehicleSpeed <= 120)"
    }
  ],
  "unresolved": []
}
```

The `violations` array is abridged above to one of its 18 entries. This run
exits `1` — the overspeed frames break the speed limit; a clean recording exits
`0` with `"status": "pass"` and an empty `violations` array.

Use exit codes in CI: `0` = pass, `1` = violations, `2` = error.

```bash
# In CI script:
aletheia check --dbc vehicle.dbc --checks checks.yaml drive.log --json > results.json
if [ $? -ne 0 ]; then echo "Verification failed"; exit 1; fi
```

### Step 5: List Signals (Debugging)

```bash
# See what signals are available in the DBC
aletheia signals --dbc vehicle.dbc

# Decode a single frame
aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
```

---

## Path 3: Python Scripter (Check API)

Use the fluent Check API for programmatic verification.

### Step 1: Import and Define Checks

```python
from fractions import Fraction

from aletheia import AletheiaClient, checks
from aletheia.dbc import dbc_to_json
from aletheia.can_log import iter_can_log

# Define checks using industry vocabulary
check_list = [
    checks.signal("VehicleSpeed").never_exceeds(120)
        .named("Speed limit").severity("safety"),

    checks.signal("BrakePressure").stays_between(Fraction("0"), Fraction("6553.5"))
        .named("Brake pressure in range").severity("warning"),

    checks.signal("Acceleration").stays_between(Fraction("-32.768"), Fraction("32.767"))
        .named("Acceleration bounded").severity("warning"),
]
```

### Step 2: Simple Signal Checks

```python
# Upper bound
checks.signal("Speed").never_exceeds(220)        # G(speed < 220)

# Lower bound
checks.signal("Voltage").never_below(11)          # G(voltage >= 11)

# Range
checks.signal("Temp").stays_between(80, 100)     # G(80 <= temp <= 100)

# Equality
checks.signal("Fault").never_equals(255)         # G(not(fault == 255))

# Settling (time-bounded range)
checks.signal("Temp").settles_between(80, 100).within(5000)
```

### Step 3: When/Then Causal Checks

```python
# Brake light must activate within 100ms of pedal press
checks.when("BrakePedal").exceeds(50) \
     .then("BrakeLight").equals(1) \
     .within(100)

# Engine must start within 2s of ignition
checks.when("Ignition").equals(1) \
     .then("EngineRPM").exceeds(500) \
     .within(2000)
```

### Step 4: Stream CAN Frames

```python
dbc = dbc_to_json("vehicle.dbc")

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
                    print(f"VIOLATION: {enrichment.get('enriched_reason')}")
                    print(f"  Signals: {enrichment.get('signals')}")

    client.end_stream()
```

### Step 5: Handle Enriched Violations

When checks are registered via `add_checks()`, violation responses are automatically enriched with signal values, formula descriptions, and human-readable reasons. See [Python API Guide — Enriched Violations](../reference/PYTHON_API.md#enriched-violations) for the full response schema.

---

## Path 4: Developer (Full DSL)

Full LTL control with Signal, Predicate, and Property types.

### Step 1: Signal Predicates

```python
from fractions import Fraction

from aletheia import Signal

# Equality
Signal("Gear").equals(0)

# Comparisons
Signal("Speed").less_than(220)
Signal("Speed").greater_than(0)
Signal("Speed").less_than_or_equal(200)
Signal("Speed").greater_than_or_equal(60)

# Range — decimals are exact Fractions (the float principle: no float)
Signal("Voltage").between(Fraction("11.5"), Fraction("14.5"))

# Change detection: directional (sign of delta determines direction)
Signal("Speed").changed_by(-10)    # Speed decreased by 10+

# Stability: |now - prev| <= tolerance
Signal("Temperature").stable_within(2)  # Temperature stable within +/-2
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
Signal("DoorClosed").equals(1).within(100)         # F_{<=100ms}(door == 1)

# Duration: hold for at least T milliseconds
Signal("DoorClosed").equals(1).for_at_least(50)    # G_{<=50ms}(door == 1)
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
power_acc = Signal("PowerMode").equals(2).eventually()  # a Property (until's arg)
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
    result = client.extract_signals(can_id=0x100, dlc=8, data=frame_bytes)
    speed = result.get("VehicleSpeed", default=0.0)

    # Build a frame from signal values
    frame = client.build_frame(can_id=0x100, dlc=8, signals={"VehicleSpeed": 72})

    # Update specific signals in an existing frame
    modified = client.update_frame(
        can_id=0x100, dlc=8, frame=frame, signals={"VehicleSpeed": 130}
    )
```

### Step 6: Mixing Tiers

All tiers compile to the same LTL formulas. Mix freely:

```python
from pathlib import Path

from aletheia import checks, load_checks, Signal

# Load base checks from YAML
check_list = load_checks(Path("checks.yaml"))

# Add a Check API check
check_list.append(checks.signal("Speed").never_exceeds(220))

# Add a raw DSL property (wrap in CheckResult for metadata)
from aletheia import CheckResult
prop = Signal("Temp").between(-40, 215).always()
check_list.append(CheckResult(prop).named("Temp range"))

# All used the same way
client.add_checks(check_list)
```

---

## Path 5: C++ Developer (Client API)

Wrap the verified core in C++ through `AletheiaClient`. Every operation returns
`std::expected`, so each step is guarded. The five steps below are contiguous
slices of one `main()`; the assembled program is in
[CPP_API.md § End-to-End](../reference/CPP_API.md#end-to-end-parse-check-stream).

### Step 1: Build & Link Setup

The binding wraps `libaletheia-ffi.so` via `dlopen`. Build a backend from the
library path, hand it to an `AletheiaClient`, and open a `using namespace
aletheia;` (Steps 2–5 rely on it for the unqualified names):

```cpp
#include <aletheia/aletheia.hpp>
#include <aletheia/backend.hpp>
#include <array>
#include <string_view>

int main() {
    using namespace aletheia;
    auto backend = make_ffi_backend("/opt/aletheia/lib/libaletheia-ffi.so");
    auto client = AletheiaClient{std::move(backend)};
    std::stop_token stop;  // a real app threads a real token for cancellation
```

`make_ffi_backend(path, rts_cores)` takes an optional GHC RTS core count
(default 1). Packaging and the loader search order live in the
[Distribution Guide](../development/DISTRIBUTION.md).

### Step 2: Parse a DBC

Parse an inline DBC string with `parse_dbc_text` (a real app reads a `.dbc` file
into this string). Every `AletheiaClient` call takes the `std::stop_token` first:

```cpp
    constexpr std::string_view dbc = R"(VERSION ""
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
)";
    if (!client.parse_dbc_text(stop, dbc))
        return 0;
```

### Step 3: Register a Check

Build a check with the fluent `check::signal(...)` API and register it. Numeric
thresholds are **exact rationals** — `PhysicalValue{Rational{220, 1}}` is 220,
never a `double`:

```cpp
    std::vector<CheckResult> checks;  // CheckResult is move-only
    checks.push_back(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    if (!client.add_checks(stop, std::move(checks)))
        return 0;
```

### Step 4: Stream a Frame

Open the stream, then send frames. A real application pulls frames from a CAN
log; here one synthetic 8-byte frame stands in:

```cpp
    if (!client.start_stream(stop))
        return 0;

    std::array<std::byte, 8> payload{};
    auto sent = client.send_frame(stop, Timestamp{1000},
        CanId{StandardId::create(0x100).value()}, Dlc::create(8).value(), payload);
    (void)sent;
```

### Step 5: Read the Verdict

Close the stream. `end_stream` returns a `Result<StreamResult>`; on success,
`result->results` carries one finalization verdict per registered check:

```cpp
    auto result = client.end_stream(stop);  // Result<StreamResult>
    if (result) {
        // result->results carries one finalization verdict per registered check
    }
```

On any failure, read `error().kind()` / `error().code()` / `error().message()`;
`ErrorCode` mirrors the kernel's `IssueCode` enum
([PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

### CLI Boundary

The `aletheia-cli` host binary mirrors the Python `aletheia` subcommands but
ships **5 of the 6**: `validate`, `extract`, `signals`, `format-dbc`,
`mux-query`. `check` is deferred — it needs a verified CAN-log reader. Verify
either through the streaming API above, or with the flagship `check` on the
Python CLI:

```bash
cmake -S cpp -B cpp/build && cmake --build cpp/build --target aletheia-cli
ALETHEIA_LIB=build/libaletheia-ffi.so cpp/build/aletheia-cli validate --dbc vehicle.dbc
# `check` is deferred in the C++ host CLI; run the flagship check on the Python CLI:
aletheia check --dbc examples/demo/vehicle.dbc --checks examples/demo/vehicle_checks.yaml examples/demo/drive.log
```

---

## Path 6: Go Developer (Client API)

Wrap the verified core in Go through `Client`. Every operation takes a
`context.Context` first and returns an `error`. The five steps below are
contiguous slices of one `main()`; the assembled program is in
[GO_API.md § End-to-End](../reference/GO_API.md#end-to-end-parse-check-stream).

### Step 1: Build & Link Setup

The binding wraps `libaletheia-ffi.so` via cgo + `dlopen`. Build a backend from
the library path, hand it to a `Client`, `defer Close()`, and take a context:

```go
package main

import (
    "context"

    "github.com/aletheia-automotive/aletheia-go/aletheia"
)

func main() {
    backend, err := aletheia.NewFFIBackend("/opt/aletheia/lib/libaletheia-ffi.so")
    if err != nil {
        panic(err)
    }
    client, err := aletheia.NewClient(backend)
    if err != nil {
        panic(err)
    }
    defer client.Close()

    ctx := context.Background()
```

`NewFFIBackend` accepts functional options (`aletheia.WithRTSCores`,
`aletheia.WithFFILogger`); `NewClient` accepts `aletheia.WithLogger`. Packaging
and the loader search order live in the
[Distribution Guide](../development/DISTRIBUTION.md).

### Step 2: Parse a DBC

Parse an inline DBC string with `ParseDBCText` (a real app reads a `.dbc` file
into this string):

```go
    const dbc = `VERSION ""
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
`
    if _, err := client.ParseDBCText(ctx, dbc); err != nil {
        return
    }
```

### Step 3: Register a Check

Numeric thresholds are **exact rationals** — build them with
`aletheia.IntRational(n)` (never a `float64`):

```go
    speedLimit := aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
    checks := []aletheia.CheckResult{speedLimit}
    if err := client.AddChecks(ctx, checks); err != nil {
        return
    }
```

### Step 4: Stream a Frame

Open the stream, then send frames. A real application pulls frames from a CAN
log; here one synthetic 8-byte frame stands in:

```go
    if err := client.StartStream(ctx); err != nil {
        return
    }

    id, _ := aletheia.NewStandardID(0x100)
    dlc, _ := aletheia.NewDLC(8)
    data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
    _, _ = client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc, data, nil, nil)
```

### Step 5: Read the Verdict

Close the stream. `EndStream` returns `(*StreamResult, error)`; on success,
`result.Results` carries one verdict per registered check:

```go
    result, err := client.EndStream(ctx) // (*StreamResult, error)
    if err == nil {
        _ = result // result.Results carries one verdict per registered check
    }
```

On failure, `errors.As` a returned error into the typed `*aletheia.Error`
(`Kind`, `Code`, `Message`); `Code` mirrors the kernel's `IssueCode` enum
([PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

### CLI Boundary

The `cmd/aletheia` host binary mirrors the Python `aletheia` subcommands but
ships **5 of the 6**: `validate`, `extract`, `signals`, `format-dbc`,
`mux-query`. `check` is deferred — it needs a verified CAN-log reader. Verify
either through the streaming API above, or with the flagship `check` on the
Python CLI:

```bash
ALETHEIA_LIB=build/libaletheia-ffi.so go run ./cmd/aletheia signals --dbc vehicle.dbc
# or build a standalone binary: (cd go && go build -o aletheia ./cmd/aletheia)
# `check` is deferred in the Go host CLI; run the flagship check on the Python CLI:
aletheia check --dbc examples/demo/vehicle.dbc --checks examples/demo/vehicle_checks.yaml examples/demo/drive.log
```

---

## Path 7: Rust Developer (Client API)

Wrap the verified core in Rust through `Client`. Every fallible operation
returns `Result<_, aletheia::Error>`, and `send_frame` returns a typed
`FrameResponse` you `match` on — verdicts are read structurally, not from a JSON
dict. The steps below are contiguous slices of one `fn main()`; the assembled
program is in
[RUST_API.md § End-to-End](../reference/RUST_API.md#end-to-end-parse-check-stream).

### Step 1: Build & Link Setup

Add the crate as a path/git dependency (it is not published to crates.io), build
`libaletheia-ffi.so`, and point the binding at it with the `ALETHEIA_LIB`
environment variable:

```toml
# Cargo.toml
[dependencies]
aletheia = { path = "…" }
```

`Client::new()` loads the default library and returns a ready client (for RTS
cores / a logger use `Client::builder()`; for tests,
`Client::with_backend(Box::new(MockBackend::new()))` needs no `.so`):

```rust
use aletheia::{check, CanId, Client, Dlc, FrameResponse, Timestamp};

fn main() -> Result<(), aletheia::Error> {
    let client = Client::new()?;
```

### Step 2: Parse a DBC

Parse an inline DBC string with `parse_dbc_text` (a real app reads a `.dbc` file
into this string); it returns the parsed DBC plus any warnings:

```rust
    let dbc = r#"VERSION ""
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
"#;
    let (_dbc, _warnings) = client.parse_dbc_text(dbc)?;
```

### Step 3: Register a Check

Numeric thresholds are **exact rationals**; an `i64` literal converts directly —
`never_exceeds(220)` is 220, never an `f64`:

```rust
    client.add_checks(&[check::signal("Speed").never_exceeds(220)])?;
```

### Step 4: Stream a Frame

Open the stream and send a frame. `send_frame` returns a typed `FrameResponse`;
`match` it to read per-frame verdicts structurally (`FrameResponse::Verdicts`
carries a `Vec<PropertyResult>`):

```rust
    client.start_stream()?;

    let id = CanId::standard(0x100)?;
    let dlc = Dlc::new(8)?;
    let data = [0u8; 8];
    match client.send_frame(Timestamp(1_000), id, dlc, &data, None, None)? {
        FrameResponse::Ack => {}                    // fire-and-forget frame accepted
        FrameResponse::Verdicts(results) => {
            for r in &results {
                // r.property_index, r.verdict (Verdict::Fails on a violation),
                // and r.enrichment: Option<Enrichment> (.enriched_reason, .signals)
                let _ = r;
            }
        }
    }
```

### Step 5: Read the Verdict

Close the stream. `end_stream` returns a `StreamResult` with one finalization
verdict per registered check (plus warnings):

```rust
    let result = client.end_stream()?;              // StreamResult: one verdict per check + warnings
    let _ = result;
    Ok(())
}
```

On failure, `Error` is an enum you `match` directly — `Error::Core { code,
message }` mirrors the kernel's `IssueCode`; Rust has no dedicated `State` kind,
so wrong-lifecycle conditions surface as `Error::Protocol`
([PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

### CLI Boundary

Rust ships a typed `Client` but **no CLI yet** — a host CLI (and a Rust CAN-log
reader) are planned for Phase 6. Until then, feed frames from your own source or
`python-can` via IPC and verify through the streaming API above, or run the
flagship `check` on the Python CLI:

```bash
aletheia check --dbc examples/demo/vehicle.dbc --checks examples/demo/vehicle_checks.yaml examples/demo/drive.log
```

---

## See Also

- **[Quick Start](QUICKSTART.md)** — 5-minute path from zero to working verification
- **[Cookbook](COOKBOOK.md)** — Problem-driven recipes
- **[Interface Guide](../reference/INTERFACES.md)** — Complete Check API, YAML, Excel reference
- **[Python API Guide](../reference/PYTHON_API.md)** — Full DSL and AletheiaClient reference
- **[C++ API Guide](../reference/CPP_API.md)** — `AletheiaClient`, Check API, and LTL DSL (C++)
- **[Go API Guide](../reference/GO_API.md)** — `Client`, Check API, and LTL DSL (Go)
- **[Rust API Guide](../reference/RUST_API.md)** — `Client`, Check API, and LTL DSL (Rust)
- **[CLI Reference](../reference/CLI.md)** — All subcommands and flags

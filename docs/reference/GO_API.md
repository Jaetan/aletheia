# Aletheia Go API Guide

**Purpose**: Reference for Aletheia's Go binding: the `Client`, the Check API and the LTL DSL. The version it documents is in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

> **Exhaustive per-symbol docs** live as godoc comments in `go/aletheia/`: run `go doc github.com/aletheia-automotive/aletheia-go/aletheia`, or any symbol, such as `go doc aletheia.Client.SendFrame`. This guide is the narrative walkthrough and godoc is the contract.
>
> **Other bindings**: the [Python API Guide](PYTHON_API.md), the [C++ API Guide](CPP_API.md), the [Rust API Guide](RUST_API.md) and the [Interface Guide](INTERFACES.md). The four bindings ship the same verified core with line-by-line equivalent APIs.

---

## Contents

- [Setup](#setup)
- [Check API](#check-api)
- [LTL DSL](#ltl-dsl)
- [Core Types](#core-types)
- [End-to-End: Parse, Check, Stream](#end-to-end-parse-check-stream)
- [Signal Operations](#signal-operations)
- [Error Handling](#error-handling)
- [Cancellation](#cancellation)
- [Command-line interface](#command-line-interface)

---

## Setup

The binding wraps `libaletheia-ffi.so` via cgo + `dlopen`. Build a backend from the library path, hand it to a `Client`, and `defer Close()`:

```go
package main

import "github.com/aletheia-automotive/aletheia-go/aletheia"

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
    // ... use client (see below) ...
}
```

`NewFFIBackend` takes functional options, among them `aletheia.WithFFILogger` and `aletheia.WithRTSCores`, and `NewClient` takes `aletheia.WithLogger`. The backend is given a path and looks for none; the command-line interface below is what looks. Packaging, and where an installation puts the library, are in the [Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`aletheia.CheckSignal(name)` builds a property from a condition in plain English, and needs no temporal logic. A threshold is an exact `Rational`, never a `float64`: `aletheia.IntRational(n)` for a whole number, `aletheia.FromDecimal("0.25")` for a decimal. `NeverExceeds`, `NeverBelow` and `NeverEquals` cannot fail; `StaysBetween`, `SettlesBetween` and `.Within(ms)` answer `(CheckResult, error)`, refusing a lower bound above its upper one. Register the result with `AddChecks`:

```go
speedLimit := aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
gear := aletheia.CheckSignal("Gear").NeverEquals(aletheia.IntRational(-1))
// A range terminal refuses a lower bound above its upper one, so it answers an
// error and the caller reads it.
coolant, err := aletheia.CheckSignal("Coolant").StaysBetween(aletheia.IntRational(80), aletheia.IntRational(105))
if err != nil {
    panic(err)
}
_, _, _ = speedLimit, coolant, gear
```

A response-time check reads `CheckWhen(...).Then(...)` and closes with `.Within(ms)`. The result takes `.Named(...)` and `.Severity(...)`:

```go
// The deadline closes the check, and refuses one that is not positive.
brakeResponse, err := aletheia.CheckWhen("Brake").Exceeds(aletheia.IntRational(50)).
    Then("Decel").Exceeds(aletheia.IntRational(2)).Within(500)
if err != nil {
    panic(err)
}
brakeResponse = brakeResponse.Named("brake response").Severity("safety")
_ = brakeResponse
```

---

## LTL DSL

For full temporal control, build a formula from the types directly. Eight predicates say something about a signal: `Equals`, `LessThan`, `GreaterThan`, `LessThanOrEqual`, `GreaterThanOrEqual`, `Between`, `ChangedBy` and `StableWithin`. `Atomic` makes a formula of one, and formulas compose under `Not`, `And`, `Or`, `Next`, `WeakNext`, `Always`, `Eventually`, `Until` and `Release`. Four of those carry a deadline as `MetricAlways`, `MetricEventually`, `MetricUntil` and `MetricRelease`, and `Never`, `Implies`, `AlwaysWithin` and `EventuallyWithin` are free functions that build them. `aletheia.Signal(name)` builds the five comparisons fluently, as Python's `aletheia.dsl.Signal` does; the other three predicates are written as their own values.

```go
// always(Speed < 220)
alwaysSafe := aletheia.Always{Inner: aletheia.Atomic{
    Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}}}
// eventually(BrakePressed == 1)
brakesApply := aletheia.Eventually{Inner: aletheia.Atomic{
    Predicate: aletheia.Equals{Signal: "BrakePressed", Value: aletheia.IntRational(1)}}}
// The fluent Signal(...) builder is exact sugar for the bare predicate struct:
sameAsAbove := aletheia.Always{Inner: aletheia.Atomic{
    Predicate: aletheia.Signal("Speed").LessThan(aletheia.IntRational(220))}}
_, _, _ = alwaysSafe, brakesApply, sameAsAbove
```

Pass formulas to `client.SetProperties`, or `CheckResult`s to `client.AddChecks` (`CheckResult.Formula()` exposes the underlying formula).

---

## Core Types

Numeric fields are **exact rationals** (no floating-point drift). CAN IDs and DLC codes are validated newtypes constructed through factories that return an `error`:

```go
// A factory refuses a value outside its type's range, so a caller that builds
// one from input reads the error rather than discarding it.
id, err := aletheia.NewStandardID(0x100) // an 11-bit identifier
if err != nil {
    panic(err)
}
dlc, err := aletheia.NewDLC(8) // an eight-byte frame
if err != nil {
    panic(err)
}
factor := aletheia.IntRational(220) // the exact rational 220/1
_, _, _ = id, dlc, factor
```

Use `aletheia.NewExtendedID` for 29-bit IDs, and `aletheia.IntRational` (a whole number) or `aletheia.FromDecimal("0.25")` (an exact decimal, via the verified kernel) to build a `Rational`.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC, register checks, start the stream, send frames, end the stream**. Every operation takes a `context.Context` first and answers an `error`. A real application reads its frames from a CAN log and reports a refusal; this one stops at the first, so a failing step is visible. A DBC text needs its version line and the `NS_`, `BS_` and `BU_` sections: the parser refuses a text missing any of them, naming the line it stopped at.

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

    const dbc = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
`
    if _, err := client.ParseDBCText(ctx, dbc); err != nil {
        panic(err)
    }

    speedLimit := aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
    if err := client.AddChecks(ctx, []aletheia.CheckResult{speedLimit}); err != nil {
        panic(err)
    }
    if err := client.StartStream(ctx); err != nil {
        panic(err)
    }

    id, err := aletheia.NewStandardID(0x100)
    if err != nil {
        panic(err)
    }
    dlc, err := aletheia.NewDLC(8)
    if err != nil {
        panic(err)
    }
    data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
    if _, err := client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc, data, nil, nil); err != nil {
        panic(err)
    }

    result, err := client.EndStream(ctx)
    if err != nil {
        panic(err)
    }
    _ = result.Results // one verdict per registered check
}
```

---

## Signal Operations

A frame can be decoded and built directly, inside a stream or outside one. The `dlc` must match the payload's length:

- `ExtractSignals(ctx, id, dlc, data)` → `*ExtractionResult` (decode a frame).
- `BuildFrame(ctx, id, dlc, signals)` → `FramePayload` (encode signal values).
- `UpdateFrame(ctx, id, dlc, data, signals)` → `FramePayload` (patch a frame).

Decoding a frame and encoding one are inverses, and a `SignalValue` is a name beside an exact value:

```go
decoded, err := client.ExtractSignals(ctx, canID, dlc, data)
if err != nil {
	panic(err)
}
for _, value := range decoded.Values {
	fmt.Printf("%s = %s\n", value.Name, value.Value)
}

rebuilt, err := client.BuildFrame(ctx, canID, dlc, []aletheia.SignalValue{
	{Name: "VehicleSpeed", Value: aletheia.IntRational(72)},
})
if err != nil {
	panic(err)
}
fmt.Printf("encoded %d bytes\n", len(rebuilt))
```

See `go doc aletheia.Client` for the exact signatures.

---

## Error Handling

Every fallible operation answers `(value, error)` and the package never panics. Read an error with `errors.As` to reach the typed `*aletheia.Error` and its `Kind`, `Code` and `Message`:

```go
import (
    "errors"

    "github.com/aletheia-automotive/aletheia-go/aletheia"
)

func describe(err error) string {
    var aerr *aletheia.Error
    if errors.As(err, &aerr) {
        return aerr.Message
    }
    return err.Error()
}
```

`ErrorKind` says whether it was a validation, the protocol, an operation the binary wire lacks, or a cancellation. `Code` is the kernel's own, listed in [PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference).

---

## Cancellation

A cancelled context is observed at a frame boundary: the frames already processed stay committed, and the call answers the wrapped `ctx.Err()`. What the four bindings promise, through `asyncio`, `context.Context` and `std::stop_token`, is in the [Cancellation Contract](../architecture/CANCELLATION.md).

---

## Command-line interface

The `cmd/aletheia` package is a host interface over `Client`, carrying the subcommands `python -m aletheia` carries: `validate`, `extract`, `signals`, `format-dbc` and `mux-query`. It refuses `check` by name, which needs a CAN-log reader the binding does not provide. The dispatch is `run` in package `main`, exercised by `cmd/aletheia/main_test.go`.

```bash
# From the go/ directory, which is where the module is:
go run ./cmd/aletheia signals --dbc ../examples/example.dbc
# The interface finds the built library from there. To point it elsewhere:
ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so go run ./cmd/aletheia signals --dbc vehicle.dbc
# Or build the binary once: go build -o aletheia ./cmd/aletheia
```

The `--dbc` and `--json` flags, and `$ALETHEIA_LIB` ahead of the build tree, are what every binding's interface does. The subcommands are documented in the [CLI Reference](CLI.md), and godoc carries every symbol: `go doc github.com/aletheia-automotive/aletheia-go/aletheia`.


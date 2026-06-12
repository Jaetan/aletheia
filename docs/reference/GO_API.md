# Aletheia Go API Guide

**Purpose**: Reference for Aletheia's Go binding — the `Client`, the Check API,
and the LTL DSL. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

> **Exhaustive per-symbol docs** live as godoc comments in `go/aletheia/` — run
> `go doc github.com/aletheia-automotive/aletheia-go/aletheia` (or any symbol,
> e.g. `go doc aletheia.Client.SendFrame`). This guide is the narrative
> walkthrough; godoc is the contract.
> **Other bindings**: see the [Python API Guide](PYTHON_API.md), the
> [C++ API Guide](CPP_API.md), and the [Interface Guide](INTERFACES.md) — the
> three bindings ship the same verified core with line-by-line-equivalent APIs.

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
- [See Also](#see-also)

---

## Setup

The binding wraps `libaletheia-ffi.so` via cgo + `dlopen`. Build a backend from
the library path, hand it to a `Client`, and `defer Close()`:

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

`NewFFIBackend` accepts functional options (e.g. `aletheia.WithFFILogger`,
`aletheia.WithRTSCores`); `NewClient` accepts `aletheia.WithLogger`. Packaging
and the loader search order are covered in the
[Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`aletheia.CheckSignal(name)` builds a property from a fluent, plain-English
condition — the recommended starting point (no LTL knowledge required). Each
terminal returns a `CheckResult` you register with `AddChecks`. `PhysicalValue`
is a `float64`, so numeric literals work directly:

```go
speedLimit := aletheia.CheckSignal("Speed").NeverExceeds(220)
coolant, _ := aletheia.CheckSignal("Coolant").StaysBetween(80, 105) // (CheckResult, error)
gear := aletheia.CheckSignal("Gear").NeverEquals(-1)
_, _, _ = speedLimit, coolant, gear
```

Response-time / causal checks use `CheckWhen(...).Then(...)` and close with a
`.Within(ms)` deadline (returning `(CheckResult, error)`); a `CheckResult` can
then be `.Named(...)` and given a `.Severity(...)`:

```go
brakeResponse, _ := aletheia.CheckWhen("Brake").Exceeds(50).
    Then("Decel").Exceeds(2).Within(500) // decel must follow within 500 ms
brakeResponse = brakeResponse.Named("brake response").Severity("safety")
_ = brakeResponse
```

---

## LTL DSL

For full temporal control, build formulas directly from the LTL struct types.
Atomic predicates (`LessThan` / `GreaterThan` / `Equals`) compose under the
temporal operators (`Always` / `Eventually` / `Next` / `Until`); metric variants
(`AlwaysWithin` / `EventuallyWithin`) and `Never` / `Implies` are free functions:

```go
// always(Speed < 220)
alwaysSafe := aletheia.Always{Inner: aletheia.Atomic{
    Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}}}
// eventually(BrakePressed == 1)
brakesApply := aletheia.Eventually{Inner: aletheia.Atomic{
    Predicate: aletheia.Equals{Signal: "BrakePressed", Value: aletheia.IntRational(1)}}}
_, _ = alwaysSafe, brakesApply
```

Pass formulas to `client.SetProperties`, or `CheckResult`s to `client.AddChecks`
(`CheckResult.Formula()` exposes the underlying formula).

---

## Core Types

Numeric fields are **exact rationals** (no floating-point drift). CAN IDs and
DLC codes are validated newtypes constructed through factories that return an
`error`:

```go
id, _ := aletheia.NewStandardID(0x100) // 11-bit standard ID (StandardID, error)
dlc, _ := aletheia.NewDLC(8)           // 8-byte CAN 2.0B frame  (DLC, error)
factor := aletheia.IntRational(220)    // exact rational 220/1
_, _, _ = id, dlc, factor
```

Use `aletheia.NewExtendedID` for 29-bit IDs, and `aletheia.IntRational` (exact)
or `aletheia.RationalFromFloat` to build a `Rational`.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC → register checks → start the stream →
send frames → end the stream**. Every operation takes a `context.Context` first
and returns an `error`, so each step is guarded; a real application pulls frames
from a CAN log instead of synthesizing them:

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
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
`
    if _, err := client.ParseDBCText(ctx, dbc); err != nil {
        return
    }

    checks := []aletheia.CheckResult{
        aletheia.CheckSignal("Speed").NeverExceeds(220),
    }
    if err := client.AddChecks(ctx, checks); err != nil {
        return
    }
    if err := client.StartStream(ctx); err != nil {
        return
    }

    id, _ := aletheia.NewStandardID(0x100)
    dlc, _ := aletheia.NewDLC(8)
    data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
    _, _ = client.SendFrame(ctx, aletheia.Timestamp{Microseconds: 1000}, id, dlc, data, nil, nil)

    result, err := client.EndStream(ctx) // (*StreamResult, error)
    if err == nil {
        _ = result // result.Results carries one verdict per registered check
    }
}
```

---

## Signal Operations

Outside (or inside) streaming, decode and synthesize frames directly. `dlc` must
match the payload length; each method takes `ctx` first and returns an `error`:

- `ExtractSignals(ctx, id, dlc, data)` → `*ExtractionResult` (decode a frame).
- `BuildFrame(ctx, id, dlc, signals)` → `FramePayload` (encode signal values).
- `UpdateFrame(ctx, id, dlc, data, signals)` → `FramePayload` (patch a frame).

See `go doc aletheia.Client` for exact signatures and [INTERFACES.md](INTERFACES.md)
for a worked extract/build round-trip.

---

## Error Handling

Every fallible operation follows Go's `(value, error)` convention — there are no
panics on the normal path. Inspect a returned error with `errors.As` to read the
typed `*aletheia.Error` (`Kind`, `Code`, `Message`):

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

`ErrorKind` distinguishes validation / protocol / binary-unsupported /
cancellation; `Code` mirrors the kernel's `IssueCode` enum (see
[PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

---

## Cancellation

Every `Client` operation takes a `context.Context` as its first parameter.
Cancelling the context is observed at frame boundaries with the
commit-prefix-and-report contract — already-processed frames stay committed, and
the wrapped `ctx.Err()` is returned. The cross-binding semantics (Python
`asyncio`, Go `context.Context`, C++ `std::stop_token`) are specified in the
[Cancellation Contract](../architecture/CANCELLATION.md).

---

## Command-line interface

The `cmd/aletheia` package is a thin host CLI over `Client`, mirroring the
Python `aletheia` subcommands — `validate`, `extract`, `signals`, `format-dbc`,
`mux-query` (`check` is deferred; it needs a verified CAN-log reader). The
dispatch logic lives in `run` (package `main`), exercised by
`cmd/aletheia/main_test.go`.

```bash
ALETHEIA_LIB=build/libaletheia-ffi.so go run ./cmd/aletheia signals --dbc vehicle.dbc
# or build a standalone binary: (cd go && go build -o aletheia ./cmd/aletheia)
```

`--dbc` reads `.dbc` text (the verified Agda text parser); `--json` selects
canonical JSON output. The library path resolves from `$ALETHEIA_LIB`, else a
build/install default. Full subcommand contract: the [CLI Reference](CLI.md).

---

## See Also

- **[Interface Guide](INTERFACES.md)** — Check API, YAML, and Excel loaders (cross-binding)
- **[Distribution Guide](../development/DISTRIBUTION.md)** — packaging + `NewFFIBackend` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)** — wire-level command/response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)** — `context.Context` semantics
- godoc: `go doc github.com/aletheia-automotive/aletheia-go/aletheia` (the exhaustive per-symbol contract)

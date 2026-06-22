# Aletheia C++ API Guide

**Purpose**: Reference for Aletheia's C++ binding — the `AletheiaClient`, the
Check API, and the raw LTL DSL. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

> **Exhaustive per-symbol docs** live as doc-comments in the public headers
> under `cpp/include/aletheia/` — especially `client.hpp`, `check.hpp`,
> `ltl.hpp`, `types.hpp`, `dbc.hpp`, `yaml.hpp`, `excel.hpp`, and `error.hpp`.
> This guide is the narrative walkthrough; the headers are the contract.
> **Other bindings**: see the [Python API Guide](PYTHON_API.md) and the
> [Interface Guide](INTERFACES.md) — the three bindings ship the same verified
> core with line-by-line-equivalent APIs.

The C++ binding targets the latest stable Clang only — see
[BUILDING.md § Toolchain support policy](../development/BUILDING.md#toolchain-support-policy).

---

## Contents

- [Setup](#setup)
- [Check API](#check-api)
- [Raw LTL DSL](#raw-ltl-dsl)
- [Core Types](#core-types)
- [End-to-End: Parse, Check, Stream](#end-to-end-parse-check-stream)
- [Signal Operations](#signal-operations)
- [Error Handling](#error-handling)
- [Cancellation](#cancellation)
- [Command-line interface](#command-line-interface)
- [See Also](#see-also)

---

## Setup

The binding wraps `libaletheia-ffi.so` via `dlopen`. Construct a backend from the
library path, then hand it to an `AletheiaClient`:

```cpp
#include <aletheia/client.hpp>
#include <aletheia/backend.hpp>

int main() {
    auto backend = aletheia::make_ffi_backend("/opt/aletheia/lib/libaletheia-ffi.so");
    auto client = aletheia::AletheiaClient{std::move(backend)};
    // ... use client (see below) ...
}
```

`make_ffi_backend(path, rts_cores)` accepts an optional GHC RTS core count
(default 1). The loader search order and packaging are covered in the
[Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`check::signal(name)` builds a property from a fluent, plain-English condition —
the recommended starting point (no LTL knowledge required). Each terminal
returns a `CheckResult` you register with `add_checks`.

```cpp
using namespace aletheia;
auto speed_limit = check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}});
auto coolant = check::signal("Coolant").stays_between(
    PhysicalValue{Rational{80, 1}}, PhysicalValue{Rational{105, 1}});
auto gear = check::signal("Gear").never_equals(PhysicalValue{Rational{-1, 1}});
(void)speed_limit;
(void)coolant;
(void)gear;
```

Response-time / causal checks use `check::when(...).then(...)`:

```cpp
using namespace aletheia;
auto brake_response = check::when("Brake").exceeds(PhysicalValue{Rational{50, 1}})
                          .then("Decel").exceeds(PhysicalValue{Rational{2, 1}});
(void)brake_response;
```

---

## Raw LTL DSL

For full temporal control, build formulas directly with `ltl::`. Atomic
predicates (`equals` / `less_than` / `greater_than` / `less_than_or_equal` /
`greater_than_or_equal`) compose under the temporal operators (`always` /
`eventually` / `next` / `until`):

```cpp
using namespace aletheia;
// always(Speed < 220)
auto always_safe = ltl::always(ltl::atomic(
    ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
// always(Speed <= 220) — inclusive variant
auto always_le = ltl::always(ltl::atomic(
    ltl::less_than_or_equal(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
// eventually(BrakePressed == 1)
auto brakes_apply = ltl::eventually(ltl::atomic(
    ltl::equals(SignalName{"BrakePressed"}, PhysicalValue{Rational{1, 1}})));
(void)always_safe;
(void)always_le;
(void)brakes_apply;
```

---

## Core Types

Numeric fields are **exact rationals** (no floating-point drift). CAN IDs and
DLC codes are validated newtypes constructed through factory functions that
return `std::expected`:

```cpp
using namespace aletheia;
auto id = CanId{StandardId::create(0x100).value()};   // 11-bit standard ID
auto dlc = Dlc::create(8).value();                     // 8-byte CAN 2.0B frame
auto factor = Rational{1, 10};                         // exact 0.1
auto threshold = PhysicalValue{Rational{2200, 10}};    // 220.0 km/h
(void)id;
(void)dlc;
(void)factor;
(void)threshold;
```

Prefer the rational constructors over `double`: `Rational{1, 10}` is exact where
`0.1` is not.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC → register checks → start the stream →
send frames → end the stream**. Every operation returns `std::expected`, so each
step is guarded; a real application pulls frames from a CAN log instead of
synthesizing them:

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

    constexpr std::string_view dbc = R"(VERSION ""
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
)";
    if (!client.parse_dbc_text(stop, dbc))
        return 0;

    std::vector<CheckResult> checks;  // CheckResult is move-only
    checks.push_back(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    if (!client.add_checks(stop, std::move(checks)))
        return 0;
    if (!client.start_stream(stop))
        return 0;

    std::array<std::byte, 8> payload{};
    auto sent = client.send_frame(stop, Timestamp{1000},
        CanId{StandardId::create(0x100).value()}, Dlc::create(8).value(), payload);
    (void)sent;

    auto result = client.end_stream(stop);  // Result<StreamResult>
    if (result) {
        // result->results carries one finalization verdict per registered check
    }
}
```

---

## Signal Operations

Outside (or inside) streaming, decode and synthesize frames directly. `dlc`
must match the payload length (`dlc_to_bytes(dlc)`); each method returns
`std::expected`:

- `extract_signals(stop, id, dlc, data)` → `ExtractionResult` (decode a frame).
- `build_frame(stop, id, dlc, signals)` → `FramePayload` (encode signal values).
- `update_frame(stop, id, dlc, data, signals)` → `FramePayload` (patch a frame).

See `cpp/include/aletheia/client.hpp` for the exact signatures and
[INTERFACES.md](INTERFACES.md) for a worked extract/build round-trip.

---

## Error Handling

Every fallible operation returns `aletheia::Result<T>` (`std::expected<T,
AletheiaError>`) — there are no exceptions on the normal path. Check
`has_value()` / use `operator bool`, and read `error().kind()`,
`error().code()`, and `error().message()` on failure:

```cpp
using namespace aletheia;
// Given a `Result<T>` named `r` from any client call:
auto describe = [](const AletheiaError& e) -> std::string_view {
    return e.message();
};
(void)describe;
```

`ErrorKind` distinguishes `Validation` / `Protocol` / `BinaryUnsupported` /
`Cancellation` / etc.; `ErrorCode` mirrors the kernel's `IssueCode` enum (see
[PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

---

## Cancellation

Every `AletheiaClient` operation takes a `std::stop_token` as its first
parameter. Requesting a stop is observed at frame boundaries with the
commit-prefix-and-report contract — already-processed frames stay committed.
The cross-binding semantics (Python `asyncio`, Go `context.Context`, C++
`std::stop_token`) are specified in the
[Cancellation Contract](../architecture/CANCELLATION.md).

---

## Command-line interface

The `aletheia-cli` binary is a thin host CLI over `AletheiaClient`, mirroring
the Python `aletheia` subcommands — `validate`, `extract`, `signals`,
`format-dbc`, `mux-query` (`check` is deferred; it needs a verified CAN-log
reader). The logic lives in `aletheia::run_cli` (`aletheia/cli.hpp`), so it is
unit-testable without spawning a process.

```bash
cmake -S cpp -B cpp/build && cmake --build cpp/build --target aletheia-cli
ALETHEIA_LIB=build/libaletheia-ffi.so cpp/build/aletheia-cli validate --dbc vehicle.dbc
```

`--dbc` reads `.dbc` text (the verified Agda text parser); `--json` selects
canonical JSON output. The library path resolves from `$ALETHEIA_LIB`, else a
build/install default. Full subcommand contract: the [CLI Reference](CLI.md).

---

## See Also

- **[Interface Guide](INTERFACES.md)** — Check API, YAML, and Excel loaders (cross-binding)
- **[Distribution Guide](../development/DISTRIBUTION.md)** — packaging + `make_ffi_backend` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)** — wire-level command/response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)** — `std::stop_token` semantics
- Public headers: `cpp/include/aletheia/*.hpp` (the exhaustive per-symbol contract)

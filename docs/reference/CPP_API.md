# Aletheia C++ API Guide

**Purpose**: Reference for Aletheia's C++ binding, covering the `AletheiaClient`, the Check API, and the raw LTL DSL. Version in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

> **Exhaustive per-symbol docs** live as doc-comments in the public headers under `cpp/include/aletheia/`, especially `client.hpp`, `check.hpp`, `ltl.hpp`, `types.hpp`, `dbc.hpp`, `yaml.hpp`, `excel.hpp`, and `error.hpp`. This guide is the narrative walkthrough; the headers are the contract.
>
> **Other bindings**: see the [Python API Guide](PYTHON_API.md), the [Go API Guide](GO_API.md), the [Rust API Guide](RUST_API.md), and the [Interface Guide](INTERFACES.md). The four bindings ship the same verified core with line-by-line-equivalent APIs.

The C++ binding targets the latest stable Clang only. See [BUILDING.md § Toolchain support policy](../development/BUILDING.md#toolchain-support-policy).

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

The binding wraps `libaletheia-ffi.so` via `dlopen`. `AletheiaClient::open` opens a client over it in one call, returning a `Result` as every call the binding answers does:

```cpp
#include <aletheia/client.hpp>
#include <aletheia/backend.hpp>
#include <iostream>

int main() {
    auto client = aletheia::AletheiaClient::open({.library = "/opt/aletheia/lib/libaletheia-ffi.so"});
    if (!client) {
        std::cerr << client.error().text() << '\n';
        return 1;
    }
    // ... use client-> (see below) ...
}
```

Every field of `ClientOptions` may be left out: an empty `.library` is the one `find_ffi_library()` finds (`ALETHEIA_LIB`, then a path a start or a backend registered, then the build directories), and the search's refusal is `open`'s, kind `Ffi`: an `ALETHEIA_LIB` naming no file (`ALETHEIA_LIB=<path> does not exist`) or no library found; `.rts_cores` unset asks for the GHC runtime's count running, 1 when nothing runs, a runtime already up keeping its own count and the difference logged as `rts.cores_mismatch` through `.logger`; `.default_checks` are applied by every `add_checks`. `open` is `make_ffi_backend(path)` or `make_ffi_backend(path, rts_cores)`, then `AletheiaClient::create(backend, logger, default_checks)`, each callable alone, `create` taking any `IBackend`. The loader search order and packaging are covered in the [Distribution Guide](../development/DISTRIBUTION.md).

The kernel reads every number a check carries, through `Rational::from_decimal` and the YAML and Excel loaders, on a GHC runtime that starts once per process: by `aletheia::start_runtime(lib, cores)`, or `start_runtime_from_env(cores)` on the library `ALETHEIA_LIB` names, or by the first backend. A program that loads checks before it builds a client starts the runtime first; before any start, `Rational::from_decimal` returns an error of kind `Ffi` (`GHC runtime not initialized: call aletheia::start_runtime or open a client before parsing decimals`), and a loader returns that error, unlocated. `cores` is the runtime's capability count, 1 for one bus; a count outside 1 to the CPUs the process may use is refused with kind `Validation`. A runtime already up keeps its count, and the start then answers `{active, requested}` when the two differ, `std::nullopt` otherwise.

```cpp
if (!aletheia::start_runtime_from_env(1))
    return 1;
auto checks = aletheia::load_checks_from_yaml("checks.yaml");
if (!checks)
    return 1;
auto defaults = aletheia::AletheiaClient::open({.default_checks = std::move(checks).value()});
```

---

## Check API

`check::signal(name)` builds a property from a fluent, plain-English condition, the recommended starting point (no LTL knowledge required). Each terminal returns a `CheckResult` you register with `add_checks`, and `stays_between` a `Result<CheckResult>`, refusing with kind `Validation` a lo above its hi.

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

Response-time / causal checks use `check::when(...).then(...)`. Their `within`, and `settles_between`'s, returns `Result<CheckResult>`, refusing with kind `Validation` a `stays_between` or `settles_between` range whose lo is above its hi, a negative bound, or one whose microseconds overflow int64:

```cpp
using namespace aletheia;
auto brake_response = check::when("Brake").exceeds(PhysicalValue{Rational{50, 1}})
                          .then("Decel").exceeds(PhysicalValue{Rational{2, 1}})
                          .within(std::chrono::milliseconds{500});
if (!brake_response)
    return 1;
```

A check's `condition_desc()` is its condition in words, every threshold rendered by the kernel on each read: a `Result<std::string>`, kind `Ffi` while the runtime is down.

---

## Raw LTL DSL

For full temporal control, build formulas directly with `ltl::`. A predicate compares a signal against a value (`equals`, `less_than`, `greater_than`, `less_than_or_equal`, `greater_than_or_equal`), against a range (`between`), or against its own recent history (`changed_by`, `stable_within`). `atomic` lifts one into a formula, and formulas compose under the boolean constructors (`negate`, `both`, `either`, `implies`) and the temporal ones (`next`, `weak_next`, `always`, `eventually`, `until`, `release`, and the time-bounded `within` and `always_within`). `never(p)` is the shorthand for an always-negated predicate:

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

Numeric fields are **exact rationals**: `Rational{1, 10}` is a tenth exactly, where the `double` `0.1` is not. The two-argument constructor takes constants only, so a pair outside int64 or a denominator that is not positive fails the build; a pair known at run time goes through `Rational::make(n, d)`, which returns `Result<Rational>`, and a whole number through `Rational::integer(n)`, which cannot fail. CAN IDs and DLC codes are validated newtypes constructed through factory functions that return `std::expected`:

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

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC → register checks → start the stream → send frames → end the stream**. Every operation returns `std::expected`, so each step is guarded and a failing step stops the program with the kernel's own message; a real application pulls frames from a CAN log instead of synthesizing them:

```cpp
#include <aletheia/aletheia.hpp>
#include <aletheia/backend.hpp>
#include <array>
#include <iostream>
#include <string_view>
#include <vector>

int main() {
    using namespace aletheia;
    std::stop_token stop;  // a real app threads a real token for cancellation
    auto fail = [](std::string_view step, const AletheiaError& e) {
        std::cerr << step << ": " << e.text() << '\n';
        return 1;
    };
    auto opened = AletheiaClient::open({.library = "/opt/aletheia/lib/libaletheia-ffi.so"});
    if (!opened)
        return fail("opening the client", opened.error());
    auto& client = *opened;

    constexpr std::string_view dbc = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
)";
    if (auto parsed = client.parse_dbc_text(stop, dbc); !parsed)
        return fail("parse_dbc_text", parsed.error());

    std::vector<CheckResult> checks;  // CheckResult is move-only
    checks.push_back(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    if (auto added = client.add_checks(stop, std::move(checks)); !added)
        return fail("add_checks", added.error());
    if (auto started = client.start_stream(stop); !started)
        return fail("start_stream", started.error());

    std::array<std::byte, 8> payload{};
    if (auto sent = client.send_frame(stop, Timestamp{1000},
            CanId{StandardId::create(0x100).value()}, Dlc::create(8).value(), payload);
        !sent)
        return fail("send_frame", sent.error());

    auto result = client.end_stream(stop);  // Result<StreamResult>
    if (!result)
        return fail("end_stream", result.error());
    // result->results carries one finalization verdict per registered check
}
```

---

## Signal Operations

Outside (or inside) streaming, decode and synthesize frames directly. `dlc` must match the payload length (`dlc_to_bytes(dlc)`); each method returns `std::expected`:

- `extract_signals(stop, id, dlc, data)` → `ExtractionResult` (decode a frame).
- `build_frame(stop, id, dlc, signals)` → `FramePayload` (encode signal values).
- `update_frame(stop, id, dlc, data, signals)` → `FramePayload` (patch a frame).

Each value is written exactly or refused: one outside the signal's declared range fails with code `frame_value_out_of_range`, one that no integer raw value scales to under the signal's factor and offset with `frame_value_not_representable`, and two requested signals sharing a bit with `frame_signals_overlap`. A written value reads back unchanged wherever the frame carries its signal: always, or for a multiplexed signal when its multiplexor's value selects it.

A `SignalValue` is a name beside an exact value:

```cpp
using namespace aletheia;
auto decoded = client.extract_signals(std::stop_token{}, can_id, dlc, data);
if (decoded)
    for (auto const& value : decoded->values)
        std::cout << value.name.get() << " = " << value.value.get().numerator() << '\n';

std::vector<SignalValue> injected{
    SignalValue{SignalName{"VehicleSpeed"}, PhysicalValue{Rational{72, 1}}}};
auto rebuilt = client.build_frame(std::stop_token{}, can_id, dlc, injected);
if (rebuilt)
    std::cout << "encoded " << rebuilt->size() << " bytes\n";
```

---

## Error Handling

Every fallible operation returns `aletheia::Result<T>` (`std::expected<T, AletheiaError>`), from opening the runtime, a backend and a client to the last frame; the one exception the binding throws is `std::bad_alloc`. Check `has_value()` / use `operator bool`, and read `error().kind()`, `error().code()` and `error().text()` on failure:

```cpp
using namespace aletheia;
// Given a `Result<T>` named `r` from any client call:
auto describe = [](const AletheiaError& e) -> std::string {
    return e.text();
};
(void)describe;
```

`message()` is the refusal's own text: for a refusal the kernel made, the kernel's message verbatim, the binding only typing it with `kind()`, `code()` and the fields the kernel's answer carries. `text()` is the error as every binding prints it.

A decimal the YAML or Excel loader reads, such as a check's value or a signal's factor, is handed to the kernel as the document spells it (a workbook cell's text with its leading and trailing whitespace trimmed), and a refusal of it, the kernel's or the shared library's, keeps its kind, code and fields: kind `Validation` with its code, or kind `InputBoundExceeded` with `bound_info()`. The loader adds `location()`, `Check '<name>'` for a YAML check (`<unnamed>` for a check without a name) and `Row <n>` for a workbook row, and `key()`, the YAML key or the column header the number sat under, through `located(location, key)`, so `text()` reads `<location>: invalid '<key>': <message>`. Every other error leaves both `std::nullopt`, and its `text()` is its `message()`. The same document gets the same answer in every binding: [LOADER_SCENARIOS.yaml](../LOADER_SCENARIOS.yaml) is that contract.

<!-- refuses: text_parse_failure -->
```cpp
if (!aletheia::start_runtime_from_env(1))  // the kernel reads every number
    return 1;
auto const refused = aletheia::load_checks_from_yaml_string(
    "checks:\n  - name: C\n    signal: Speed\n    condition: never_exceeds\n    value: .5\n");
if (refused || refused.error().text() !=
                   "Check 'C': invalid 'value': parse failed at line 1, column 1")
    return 1;
```

`ErrorKind` is one of `Protocol`, `Validation`, `State`, `Ffi`, `BinaryUnsupported`, `Cancellation`, `InputBoundExceeded` and `TextRoundtrip`; `ErrorCode` mirrors the kernel's error codes and `FfiValidationError`, the shared library's refusal of an entry's arguments (see [PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

A DBC past one of the size bounds in `<aletheia/limits.hpp>` is refused with kind and code `InputBoundExceeded` by every command that takes one: `parse_dbc`, `parse_dbc_text`, `validate_dbc` and `format_dbc_text`, which refuses it rather than formatting it. `error().bound_info()` then carries the bound kind, the observed size, the limit and `field`, the part of the DBC that crossed the bound (such as `"senders array"`), which every other bound leaves `std::nullopt`; the message names the command and that part. A text field's length is counted in characters, against `max_string_length_characters`.

---

## Cancellation

Every `AletheiaClient` operation takes a `std::stop_token` as its first parameter. Requesting a stop is observed at frame boundaries with the commit-prefix-and-report contract, so already-processed frames stay committed. The cross-binding semantics (Python `asyncio`, Go `context.Context`, C++ `std::stop_token`) are specified in the [Cancellation Contract](../architecture/CANCELLATION.md).

---

## Command-line interface

The `aletheia-cli` binary is a thin host CLI over `AletheiaClient`, mirroring the Python `aletheia` subcommands `validate`, `extract`, `signals`, `format-dbc`, `mux-query`, `template` (`check` is deferred; it needs a verified CAN-log reader). The logic lives in `aletheia::run_cli` (`aletheia/cli.hpp`), so it is unit-testable without spawning a process.

~~~bash
cmake -S cpp -B cpp/build && cmake --build cpp/build --target aletheia-cli
ALETHEIA_LIB=build/libaletheia-ffi.so cpp/build/aletheia-cli validate --dbc vehicle.dbc
~~~

The `--dbc` / `--json` flags and `$ALETHEIA_LIB` library-path resolution are the shared host-CLI contract; the full subcommand reference lives in the [CLI Reference](CLI.md).

---

## See Also

- **[Interface Guide](INTERFACES.md)** — Check API, YAML, and Excel loaders (cross-binding)
- **[Distribution Guide](../development/DISTRIBUTION.md)** — packaging + `make_ffi_backend` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)** — wire-level command/response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)** — `std::stop_token` semantics

# Aletheia Rust API Guide

**Purpose**: Reference for Aletheia's Rust binding, covering the `Client`, the Check API and the LTL DSL. The binding loads `libaletheia-ffi.so` at runtime through the [`libloading`](https://crates.io/crates/libloading) crate.

> **Exhaustive per-symbol docs** live as rustdoc comments in `rust/src/`: run `cargo doc --open`, or read them on the type, such as `Client::send_frame`. This guide is the narrative walkthrough; rustdoc is the contract.
>
> **Other bindings**: see the [Python API Guide](PYTHON_API.md), the [C++ API Guide](CPP_API.md), the [Go API Guide](GO_API.md), and the [Interface Guide](INTERFACES.md). All four bindings ship the same verified core with idiomatic, feature-equivalent APIs.

---

## Contents

- [Setup](#setup)
- [Check API](#check-api)
- [LTL DSL](#ltl-dsl)
- [Core Types](#core-types)
- [End-to-End: Parse, Check, Stream](#end-to-end-parse-check-stream)
- [Signal Operations](#signal-operations)
- [Error Handling](#error-handling)
- [Async & Cancellation](#async--cancellation)
- [Testing with MockBackend](#testing-with-mockbackend)
- [See Also](#see-also)

---

## Setup

Add the crate as a path or git dependency, it being unpublished (`publish = false`), build `libaletheia-ffi.so` as the [Building Guide](../development/BUILDING.md) describes, and point the binding at it with the `ALETHEIA_LIB` environment variable. `Client::new()` loads the default library and returns a ready client:

```rust
use aletheia::Client;

fn main() -> Result<(), aletheia::Error> {
    let client = Client::new()?; // loads libaletheia-ffi.so ($ALETHEIA_LIB or an install default)
    // ... use client (see below) ...
    Ok(())
}
```

For a configured client, with GHC RTS cores, a logger or a minimum log level, use the builder; for tests, inject a backend directly:

```rust
use aletheia::{Client, LogLevel};

let client = Client::builder()
    .rts_cores(4)
    .min_level(LogLevel::Info)
    .build()?;               // Result<Client, Error>
// Testing seam: Client::with_backend(Box::new(MockBackend::new())), no .so needed.
```

The kernel reads every number a check carries, through `Rational::from_decimal`, `TimeBound::parse` and the YAML and Excel loaders, and checks every predicate, formula and check a builder finishes, on a GHC runtime that starts once per process: by `aletheia::start_runtime(cores, logger)`, on the library a client loads, or by the first client. Nothing else starts it, so a program that builds or loads checks before it builds a client starts the runtime first; before any start, such a call answers `Error::RtsNotInitialized { operation }`, its text naming the call: `GHC runtime not initialized: call aletheia::start_runtime or build a Client before parsing decimals`, or `before reading a time bound`, `before building a check`, `before rendering` for a check's description. `cores` is the runtime's capability count, 1 for one bus; a count outside 1 to the CPUs the process may use is an `Error::Validation`. A client built without `rts_cores` asks for the count running; a runtime already up keeps its count, and another count asked of it logs `rts.cores_mismatch` on the logger given. `ClientBuilder::default_checks` takes the checks every `add_checks` prepends:

```rust
use aletheia::{load_checks_from_yaml, Client};

aletheia::start_runtime(1, None)?;
let checks = load_checks_from_yaml(
    "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 199.5\n",
)?;
let client = Client::builder().default_checks(checks).build()?;
```

Packaging and the library-path search order are covered in the [Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`aletheia::check::signal(name)` builds a property from a fluent, plain-English condition, the recommended starting point, needing no LTL. Numeric thresholds are exact `Rational`s and never `f64`; every value takes `impl Into<Rational>`, so an integer literal works directly and `Rational::from_decimal("0.25")` gives an exact decimal. A window is a `TimeBound`, whole microseconds. Each chain's finishing call hands the check it made to the kernel, which refuses a range whose minimum is above its maximum, a time bound past its limit and a signal name that is no identifier with the reason `set_properties` would give, so every finishing call returns `Result<Check, Error>`: `never_exceeds`, `never_below`, `never_equals` and `stays_between`, and a chain at the call that ends it, `equals(v).always()` or `settles_between(lo, hi).within(bound)`. The kernel's runtime must be up, which `aletheia::start_runtime` or a client sees to. Register a `Check` with `add_checks`:

```rust
use aletheia::{check, Rational, TimeBound};

aletheia::start_runtime(1, None)?;                                      // the kernel checks every check
let speed_limit = check::signal("Speed").never_exceeds(220)?;           // integer → Rational
let coolant = check::signal("Coolant").stays_between(80, 105)?;         // Result<Check, Error>
let idle = check::signal("Rpm").settles_between(700, 900).within(TimeBound(2_000_000))?; // 2 s
let quarter = check::signal("Throttle").never_exceeds(Rational::from_decimal("0.25")?)?;
```

Response-time and causal checks use `check::when(..).then(..)` and close with `.within(bound)`, returning `Result<Check, Error>`. Any `Check` can then be renamed and given a severity, and `condition_desc()` renders its condition through the kernel, the window in microseconds:

```rust
use aletheia::{check, TimeBound};

aletheia::start_runtime(1, None)?;      // the kernel checks every check
let brake_response = check::when("Brake").exceeds(50)
    .then("Decel").exceeds(2)
    .within(TimeBound(500_000))?        // decel must follow within 500 ms
    .named("brake response")
    .with_severity("safety");
assert_eq!(brake_response.condition_desc()?, "> 2 within 500000µs");
```

---

## LTL DSL

For full temporal control, build formulas directly. `Predicate` has a constructor for each of the eight: `equals`, `less_than`, `greater_than`, `less_than_or_equal`, `greater_than_or_equal`, `between`, `changed_by` and `stable_within`, each handing the predicate it made to the kernel and returning `Result<Predicate, Error>`, as a check's finishing call does. A predicate composes under the `Formula` temporal operators; the metric `Formula::always_within` and `eventually_within` take a `TimeBound` and return `Result<Formula, Error>` the same way, and `Formula::never` and `Formula::implies` are constructors. An enum variant written directly is checked when `set_properties` installs it:

```rust
use aletheia::{Formula, Predicate, TimeBound};

aletheia::start_runtime(1, None)?;      // the kernel checks every predicate a constructor builds
// always(Speed < 220)
let always_safe = Formula::Always(Box::new(
    Formula::Atomic(Predicate::less_than("Speed", 220)?)));
// never(Gear == -1)
let never_reverse = Formula::never(Predicate::equals("Gear", -1)?);
// within 100 ms, BrakeLight becomes 1 once Brake exceeds 50 (implies + eventually_within)
let brake_light = Formula::implies(
    Formula::Atomic(Predicate::greater_than("Brake", 50)?),
    Formula::eventually_within(TimeBound(100_000), // microseconds
        Formula::Atomic(Predicate::equals("BrakeLight", 1)?))?);
```

Formulas nest up to `aletheia::MAX_FORMULA_DEPTH`, which is 100. Pass a `&[Formula]` to `client.set_properties`, or a `&[Check]` to `client.add_checks`. `Check::formula()` exposes the underlying formula. The exhaustive variant lists are in rustdoc.

---

## Core Types

Numeric fields are **exact rationals**, with no floating-point drift. A `Rational` is a sign, a numerator magnitude and a positive denominator, each magnitude up to 2^128-1, always in lowest terms, so its equality is value equality (`1/2 == 2/4`); it has no ordering, the kernel deciding every comparison a property makes. `Rational::new(numerator, denominator)` takes two `i64`s, `Rational::from_parts(negative, numerator, denominator)` reaches every magnitude, `Rational::integer` takes an `i128`, `From` makes one of every fixed-width integer type, `i8` to `u128`, and `Rational::from_decimal` reads a decimal through the kernel; `is_negative()`, `numerator()` and `denominator()` read it back. A value description's key is a `SignMagnitude { negative, magnitude }`, a whole number whose magnitude reaches 2^128-1 in either sign, which `Display` prints and `i64::try_from` narrows, and a multiplexed signal's selector values are `u128`s. A `Timestamp` and a `TimeBound` are whole microseconds; `TimeBound::parse(text)`, or `text.parse::<TimeBound>()`, reads a window through the kernel, which refuses a negative or fractional number and one past 2^64-1. CAN IDs and DLC codes are validated newtypes built through fallible constructors:

```rust
use aletheia::{CanId, Dlc, Rational, SignMagnitude, TimeBound, Timestamp};

aletheia::start_runtime(1, None)?;      // the kernel reads every decimal and time bound
let id = CanId::standard(0x100)?;      // 11-bit standard ID  (Result<CanId, Error>)
let ext = CanId::extended(0x1FFF_FFFF)?; // 29-bit extended ID
let dlc = Dlc::new(8)?;                 // DLC code 8 → 8 payload bytes (Dlc::to_bytes)
let factor = Rational::integer(220);    // exact 220/1
let step = Rational::from_decimal("0.25")?; // exact 1/4 via the verified kernel
assert_eq!((step.numerator(), step.denominator()), (1, 4));
let widest = Rational::from_parts(true, u128::MAX, 1)?; // -(2^128-1)
let key = SignMagnitude { negative: true, magnitude: 32_768 };
assert_eq!(key.to_string(), "-32768");
let window: TimeBound = "1500".parse()?; // 1500 µs, read by the kernel
let ts = Timestamp(1_000);              // microseconds
```

`CanId::value()` and `is_extended()`, and `Dlc::to_bytes()` and `from_bytes(n)`, read the components back.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC, register checks, start the stream, send frames, end the stream**. `send_frame` returns a typed `FrameResponse`, matched rather than read out of a JSON dictionary, so verdicts are read structurally:

```rust
use aletheia::{check, CanId, Client, Dlc, FrameResponse, Timestamp};

fn main() -> Result<(), aletheia::Error> {
    aletheia::start_runtime(1, None)?;              // the kernel checks every check
    let client = Client::new()?;

    let dbc = r#"VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
"#;
    let _parsed = client.parse_dbc_text(dbc)?;     // ParsedDbc { dbc, warnings }

    client.add_checks(&[check::signal("Speed").never_exceeds(220)?])?;
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

    let result = client.end_stream()?;              // StreamResult: one verdict per check + warnings
    let _ = result;
    Ok(())
}
```

A `StreamResult` carries one `PropertyResult` per check and the stream's `warnings`, each a `StreamWarning` whose `kind` is a `WarningKind`: `UncachedAtom`, a property asking about a signal no frame carried. A real application pulls frames from a CAN log. The binding has no CAN-log reader, so frames come from your own source or from `python-can`. Send a batch eagerly with `send_frames(&[Frame])`, or lazily with `send_frames_iter(..)`.

---

## Signal Operations

Outside streaming or inside it, decode and synthesize frames directly. The `dlc` must match the payload length, and each returns a `Result`:

- `extract_signals(id, dlc, data)` → `ExtractionResult` (decode a frame).
- `build_frame(message, dlc, signals)` → `Vec<u8>` (encode signal values).
- `update_frame(message, dlc, frame, signals)` → `Vec<u8>` (patch a frame).

Each value is written exactly or refused: one outside the signal's declared range fails with code `frame_value_out_of_range`, one that no integer raw value scales to under the signal's factor and offset with `frame_value_not_representable`, and two requested signals sharing a bit with `frame_signals_overlap`. A written value reads back unchanged wherever the frame carries its signal: always, or for a multiplexed signal when its multiplexor's value selects it. Values travel as exact rationals both ways, a 64-bit signal's largest raw value, 2^64-1, among them; an extracted value whose numerator or denominator in lowest terms passes 2^128-1 is refused as that signal's entry in `errors`.

`extract_signals` reads the kernel's binary reply once a typed `parse_dbc` or `parse_dbc_text` has given the client the message's signal names, and its JSON reply otherwise. `Client::process`, the raw JSON escape hatch, can load another DBC, so every call empties that cache, and extraction reads the JSON reply until the next typed parse.

The typed `Dbc` keeps, in `unresolved_value_descs: Vec<RawValueDescription>`, each `VAL_` line of a parsed text whose CAN id and signal name matched no signal, with its entries, so that `validate_dbc` can warn about it.

Encoding takes the `DbcMessage` itself rather than its identifier, the signal positions being resolved against that message. A `SignalValue` is a name beside an exact value:

```rust
use aletheia::{CanId, Client, Dlc, SignalValue, Rational};

let client = Client::new()?;
let parsed = client.parse_dbc_text(r#"VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
"#)?;
let message = &parsed.dbc.messages[0];
let dlc = Dlc::new(8)?;

let decoded = client.extract_signals(CanId::standard(0x100)?, dlc, &[0u8; 8])?;
for value in &decoded.values {
    println!("{} = {:?}", value.name, value.value);
}

let rebuilt = client.build_frame(
    message,
    dlc,
    &[SignalValue { name: "Speed".to_string(), value: Rational::integer(72) }],
)?;
println!("encoded {} bytes", rebuilt.len());
```

---

## Error Handling

Every fallible operation returns `Result<_, aletheia::Error>`, and none panics on the normal path. `Error` is an enum matched directly. `Core { code, message }` carries the kernel's error code, `Validation { message, code, located }` is the caller's own input refused, carrying the kernel's code when the kernel refused it, and `Protocol`, `InputBoundExceeded(..)` and `ValidationFailed { .. }` classify what else a call refuses; the remaining variants, listed in rustdoc, are the shared library's loading and runtime failures (`LibraryLoad`, `SymbolMissing`, `InitFailed`, `AbiMismatch`, `RtsNotInitialized { operation }`), a null reply (`NullResponse`), a batch's per-frame error (`Frame`), the round-trip refusal (`TextRoundtripFailed`) and a mock backend's internal `BinaryPathUnsupported` signal:

```rust
use aletheia::Error;

fn describe(err: &Error) -> String {
    match err {
        Error::Validation { message, code, .. } => match code {
            Some(code) => format!("validation [{code}]: {message}"),
            None => format!("validation: {message}"),
        },
        Error::Core { code, message } => format!("core [{code}]: {message}"),
        other => other.to_string(),
    }
}
```

The YAML loader (`load_checks_from_yaml`, `load_checks_from_yaml_file`) and the `aletheia-excel` crate's (`load_checks_from_excel`, `load_dbc_from_excel`) hand the kernel each number they read as a rational, such as a check's `value` or a signal's `Factor`, as the text the document spells it with, a spreadsheet cell's trimmed of the whitespace around it, so the kernel decides what a valid number is. A number the kernel refuses keeps the kernel's variant, code and fields, `Error::Validation` carrying the kernel's `code` or `Error::InputBoundExceeded`, and gains `located: Option<Box<Located>>`, the place the loader read it: `location` (`Check 'C'` for a YAML check named `C`, `Check '<unnamed>'` for one with no name, `Row 2` for a spreadsheet row) and `key: Option<String>`, the YAML key or the column header it sat under (`value`, `within_us`, `Factor`), which `Error::location()` and `Error::key()` return; outside a loader `located` and both accessors are `None`. Its text (`to_string()`) reads `<location>: invalid '<key>': <kernel message>`. A YAML check's `within_us` and the Excel crate's `Time (µs)` and `Within (µs)` are whole microseconds the kernel reads through `TimeBound::parse`. A check the kernel refuses as it is built, where no single key holds the refusal, gains a place with no key and reads `<location>: <kernel message>`. A loader of your own locates a refusal with `Error::located(location, key)`, or `Error::located_at(location)` for a refusal of the place as a whole, each setting `located` on those two variants and returning any other error, such as a runtime that is not up, unchanged. The same document gets the same answer in every binding: [LOADER_SCENARIOS.yaml](../LOADER_SCENARIOS.yaml) is that contract.

<!-- refuses: text_parse_failure -->
```rust
aletheia::start_runtime(1, None)?; // the kernel reads every number
let refused = load_checks_from_yaml(
    "checks:\n  - name: C\n    signal: Speed\n    condition: never_exceeds\n    value: .5\n",
)
.unwrap_err();
assert_eq!(
    refused.to_string(),
    "Check 'C': invalid 'value': parse failed at line 1, column 1"
);
assert_eq!(
    (refused.location(), refused.key()),
    (Some("Check 'C'"), Some("value"))
);
```

The kernel bounds the length of a DBC's lists and strings, so `parse_dbc_text`, `parse_dbc`, `validate_dbc` and `format_dbc_text` return `Error::InputBoundExceeded` for a DBC past a size bound, its boxed `BoundRefusal` carrying the bound's kind (one of the `aletheia::limits` `BOUND_KIND_*` codes), the observed size, the limit, the kernel's `message` and, in `field: Option<String>`, the part of the DBC that crossed it (e.g. `"senders array"`, `"version string"`); `format_dbc_text` checks every bound before it formats anything. A bound that names no part of a DBC, such as the input's length, its nesting depth or an identifier's length, leaves `field` as `None`. `observed` and `limit` are `u128`s: a number past 2^128-1 is refused with `observed` at `u128::MAX`, its message naming only the limit. The error's text (`to_string()`) is the kernel's message exactly, e.g. `ParseDBC: senders array: array cardinality 10001 exceeds limit 10000`; the binding renders nothing of its own.

`Error::Protocol` is a reply the binding cannot read. Every place of a reply holding what the kernel never writes there is refused in one form, the same text in the four bindings: `reply <path>: expected <what>, got <what came>`, the path being the reply's keys from its root joined by `/`, such as `reply dbc/messages/signals/factor: expected a rational, got string`, and a key the reply lacks coming as `nothing`. A bound refusal's `bound_kind`, `observed` and `limit` and a validation refusal's `has_errors` and `issues` are read whole: a reply holding part of one is refused in that form, never read as a bare `Error::Core`. Rust has no dedicated `State` variant, so a call made in the wrong lifecycle state surfaces as `Error::Protocol` too. Codes match the kernel's `IssueCode` enum, tabulated in [PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference).

---

## Async & Cancellation

The synchronous `Client` is single-threaded and not `Send`. For an async, cancellable client, enable the `async` feature and use `AsyncClient`, which runs the client on a dedicated worker thread and exposes `async` methods resolving on whichever runtime you use. Dropping a pending future or the client cancels in-flight work at a frame boundary under the commit-prefix-and-report contract, so already-processed frames stay committed. The cross-binding cancellation semantics are specified in the [Cancellation Contract](../architecture/CANCELLATION.md).

Tests host the sync client on an `aletheia::testing::TurnExecutor` in place of the worker thread: `turns.adopt(client)` returns the `AsyncClient`, and `turns.block_on(future)` runs each queued call on the test's own thread at its turn, in queue order. A call whose future is dropped before its turn never reaches the client, as the worker skips a cancelled job, and one dropped during its turn runs to completion; a future left waiting with no call queued panics rather than hangs. A test therefore needs no thread, timer or runtime, and `run_turn()` runs one call when a test steps by hand.

~~~toml
# Cargo.toml
[dependencies]
aletheia = { path = "…", features = ["async"] }
~~~

---

## Testing with MockBackend

`MockBackend` is a public, clonable test double that records requests and replays queued responses, driving a `Client` without loading the library. Each response is read as the kernel's reply to its command would be, so a queue holds each command's own status, `success` for `start_stream`:

```rust
use aletheia::{Client, MockBackend};

let mock = MockBackend::new();
mock.respond_json(r#"{"status":"success"}"#);
let probe = mock.clone();                    // shares the queue + capture log
let client = Client::with_backend(Box::new(mock));
client.start_stream()?;                      // takes the queued response
assert_eq!(probe.captured(), vec!["<binary:startStream>".to_string()]);
```

An exhausted queue is an explicit error, `Error::Protocol` carrying `mock backend: no queued response for <op>`. All four bindings' mocks refuse that way, none synthesising a default response. A double of your own implements the `Backend` trait; its `build_frame_bin` and `update_frame_bin` receive a `SignalInjection` whose `values` pair each signal's position in its message with the exact `Rational` it is set to.

---

## See Also

- **[Interface Guide](INTERFACES.md)**, the Check API and the YAML and Excel loaders
- **[Distribution Guide](../development/DISTRIBUTION.md)**, packaging and the `ALETHEIA_LIB` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)**, the wire-level command and response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)**, the async cancellation semantics
- rustdoc: `cargo doc --open` (the exhaustive per-symbol contract)

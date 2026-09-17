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

Packaging and the library-path search order are covered in the [Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`aletheia::check::signal(name)` builds a property from a fluent, plain-English condition, the recommended starting point, needing no LTL. Numeric thresholds are exact `Rational`s and never `f64`; every value takes `impl Into<Rational>`, so an `i64` literal works directly and `Rational::from_decimal("0.25")` gives an exact decimal. The single-value terminals `never_exceeds`, `never_below` and `never_equals` are infallible; the range terminals `stays_between` and `settles_between(..).within(ms)`, and the causal `.within(ms)`, return `Result<Check, Error>`, guarding against a low bound above the high one. Register a `Check` with `add_checks`:

```rust
use aletheia::{check, Rational};

let speed_limit = check::signal("Speed").never_exceeds(220);           // i64 → Rational
let coolant = check::signal("Coolant").stays_between(80, 105)?;        // Result<Check, Error>
let idle = check::signal("Rpm").settles_between(700, 900).within(2000)?; // .within closes it
let quarter = check::signal("Throttle").never_exceeds(Rational::from_decimal("0.25")?);
```

Response-time and causal checks use `check::when(..).then(..)` and close with a `.within(ms)` deadline, returning `Result<Check, Error>`. Any `Check` can then be renamed and given a severity:

```rust
use aletheia::check;

let brake_response = check::when("Brake").exceeds(50)
    .then("Decel").exceeds(2)
    .within(500)?                       // decel must follow within 500 ms
    .named("brake response")
    .with_severity("safety");
```

---

## LTL DSL

For full temporal control, build formulas directly. `Predicate` has a constructor for each of the eight: `equals`, `less_than`, `greater_than`, `less_than_or_equal`, `greater_than_or_equal`, `between`, `changed_by` and `stable_within`. A predicate composes under the `Formula` temporal operators; the metric `Formula::always_within` and `eventually_within` take a `TimeBound`, and `Formula::never` and `Formula::implies` are constructors:

```rust
use aletheia::{Formula, Predicate, TimeBound};

// always(Speed < 220)
let always_safe = Formula::Always(Box::new(
    Formula::Atomic(Predicate::less_than("Speed", 220))));
// never(Gear == -1)
let never_reverse = Formula::never(Predicate::equals("Gear", -1));
// within 100 ms, BrakeLight becomes 1 once Brake exceeds 50 (implies + eventually_within)
let brake_light = Formula::implies(
    Formula::Atomic(Predicate::greater_than("Brake", 50)),
    Formula::eventually_within(TimeBound(100_000), // microseconds
        Formula::Atomic(Predicate::equals("BrakeLight", 1))));
```

Formulas nest up to `aletheia::MAX_FORMULA_DEPTH`, which is 100. Pass a `&[Formula]` to `client.set_properties`, or a `&[Check]` to `client.add_checks`. `Check::formula()` exposes the underlying formula. The exhaustive variant lists are in rustdoc.

---

## Core Types

Numeric fields are **exact rationals**, with no floating-point drift. CAN IDs and DLC codes are validated newtypes built through fallible constructors:

```rust
use aletheia::{CanId, Dlc, Rational, Timestamp};

let id = CanId::standard(0x100)?;      // 11-bit standard ID  (Result<CanId, Error>)
let ext = CanId::extended(0x1FFF_FFFF)?; // 29-bit extended ID
let dlc = Dlc::new(8)?;                 // DLC code 8 → 8 payload bytes (Dlc::to_bytes)
let factor = Rational::integer(220);    // exact 220/1
let step = Rational::from_decimal("0.25")?; // exact 1/4 via the verified kernel
let ts = Timestamp(1_000);              // microseconds
```

`CanId::value()` and `is_extended()`, `Dlc::to_bytes()` and `from_bytes(n)`, and `Rational::numerator()` and `denominator()` read the components back.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC, register checks, start the stream, send frames, end the stream**. `send_frame` returns a typed `FrameResponse`, matched rather than read out of a JSON dictionary, so verdicts are read structurally:

```rust
use aletheia::{check, CanId, Client, Dlc, FrameResponse, Timestamp};

fn main() -> Result<(), aletheia::Error> {
    let client = Client::new()?;

    let dbc = r#"VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
"#;
    let _parsed = client.parse_dbc_text(dbc)?;     // ParsedDbc { dbc, warnings }

    client.add_checks(&[check::signal("Speed").never_exceeds(220)])?;
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

A real application pulls frames from a CAN log. The binding has no CAN-log reader, so frames come from your own source or from `python-can`. Send a batch eagerly with `send_frames(&[Frame])`, or lazily with `send_frames_iter(..)`.

---

## Signal Operations

Outside streaming or inside it, decode and synthesize frames directly. The `dlc` must match the payload length, and each returns a `Result`:

- `extract_signals(id, dlc, data)` → `ExtractionResult` (decode a frame).
- `build_frame(message, dlc, signals)` → `Vec<u8>` (encode signal values).
- `update_frame(message, dlc, frame, signals)` → `Vec<u8>` (patch a frame).

Encoding takes the `DbcMessage` itself rather than its identifier, the signal positions being resolved against that message. Decoding a frame and encoding one are inverses, and a `SignalValue` is a name beside an exact value:

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

Every fallible operation returns `Result<_, aletheia::Error>`, and none panics on the normal path. `Error` is an enum matched directly. `Core { code, message }` mirrors the kernel's `IssueCode`, and `Validation`, `Protocol`, `InputBoundExceeded { .. }` and `ValidationFailed { .. }` classify what a call refuses; the remaining variants are the loader's own failures and the round-trip refusal, listed in rustdoc:

```rust
use aletheia::Error;

fn describe(err: &Error) -> String {
    match err {
        Error::Validation(msg) => format!("validation: {msg}"),
        Error::Core { code, message } => format!("core [{code}]: {message}"),
        other => other.to_string(),
    }
}
```

Rust has no dedicated `State` variant, so a call made in the wrong lifecycle state surfaces as `Error::Protocol`. Codes match the kernel's `IssueCode` enum, tabulated in [PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference).

---

## Async & Cancellation

The synchronous `Client` is single-threaded and not `Send`. For an async, cancellable client, enable the `async` feature and use `AsyncClient`, which runs the client on a dedicated worker thread and exposes `async` methods resolving on whichever runtime you use. Dropping a pending future or the client cancels in-flight work at a frame boundary under the commit-prefix-and-report contract, so already-processed frames stay committed. The cross-binding cancellation semantics are specified in the [Cancellation Contract](../architecture/CANCELLATION.md).

```toml
# Cargo.toml
[dependencies]
aletheia = { path = "…", features = ["async"] }
```

---

## Testing with MockBackend

`MockBackend` is a public, clonable test double that records requests and replays queued responses, driving a `Client` without loading the library:

```rust
use aletheia::{Client, MockBackend};

let mock = MockBackend::new();
mock.respond_json(r#"{"status":"ack"}"#);
let probe = mock.clone();                    // shares the queue + capture log
let client = Client::with_backend(Box::new(mock));
client.start_stream()?;                      // takes the queued response
assert_eq!(probe.captured(), vec!["<binary:startStream>".to_string()]);
```

An exhausted queue is an explicit error, `Error::Protocol` carrying `mock backend: no queued response for <op>`. All four bindings' mocks refuse that way, none synthesising a default response.

---

## See Also

- **[Interface Guide](INTERFACES.md)**, the Check API and the YAML and Excel loaders
- **[Distribution Guide](../development/DISTRIBUTION.md)**, packaging and the `ALETHEIA_LIB` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)**, the wire-level command and response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)**, the async cancellation semantics
- rustdoc: `cargo doc --open` (the exhaustive per-symbol contract)

# Aletheia Rust API Guide

**Purpose**: Reference for Aletheia's Rust binding — the `Client`, the Check API,
and the LTL DSL. The binding loads `libaletheia-ffi.so` at runtime via the
[`libloading`](https://crates.io/crates/libloading) crate.

> **Exhaustive per-symbol docs** live as rustdoc comments in `rust/src/` — run
> `cargo doc --open` (or read them on the type, e.g. `Client::send_frame`). This
> guide is the narrative walkthrough; rustdoc is the contract.
> **Other bindings**: see the [Python API Guide](PYTHON_API.md), the
> [C++ API Guide](CPP_API.md), the [Go API Guide](GO_API.md), and the
> [Interface Guide](INTERFACES.md) — all four bindings ship the same verified
> core with idiomatic, feature-equivalent APIs.

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

Add the crate as a path/git dependency (it is not published to crates.io —
`publish = false`), build `libaletheia-ffi.so` (see the
[Building Guide](../development/BUILDING.md)), and point the binding at it with
the `ALETHEIA_LIB` environment variable. `Client::new()` loads the default
library and returns a ready client:

```rust
use aletheia::Client;

fn main() -> Result<(), aletheia::Error> {
    let client = Client::new()?; // loads libaletheia-ffi.so ($ALETHEIA_LIB or an install default)
    // ... use client (see below) ...
    Ok(())
}
```

For a configured client (GHC RTS cores, a logger, a minimum log level) use the
builder; for tests, inject a backend directly:

```rust
use aletheia::{Client, LogLevel};

let client = Client::builder()
    .rts_cores(4)
    .min_level(LogLevel::Info)
    .build()?;               // Result<Client, Error>
// Testing seam: Client::with_backend(Box::new(MockBackend::new())) — no .so needed.
```

Packaging and the library-path search order are covered in the
[Distribution Guide](../development/DISTRIBUTION.md).

---

## Check API

`aletheia::check::signal(name)` builds a property from a fluent, plain-English
condition — the recommended starting point (no LTL knowledge required). Numeric
thresholds are exact `Rational`s (the float principle — no `f64`); every value
takes `impl Into<Rational>`, so an `i64` literal works directly, and
`Rational::from_decimal("0.25")` gives an exact decimal. The single-value
terminals (`never_exceeds` / `never_below` / `never_equals`) are infallible; the
range terminals (`stays_between` / `settles_between(..).within(ms)`) and the
causal `.within(ms)` return `Result<Check, Error>`, guarding against `lo > hi`.
Register a `Check` with `add_checks`:

```rust
use aletheia::{check, Rational};

let speed_limit = check::signal("Speed").never_exceeds(220);           // i64 → Rational
let coolant = check::signal("Coolant").stays_between(80, 105)?;        // Result<Check, Error>
let idle = check::signal("Rpm").settles_between(700, 900).within(2000)?; // .within closes it
let quarter = check::signal("Throttle").never_exceeds(Rational::from_decimal("0.25")?);
```

Response-time / causal checks use `check::when(..).then(..)` and close with a
`.within(ms)` deadline (returning `Result<Check, Error>`); any `Check` can then
be renamed and given a severity:

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

For full temporal control, build formulas directly. Atomic predicates
(`Predicate::less_than` / `greater_than` / `equals` / `less_than_or_equal` /
`greater_than_or_equal`) compose under the `Formula` temporal operators; the
metric variants `Formula::always_within` / `eventually_within` take a
`TimeBound`, and `Formula::never` / `Formula::implies` are constructors:

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

Formulas nest up to `aletheia::MAX_FORMULA_DEPTH` (100). Pass a `&[Formula]` to
`client.set_properties`, or `&[Check]` to `client.add_checks`
(`Check::formula()` exposes the underlying formula). The exhaustive `Formula` /
`Predicate` variant list is in rustdoc.

---

## Core Types

Numeric fields are **exact rationals** (no floating-point drift). CAN IDs and DLC
codes are validated newtypes built through fallible constructors:

```rust
use aletheia::{CanId, Dlc, Rational, Timestamp};

let id = CanId::standard(0x100)?;      // 11-bit standard ID  (Result<CanId, Error>)
let ext = CanId::extended(0x1FFF_FFFF)?; // 29-bit extended ID
let dlc = Dlc::new(8)?;                 // DLC code 8 → 8 payload bytes (Dlc::to_bytes)
let factor = Rational::integer(220);    // exact 220/1
let step = Rational::from_decimal("0.25")?; // exact 1/4 via the verified kernel
let ts = Timestamp(1_000);              // microseconds
```

`CanId::value()` / `is_extended()`, `Dlc::to_bytes()` / `from_bytes(n)`, and
`Rational::numerator()` / `denominator()` read the components back.

---

## End-to-End: Parse, Check, Stream

The streaming workflow is **parse a DBC → register checks → start the stream →
send frames → end the stream**. `send_frame` returns a typed `FrameResponse` — a
`match`, not a JSON dict — so verdicts are read structurally:

```rust
use aletheia::{check, CanId, Client, Dlc, FrameResponse, Timestamp};

fn main() -> Result<(), aletheia::Error> {
    let client = Client::new()?;

    let dbc = r#"VERSION ""
BU_ ECU
BO_ 256 Engine: 8 ECU
 SG_ Speed : 0|16@1+ (0.1,0) [0|6553.5] "km/h" ECU
"#;
    let (_dbc, _warnings) = client.parse_dbc_text(dbc)?;

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

A real application pulls frames from a CAN log; a Rust CAN-log reader is planned
(Phase 6) — until then, feed frames from your own source or `python-can` via IPC.
Send a batch eagerly with `send_frames(&[Frame])`, or lazily with
`send_frames_iter(..)` (see [Signal Operations](#signal-operations) and rustdoc).

---

## Signal Operations

Outside (or inside) streaming, decode and synthesize frames directly. `dlc` must
match the payload length; each returns a `Result`:

- `extract_signals(id, dlc, data)` → `ExtractionResult` (decode a frame).
- `build_frame(id, dlc, signals)` → `Vec<u8>` (encode signal values).
- `update_frame(id, dlc, data, signals)` → `Vec<u8>` (patch a frame).

See rustdoc for the exact `SignalInjection` argument shape and
[INTERFACES.md](INTERFACES.md) for a worked extract/build round-trip.

---

## Error Handling

Every fallible operation returns `Result<_, aletheia::Error>` — there are no
panics on the normal path. `Error` is an enum you `match` on directly; its
`Error::Core { code, message }` variant mirrors the kernel's `IssueCode`, and
`Error::Validation` / `Error::Protocol` / `Error::InputBoundExceeded { .. }` /
`Error::ValidationFailed { .. }` classify the failure:

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

Rust has no dedicated `State` kind — wrong-lifecycle conditions surface as
`Error::Protocol` (this binding's wrong-state category). Codes match the kernel's
`IssueCode` enum (see
[PROTOCOL.md § Error Code Reference](../architecture/PROTOCOL.md#error-code-reference)).

---

## Async & Cancellation

The synchronous `Client` is single-threaded (`!Send`). For an async, cancellable
client, enable the `async` feature and use `AsyncClient`, which runs the client
on a dedicated worker thread and exposes `async` methods that resolve on the
runtime of your choice (Tokio, async-std, smol — the binding is runtime-agnostic).
Dropping a pending future or the client cancels in-flight work at a frame
boundary with the commit-prefix-and-report contract — already-processed frames
stay committed. The cross-binding cancellation semantics are specified in the
[Cancellation Contract](../architecture/CANCELLATION.md).

```toml
# Cargo.toml
[dependencies]
aletheia = { path = "…", features = ["async"] }
```

---

## Testing with MockBackend

`MockBackend` is a public, `Clone`-able test double that records requests and
replays queued responses — drive a `Client` without loading the `.so`:

```rust
use aletheia::{Client, MockBackend};

let mock = MockBackend::new();
mock.respond_json(r#"{"status":"ack"}"#);
let probe = mock.clone();                    // shares the queue + capture log
let client = Client::with_backend(Box::new(mock));
// ... exercise client ...
assert_eq!(probe.captured(), vec!["<binary:startStream>".to_string()]);
```

An exhausted queue is an explicit error (`Error::Protocol` with
`mock backend: no queued response for <op>`) — the no-surprise contract shared by
all four bindings' mocks (none synthesises a default response).

---

## See Also

- **[Interface Guide](INTERFACES.md)** — Check API, YAML, and Excel loaders (cross-binding)
- **[Distribution Guide](../development/DISTRIBUTION.md)** — packaging + `ALETHEIA_LIB` wiring
- **[JSON Protocol](../architecture/PROTOCOL.md)** — wire-level command/response spec
- **[Cancellation Contract](../architecture/CANCELLATION.md)** — async cancellation semantics
- rustdoc: `cargo doc --open` (the exhaustive per-symbol contract)

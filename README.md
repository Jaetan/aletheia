# Aletheia

**Check recorded CAN logs against plain-language rules — with a signal decoder that's mathematically proven correct, not just tested.**

Aletheia checks recorded CAN logs against rules like *"Speed never exceeds 220"* or *"the brake light turns on within 100 ms of the pedal"* — and the code that decodes your signals is mathematically **proven** correct, not just tested. Point it at your `.dbc` and your `.blf` / `.asc` / `.mf4` / candump log; get pass/fail plus the exact timestamp of every violation.

> **The jargon, glossed once:** the "rules" are [Linear Temporal Logic](docs/GLOSSARY.md) (LTL) formulas, and the checker is written in [Agda](docs/GLOSSARY.md), a proof assistant where a program that compiles is a program that's proven correct. You never touch either — every italicized term is defined in the **[Glossary](docs/GLOSSARY.md)**.

**Building something safety-critical?** Formal methods like Aletheia's are exactly what **ISO 26262** (automotive functional safety) *recommends* for **ASIL-D**, the highest integrity level. Aletheia hands you a decoder whose correctness is a theorem, not a test suite.

**One honest caveat up front:** the proof covers the decoder and the rule-checker — it does *not* vouch for your DBC being right for your vehicle, the logger hardware, or a rule you specified wrong. ([Full scope below.](#what-the-proof-does-and-doesnt-cover))

---

## The pain this removes

Every item below is a bug class that has shipped in real CAN tooling. Aletheia turns each into a proven guarantee:

- **Wrong endianness / byte order** → silently swapped bytes and a plausible-but-wrong speed. → *The decoder is proven to honor the DBC's byte order for every signal.*
- **Bit-shift & masking mistakes** → a signal straddling a byte boundary reads garbage. → *Proven correct for every start-bit / length, cross-byte signals included.*
- **Sign extension** → a small negative temperature reads as a huge positive number. → *Signed decoding is proven for all widths.*
- **Multiplexed-signal decoding** → the wrong multiplexer case selects the wrong signal. → *Mux selection is part of the proof.*
- **Ad-hoc scripts with their own bugs** → every team re-implements decode + threshold logic, each with fresh mistakes. → *One proven core, four language bindings, zero re-implementation.*

## Why switch from cantools / python-can / hand-rolled scripts?

All three decode CAN with **tested** code: correct on the cases someone thought to test, and still potentially wrong on an untried endianness, sign, or multiplexer case. Aletheia's decoder is **proven correct for all inputs** — the guarantee holds even for signals no test ever exercised.

| If you use… | How it decodes signals | The gap Aletheia closes |
|---|---|---|
| **cantools** | hand-written Python decoders, validated by unit tests | an untested endianness / sign / mux combination can still decode wrong |
| **python-can** | transport plus tested per-DBC decoders | same tested-not-proven decode path, and no temporal-rule checking |
| **hand-rolled scripts** | your own bit-shifts and threshold checks | the most bug-prone option — every script re-derives decode logic from scratch |

## What you get

- **Proven-correct decoding** — signal extraction and frame building are correct for *every* valid DBC, by mathematical proof rather than test coverage.
- **Temporal rules, not just thresholds** — *"within 100 ms"*, *"eventually"*, *"never after"*: full LTL over the whole trace, with a streaming checker that runs in O(1) memory (verified 1.08× growth across a 100× longer trace) — fast enough for real-time 1 Mbps CAN. Per-binding / per-lane throughput lives in [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).
- **Four first-class bindings** — Python, C++, Go, and Rust, all running in-process (no subprocess, no IPC overhead) and all producing identical verdicts.
- **Real-world DBC support** — multiplexed signals, 29-bit IDs, signed integers, value tables, attributes, environment variables, and comments; validated against a cross-binding corpus with typed rejection codes ([error reference](docs/architecture/PROTOCOL.md#error-code-reference)).
- **Exact arithmetic** — signal values are exact rationals end-to-end, never floats: a decoded value is never off by a rounding step.
- **Four ways to write checks** — Check API (engineers), YAML (CI/CD), Excel (technicians), and the full LTL DSL (developers). Pick the level that fits the team.

---

## Quick Start

### 60-second try — no code

The fastest path writes zero code. Point the `aletheia` CLI at a DBC, a checks file, and a recorded log. Ready-to-run sample assets ship in [`examples/demo/`](examples/demo/), so this runs as-is:

```bash
cd examples/demo
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
```

- **exit 0** — every check passed
- **exit 1** — violations found (each printed with the exact microsecond timestamp)
- **exit 2** — error (bad DBC, unreadable log, …)

The sample `drive.log` speeds past its 120 kph limit, so this run reports a timestamped `VehicleSpeed` violation and exits 1. The three shipped assets — `vehicle.dbc`, `vehicle_checks.yaml`, and the candump `drive.log` — are a matched set. Recorded logs in `.blf` / `.asc` / `.mf4` / candump `.log` all work as the trace argument. Full subcommand + flag reference: **[CLI Guide](docs/reference/CLI.md)** — six subcommands (`check`, `validate`, `extract`, `signals`, `format-dbc`, `mux-query`):

```bash
# Validate a DBC and list every issue (errors and warnings)
aletheia validate --dbc vehicle.dbc

# List the signals a DBC defines
aletheia signals --dbc vehicle.dbc
```

### Install

Aletheia separates a **one-time, build-time toolchain** from a **lightweight runtime**:

- **Build once** (from source): Agda + GHC + Cabal compile the verified core into the shared library `libaletheia-ffi.so`. This is where the proofs are checked; it happens once, not at runtime.
  ```bash
  cabal run shake -- build
  ```
- **Run**: only `libaletheia-ffi.so` plus Python 3.14 (and your binding's own runtime). No Agda, no proof assistant, at runtime.

> **There is no published wheel yet — `pip install aletheia` does not work today.** After building the library, install the Python binding editable from the source tree: `pip install -e '.[can]'` inside `python/`. Full setup, prerequisites, and troubleshooting: **[Building Guide](docs/development/BUILDING.md)**.

### In code: the Python streaming DSL

Prefer to script it? The Python binding streams frames and reports violations with timestamps.

> **Which style should I use?** New users should start with the **Check API** or the YAML/Excel loaders shown under [Higher-Level Interfaces](#higher-level-interfaces) below — they cover the common cases. The raw DSL (`Signal`, `set_properties`) shown here is the escape hatch for full LTL control (metric operators, custom predicates). See the [Interface Guide](docs/reference/INTERFACES.md) for an end-to-end comparison.

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc import dbc_to_json
from aletheia.can_log import iter_can_log  # from source: pip install -e '.[can]' under python/

# Load DBC specification (converts .dbc to JSON)
dbc_json = dbc_to_json("vehicle.dbc")

# Define temporal properties using fluent DSL (raw LTL)
speed_limit = Signal("Speed").less_than(220).always()
brake_check = Signal("BrakePressed").equals(1).eventually()

# Stream CAN frames from a .blf / .asc / .log / .mf4 trace and check properties.
# iter_can_log() yields CANFrameTuple(timestamp_us, can_id, dlc, data, extended,
# brs, esi) — seven fields. timestamp_us is microseconds (int), can_id is the
# raw 11- or 29-bit arbitration ID, dlc is the DLC code (0–8 for CAN 2.0B, 0–15
# for CAN-FD), data is bytes/bytearray of length dlc_to_bytes(dlc), extended is
# True for 29-bit IDs, brs/esi are CAN-FD Bit Rate Switch / Error State
# Indicator (None on CAN 2.0B frames). The unpack below ignores the trailing
# three fields for brevity.
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([speed_limit.to_dict(), brake_check.to_dict()])
    client.start_stream()

    for timestamp_us, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.blf"):
        response = client.send_frame(timestamp_us, can_id, dlc, data)
        # A frame that produces verdicts returns a property_batch envelope;
        # each fails entry is a violation. timestamp is an int (microseconds).
        if response.get("type") == "property_batch":
            for entry in response["results"]:
                if entry.get("status") == "fails":
                    print(f"Violation at {entry['timestamp']}us")

    client.end_stream()
```

See the [Python API Guide](docs/reference/PYTHON_API.md) for the complete DSL reference.

### Higher-Level Interfaces

For users who don't need full LTL control, Aletheia provides three
higher-level interfaces that compile to the same verified core (recommended
entry point for new users):

```python
from aletheia import checks, load_checks, load_checks_from_excel

# Check API — industry vocabulary
checks.signal("Speed").never_exceeds(220)
checks.when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100)

# YAML — declarative config files
check_list = load_checks("checks.yaml")

# Excel — spreadsheet templates for technicians
check_list = load_checks_from_excel("checks.xlsx")
```

See the [Interface Guide](docs/reference/INTERFACES.md) for end-to-end workflows.

### Signal Operations

`AletheiaClient` also provides signal extraction and frame building:

```python
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)

    # Build a frame from signal values
    frame = client.build_frame(can_id=0x100, dlc=8, signals={"Speed": 72})

    # Extract signals from a frame
    result = client.extract_signals(can_id=0x100, dlc=8, data=frame)
    speed = result.get("Speed")  # Fraction(72) — extraction values are exact Fractions

    # Update specific signals in a frame
    modified = client.update_frame(can_id=0x100, dlc=8, frame=frame, signals={"Speed": 130})
```

### Async client and lazy iter

For asyncio code, ``aletheia.asyncio.AletheiaClient`` mirrors the sync surface
as ``async def`` methods, cancellable via ``asyncio.CancelledError``. Both
clients expose ``send_frames_iter`` for processing frames lazily one at a
time — useful when the source is a live producer (queue, socket, generator)
and full materialization is wasteful or impossible.

```python
import asyncio
from aletheia.asyncio import AletheiaClient

async def watch(timeout_s: float):
    async with AletheiaClient() as client:
        await client.parse_dbc(dbc_json)
        await client.set_properties([prop.to_dict()])
        await client.start_stream()
        try:
            async with asyncio.timeout(timeout_s):
                async for r in client.send_frames_iter(live_frames()):
                    if r.violation is not None:
                        handle(r.violation)
        except TimeoutError:
            pass  # committed prefix is durable
        await client.end_stream()
```

See the [Cancellation contract](docs/architecture/CANCELLATION.md) for the
behavioral parity guarantees Python, C++, Go, and Rust all share.

### Which binding? Start here

Python is the **reference binding**. C++, Go, and Rust are **API-compatible ports** that call the same proven core and produce identical verdicts — pick the one that matches your stack:

| Language | Start here | Host CLI |
|---|---|---|
| **Python** (reference) | [Python API Guide](docs/reference/PYTHON_API.md) | ✅ all 6 subcommands |
| **C++** | [C++ API Guide](docs/reference/CPP_API.md) | ✅ 5 (`check` deferred — needs a verified CAN-log reader) |
| **Go** | [Go API Guide](docs/reference/GO_API.md) | ✅ 5 (`check` deferred — needs a verified CAN-log reader) |
| **Rust** | [Rust API Guide](docs/reference/RUST_API.md) | typed client today; CLI is a Phase 6 goal |

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── include/             # C header (aletheia.h)
├── python/              # Python API
├── cpp/                 # C++23 binding
├── go/                  # Go binding
├── rust/                # Rust binding (loads libaletheia-ffi.so at runtime)
├── benchmarks/          # Cross-language benchmarks
├── docs/                # Documentation
└── examples/            # Sample DBC files and demos
```

## Documentation

**📚 [Complete Documentation Index](docs/INDEX.md)** - Full navigation guide

### Getting Started
- [Glossary](docs/GLOSSARY.md) - Plain-language definitions of LTL, formal verification, Agda, DBC, and CAN terms
- [Tutorials](docs/guides/TUTORIAL.md) - End-to-end walkthroughs by role (start here if new to Aletheia)
- [Quick Start](docs/guides/QUICKSTART.md) - 5-minute walkthrough (assumes built library)
- [Building Guide](docs/development/BUILDING.md) - Setup and installation

### Guides
- [Cookbook](docs/guides/COOKBOOK.md) - Problem-driven recipes

### Reference
- [Interface Guide](docs/reference/INTERFACES.md) - Check API, YAML, Excel loaders
- [Python API Guide](docs/reference/PYTHON_API.md) - Raw DSL and AletheiaClient reference (reference binding)
- [C++ API Guide](docs/reference/CPP_API.md) - `AletheiaClient`, Check API, and the `ltl::` DSL
- [Go API Guide](docs/reference/GO_API.md) - `Client`, Check API, and the LTL DSL
- [Rust API Guide](docs/reference/RUST_API.md) - `Client`, Check API, and the LTL DSL
- [CLI Reference](docs/reference/CLI.md) - `aletheia` subcommands

### Architecture & Design
- [Design Overview](docs/architecture/DESIGN.md) - Three-layer architecture
- [JSON Protocol](docs/architecture/PROTOCOL.md) - Low-level protocol specification
- [Cancellation Contract](docs/architecture/CANCELLATION.md) - Cross-binding cancellation semantics
- [cgo Notes](docs/architecture/CGO_NOTES.md) - Go binding's cgo + dlopen rationale

### Operations
- [Runbook](docs/operations/RUNBOOK.md) - Symptom → cause → action
- [Stability Bench](docs/operations/STABILITY.md) - RSS / FD drift detection
- [Mutation Testing](docs/operations/MUTATION.md) - Per-binding mutation testing

### Development
- [Local CI](docs/development/CI_LOCAL.md) - Three-layer CI architecture
- [Release Guide](docs/development/RELEASE.md) - Tag / sign / publish procedure
- [Feature Matrix](docs/FEATURE_MATRIX.yaml) - Cross-binding feature parity (the live source)

### Contributing
- [Contributing Guide](CONTRIBUTING.md) - How to contribute
- [CLAUDE.md](CLAUDE.md) - AI-assisted development
- [Project Status](PROJECT_STATUS.md) - Current phase and roadmap
- [CHANGELOG](CHANGELOG.md) - Public-API change log

### Additional
- [Project Pitch](docs/PITCH.md) - Why Aletheia?
- [Examples](examples/) - Sample DBC files and demos

## Project Status

**Current Phase**: See [PROJECT_STATUS.md](PROJECT_STATUS.md) for current phase and detailed status.

Complete information on deliverables, quality gates, and roadmap is available in PROJECT_STATUS.md.

## Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) to understand what kinds of contributions belong upstream, extension points for customization, and submission guidelines.

## License

This project is licensed under the **BSD 2-Clause License**. See [LICENSE.md](LICENSE.md) for details.

### License Philosophy

BSD 2-Clause was chosen to allow broad adoption (including proprietary use) while encouraging collaboration through architecture and process rather than legal compulsion.

---

## Under the hood (for the curious)

You never need this section to *use* Aletheia — it's here for readers who want to know what "proven" actually means.

### What the proof does and doesn't cover

**Proven** (a bug in these classes cannot exist in the verified core):

- Signal extraction and frame building are correct for every valid DBC and every input frame — all byte orders, widths, signs, and multiplexer cases.
- The LTL checker's verdicts match the formal semantics of the properties, and do not drift over arbitrarily long traces.
- The DBC round-trip is exact: `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` — parsing a formatted DBC returns the original definition, proven for all well-formed inputs.

**Not covered** (still your responsibility, as with any tool):

- **Specification errors** — the proof shows the implementation matches the *stated* rule, not that the rule (or the DBC) is the right one for your vehicle.
- **Hardware / bus / OS** — bit-stuffing on the physical bus, ECU faults, logger timestamp skew, kernel scheduling: all below Aletheia's boundary.
- **Integration & operator error** — wiring the wrong log, missing a rule, misreading a YAML threshold.
- **Trusted components** — Agda's `--safe` kernel, GHC, and the Haskell `base` + `text` used in the thin shim are trusted, not verified.

In short: Aletheia eliminates the "the decoder was wrong" and "the checker drifted" bug classes — not bugs elsewhere in your system.

### How the layers fit together

The verified Agda core is compiled to Haskell (via Agda's MAlonzo backend) and linked into a single shared library, `libaletheia-ffi.so`. Every binding loads that same library in-process — Python via `ctypes`, C++ and Go via `dlopen`, Rust via `libloading` — so all four run identical proven logic with no subprocess or IPC overhead. Architecture detail: [Design Overview](docs/architecture/DESIGN.md).

### Etymology

**Aletheia** (Ἀλήθεια) is Greek for "truth" or "disclosure" — in philosophy, the uncovering or revealing of truth. It's a fitting name for a tool whose job is to reveal what your CAN logs actually did, with correctness you can prove rather than hope for.
</content>
</invoke>

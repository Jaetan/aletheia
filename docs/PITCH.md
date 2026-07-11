# Aletheia: Project Pitch

**Check recorded CAN logs against plain-language rules — with a signal decoder that's mathematically proven correct, not just tested.**
**Last Updated**: 2026-07-10

Aletheia checks recorded CAN logs against rules like *"Speed never exceeds 220"* or *"the brake light turns on within 100 ms of the pedal"* — and the code that decodes your signals is mathematically **proven** correct, not just tested. Point it at your `.dbc` and your `.blf` / `.asc` / `.mf4` / candump log; get pass/fail plus the exact timestamp of every violation.

> **The jargon, glossed once:** the "rules" are [Linear Temporal Logic](GLOSSARY.md) (LTL) formulas — a formal method for specifying how a sequence must behave over time — and the checker is written in [Agda](GLOSSARY.md), a proof assistant. You never touch either; every italicized term is defined in the **[Glossary](GLOSSARY.md)**.

**Building something safety-critical?** Formal methods like Aletheia's are exactly what **ISO 26262** (automotive functional safety) *recommends* for **ASIL-D**, the highest integrity level. Aletheia gives you a decoder whose correctness is a theorem, not a test suite.

**One honest caveat up front:** the proof covers the decoder and the rule-checker — not whether your DBC is right for your vehicle, the logger hardware, or a rule you specified wrong. ([Full scope below.](#what-the-proofs-dont-cover))

This document explains what Aletheia is, why it exists, and what it means for your team to adopt it.

---

## The pain this removes

Every item below is a bug class that has shipped in real CAN tooling. Aletheia turns each into a proven guarantee:

- **Wrong endianness / byte order** → silently swapped bytes, a plausible-but-wrong speed. → *The decoder is proven to honor the DBC's byte order for every signal.*
- **Bit-shift & masking mistakes** → a signal straddling a byte boundary reads garbage. → *Proven correct for every start-bit / length, cross-byte signals included.*
- **Sign extension** → a small negative temperature reads as a huge positive number. → *Signed decoding is proven for all widths.*
- **Multiplexed-signal decoding** → the wrong multiplexer case selects the wrong signal. → *Mux selection is part of the proof.*
- **Ad-hoc scripts with their own bugs** → every team re-implements decode + threshold logic, each with fresh mistakes. → *One proven core, four language bindings, zero re-implementation.*

## Why switch from cantools / python-can / hand-rolled scripts?

All three decode CAN with **tested** code: correct on the cases someone thought to test, and still potentially wrong on an untried endianness, sign, or multiplexer case. Aletheia's decoder is **proven correct across the whole input space** — for every signal a valid DBC admits and every value it can hold, decode is proven to invert the DBC's encoding, in both byte orders and both signednesses. The guarantee holds even for signals and values no test ever exercised.

| If you use… | How it decodes signals | The gap Aletheia closes |
|---|---|---|
| **cantools** | hand-written Python decoders, validated by unit tests | an untested endianness / sign / mux combination can still decode wrong |
| **python-can** | transport plus tested per-DBC decoders | same tested-not-proven decode path, and no temporal-rule checking |
| **hand-rolled scripts** | your own bit-shifts and threshold checks | the most bug-prone option — every script re-derives decode logic from scratch |

---

## What is Aletheia?

Aletheia is a library for analyzing automotive CAN bus data with **mathematical guarantees of correctness**, with first-class bindings for **Python, C++, Go, and Rust**. You write temporal properties (e.g., "Speed never exceeds 220 km/h"), and Aletheia verifies them against CAN traces with proofs that the checker itself is bug-free.

**Elevator pitch**: Testing shows the presence of bugs. Formal verification proves their absence. Aletheia brings proof-backed CAN analysis to engineers — in Python, C++, Go, or Rust — without requiring a PhD in formal methods.

---

## The Problem

**Current state**: Automotive software is tested, not proven.

Testing CAN frame processing is error-prone:
- Signal extraction bugs cause safety issues (wrong endianness, bit shifts, sign extension)
- Temporal properties are checked with ad-hoc scripts that may themselves have bugs
- Regression tests provide examples, not guarantees
- Edge cases (multiplexed signals, 29-bit IDs, signed integers) are easy to get wrong

**Real-world impact**: A bug in signal extraction can lead to incorrect speed readings, missed brake states, or corrupted diagnostic data. Testing catches some of these. Formal verification catches all of them.

---

## The Solution

Aletheia provides:

1. **Multi-language APIs**: Familiar interfaces for automotive engineers
   ```python
   checks.signal("Speed").never_exceeds(220)                   # Python
   ```
   ```cpp
   check::signal("Speed").never_exceeds(PhysicalValue::of(220, 1));  // C++
   ```
   ```go
   aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))  // Go
   ```
   ```rust
   check::signal("Speed").never_exceeds(220)                   // Rust
   ```

2. **Formally verified core**: Signal extraction and LTL checking implemented in Agda with mathematical proofs of correctness

3. **Streaming architecture**: Process gigabyte-scale CAN traces with O(1) memory (verified 1.08× memory growth across a 100× trace increase). Single-bus streaming throughput per binding / lane / property shape lives in [BENCHMARKS.md § Canonical Results](development/BENCHMARKS.md#canonical-results) — the canonical table.

4. **DBC integration**: Parse real-world DBC files (tested against OpenDBC corpus)

5. **Proven DBC validator**: 23 structural checks with a machine-checked **soundness + completeness** proof. It certifies your DBC is well-formed — which is exactly the precondition the decode proof assumes, so a validated DBC is one the correctness guarantee actually applies to.

6. **Exact arithmetic**: Signal values are exact rationals end-to-end, never floats — a decoded value is never off by a rounding step.

**Key insight**: You write Python, C++, Go, or Rust. The proof burden lives in Agda. If the code type-checks, it's correct by construction.

**Where to start, by language** — Python is the reference binding; the others are API-compatible ports that call the same proven core:

- **Python** → [Python API Guide](reference/PYTHON_API.md)
- **C++** → [C++ API Guide](reference/CPP_API.md)
- **Go** → [Go API Guide](reference/GO_API.md)
- **Rust** → [Rust API Guide](reference/RUST_API.md)

---

## Why Formal Verification?

**Testing** shows the presence of bugs. **Formal verification** proves their absence.

| Approach | What it provides | What it misses |
|----------|------------------|----------------|
| Unit tests | Examples of correct behavior | Edge cases, unexpected inputs |
| Property-based testing | Random exploration | Exhaustive coverage guarantees |
| **Formal verification** | **Mathematical proof of correctness** | **Nothing (within specified properties)** |

<a id="what-the-proofs-dont-cover"></a>

**What the proofs don't cover** (important to set expectations):

- **Specification errors**: The proofs guarantee the implementation matches the stated properties, not that the properties are the right ones. "Speed extraction returns the value encoded by the DBC" is proven; whether that DBC is correct for your vehicle is an engineering question.
- **Hardware, bus layer, and OS behaviour**: Bit-stuffing errors on the physical CAN bus, ECU faults, timestamp skew from the logger hardware, and kernel scheduling all sit below Aletheia's abstraction boundary.
- **Integration and operator error**: Wiring the wrong log file, missing a property, misreading a YAML threshold — these are normal human-process risks and must be covered by the surrounding tooling and review practices.
- **Third-party components**: Agda's `--safe` kernel, GHC, and the Haskell `base` + `text` used in the shim are trusted rather than verified. Compiler and runtime bugs at that level propagate through.

In other words: Aletheia eliminates the class of bugs where "the signal extraction code was wrong" or "the LTL evaluator drifted over a long trace" — not bugs elsewhere in the system.

**Example**:
- Test: "Speed extraction works for 100 km/h" ✓
- Proof: "Speed extraction is correct for every value the signal can represent, in both byte orders" ✓✓✓

**Trade-off**: Higher upfront cost (writing proofs), lower long-term cost (no signal extraction bugs, ever).

---

## Technology Stack

Aletheia uses a three-layer architecture:

```
Python / C++ / Go / Rust (user-facing APIs, in-process)
   ↓ shared library, loaded in-process (no subprocess, no IPC)
Haskell (thin FFI wrapper → libaletheia-ffi.so)
   ↓
Agda (all logic + proofs, compiled via the MAlonzo backend)
```

**Why these technologies?**

- **Agda**: A proof assistant where code that type-checks is mathematically proven correct — similar to how Rust's compiler guarantees memory safety, but for logical correctness. Used in aerospace, cryptography, and compilers.
- **Haskell**: Mature compiler (GHC) for Agda-generated code. Industry-proven (Meta, Standard Chartered, IOHK). Compiled to a shared library loaded by all bindings.
- **Python / C++ / Go / Rust**: Familiar interfaces for automotive engineers. All complexity hidden behind a shared library each language loads in-process, with no subprocess overhead.

**Proven track record**:
- Agda: Used in verified compilers (Agda-to-Haskell compiler itself), verified data structures, and verified network protocols
- Haskell: Used in production at scale (>1M LoC codebases at Meta, Standard Chartered, IOHK)
- Formal methods stack: Same class of tools as CompCert (verified C compiler) and seL4 (verified microkernel)

---

## Risks and Mitigations

### Technical Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Build complexity** | Requires Agda + GHC + Cabal | Low | Documented build process, tested on Ubuntu/Debian/WSL2. One-time build-time toolchain; runtime is just the shared library + Python. |
| **Toolchain maturity** | Agda ecosystem smaller than Python | Low | Agda 2.8.0 is stable. GHC is industry-proven. Only standard library dependencies. |
| **Agda learning curve** | Modifying core requires expertise | Medium | Binding APIs are stable. Core changes rare. Can contract experts if needed. |

### People Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Bus factor** | Knowledge concentrated in one person | High initially | Documentation emphasizes maintainability. CLAUDE.md provides AI-assisted development guide. |
| **Hiring difficulty** | Agda experts are rare | Medium | Not needed for binding-API users. For core development: remote contractors available, or train interested engineers. |
| **Team resistance** | "Not invented here" / unfamiliar tech | Medium | Start with non-critical use cases. Demonstrate value before mandating adoption. |

### Legal/Compliance Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **License compatibility** | BSD 2-Clause vs. company policy | Low | Permissive license, allows proprietary use. No copyleft. |
| **Patent issues** | Agda/GHC patents | Very Low | Agda is open source (MIT). GHC is open source (BSD 3-Clause). No known patent issues. |
| **Regulatory acceptance** | Formal methods not in compliance checklist | Medium | Formal verification **strengthens** compliance story. ISO 26262 (the automotive functional safety standard) recommends formal methods for ASIL-D (the highest safety integrity level). |

---

## For Engineers

**What you need to know**: How to use the API in your language. That's it.

**What you don't need to know**: Agda, Haskell, formal verification theory.

**Four ways to define checks** (all compile to the same verified core):

Python:
```python
from pathlib import Path
checks.signal("Speed").never_exceeds(220)           # Check API
load_checks(Path("checks.yaml"))                    # YAML (Path → file)
load_checks_from_excel("tests.xlsx")                # Excel
Signal("Speed").less_than(220).always()             # Full DSL
```

C++:
```cpp
check::signal("Speed").never_exceeds(PhysicalValue::of(220, 1));
[[maybe_unused]] auto _yaml  = load_checks_from_yaml("checks.yaml");
[[maybe_unused]] auto _excel = load_checks_from_excel("tests.xlsx");
// LTL formulas via ltl:: namespace (compositional, not fluent DSL):
auto f = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue::of(220, 1))));
```

Go:
```go
aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
_, _ = aletheia.LoadChecksFromYAMLFile("checks.yaml")
_, _ = excel.LoadChecks("tests.xlsx")
// LTL formulas via struct-based AST (compositional, not fluent DSL):
f := aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)}}}
_ = f
```

Rust:
```rust
let speed = check::signal("Speed").never_exceeds(220);       // Check API (i64 → exact Rational)
let coolant = check::signal("Coolant").stays_between(80, 105)?;
// LTL formulas via the compositional Formula/Predicate AST:
let f = Formula::Always(Box::new(Formula::Atomic(Predicate::less_than("Speed", 220))));
```

**Streaming workflow** (Python shown). The client pattern — parse the DBC, add checks, feed frames, read verdicts — is identical across all four bindings. The `iter_can_log` log-file reader, however, is currently Python-only: in C++, Go, and Rust you supply frames from your own source (a live bus, your own parser, or replayed capture) and feed them to `send_frame` the same way.

```python
from aletheia import AletheiaClient, checks
from aletheia.dbc import dbc_to_json
from aletheia.can_log import iter_can_log

dbc = dbc_to_json("vehicle.dbc")
check_list = [checks.signal("Speed").never_exceeds(220)]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(check_list)
    client.start_stream()

    for ts, can_id, dlc, data, _extended, _brs, _esi in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("status") == "fails":
            print(f"Violation at {response['timestamp']['numerator']}us")

    client.end_stream()
```

In Rust the same loop reads verdicts by matching on the frame response — `FrameResponse::Ack` for an accepted frame with no verdict yet, `FrameResponse::Verdicts(Vec<PropertyResult>)` when a frame closes one or more checks:

```rust
match client.send_frame(ts, id, dlc, &data, None, None)? {
    FrameResponse::Ack => {}                       // frame accepted, no verdict yet
    FrameResponse::Verdicts(results) => {          // Vec<PropertyResult>
        for r in &results {
            // r.property_index, r.verdict (Verdict::Fails on a violation), r.enrichment
            let _ = r;
        }
    }
}
```

**Learning curve**: If you can use a standard library in your language, you can use Aletheia. All four bindings follow the same workflow and produce identical verification results — surface APIs use each language's idioms (Python fluent DSL, C++ strong types + `std::expected`, Go interfaces + functional options, Rust `Result` + builder) but the protocol-level behavior is the same.

**Debugging**: Violations include counterexamples (frame number, signal values). Standard debugging in your language applies.

**Testing**: Write unit tests for your properties, just like any other code. The difference: Aletheia's checker is proven correct, so if your property is right, it will catch bugs.

---

## For Team Leads

**Integration questions**:

**Q: How does this fit into our CI/CD pipeline?**
A: Aletheia provides Python, C++, Go, and Rust bindings. Integrate like any test suite in your language. Run `pytest tests/` in CI for Python. Checks can also be defined in YAML for version-controlled CI configurations, and the `aletheia` CLI returns a shell exit code (0 pass / 1 violations / 2 error) for pipeline gating.

**Q: What's the maintenance burden?**
A: Binding layers: Standard maintenance per language. Agda core: Rarely changes (core logic stable since Phase 3, extensions added in Phases 4-5). Build system: Shake + Cabal, documented in BUILDING.md.

**Q: What if the original developer leaves?**
A: Documentation includes:
- BUILDING.md: Complete build instructions
- CLAUDE.md: AI-assisted development guide
- CONTRIBUTING.md: Contribution guidelines
- Examples: demo scripts covering all four interface tiers

The core is stable. Most changes will be binding-side (adding checks, integrating with tools).

**Q: Can we extend it?**
A: Yes. Extension points:
- Bindings (Python/C++/Go/Rust): Add new DSL methods, integrations, visualizations
- Agda (advanced): Add new LTL operators, signal predicates, DBC features

See CONTRIBUTING.md for guidance on what belongs upstream vs. private.

**Q: What's the performance profile?**
A: Comfortably real-time — a 1 Mbps CAN bus needs ~8,000 fps and a 5 Mbit/s CAN-FD bus ~6,000 fps; every binding clears its bar with margin to spare. See [BENCHMARKS.md](development/BENCHMARKS.md#canonical-results) for the throughput numbers and the real-time headroom.

**Q: Dependencies?**
A: A one-time build-time Haskell/Agda toolchain plus `libgmp-dev`; the runtime is just `libaletheia-ffi.so` and Python 3.14+ (plus your binding's own runtime). There is no published wheel yet — install the Python binding editable from source after building. See [Building Guide § Prerequisites](development/BUILDING.md#prerequisites) for the exact version pins (this is the single source of truth — other docs cross-reference it rather than copying).

---

## For Engineering Managers

**Business case**:

**Value proposition**: Reduce CAN signal extraction bugs to zero. Prove temporal properties hold across all traces, not just test cases.

**ROI timeline**:
- **Weeks 1-2**: Integration and team training
- **Weeks 3-4**: Apply to non-critical verification tasks (learn the tool)
- **Months 2-3**: Deploy on safety-critical properties (where bugs are costly)
- **Ongoing**: Catch bugs in production that testing would miss

**Cost structure**:
- **Upfront**: Integration (1-2 weeks), training (binding-API engineers: 1 day, Agda maintainer: 1-2 weeks)
- **Ongoing**: Maintenance (minimal for stable core, standard for the binding APIs)

**Risk management**:

| Risk Type | Assessment | Mitigation |
|-----------|------------|------------|
| **Technical** | Medium | Proven toolchain (Agda/GHC), comprehensive docs, AI-assisted maintenance |
| **People** | Medium-High | Clear docs, external contractors available, gradual adoption |
| **Legal** | Low | Permissive license (BSD 2-Clause), no known patent issues |
| **Compliance** | Low (helps) | Formal methods strengthen the ISO 26262 (automotive functional safety) compliance story |

**Decision framework**:

**Green light if**:
- Safety-critical CAN analysis (ASIL-C/D — the higher automotive safety integrity levels)
- High cost of signal extraction bugs (recalls, field failures)
- Need mathematical guarantees beyond testing
- Team willing to learn new tools

**Yellow light if**:
- Only non-critical applications (testing may suffice)
- Extremely tight performance requirements beyond current throughput (see [BENCHMARKS.md](development/BENCHMARKS.md#canonical-results))
- Team strongly resistant to new technologies

**Red light if**:
- No CAN bus analysis needs
- Build environment cannot support Linux toolchain
- Legal/compliance team rejects BSD 2-Clause license

**Competitive advantage**: Few tools offer proven-correct CAN analysis. Most automotive testing is example-based. Formal verification is a differentiator for safety-critical systems.

---

## Current Status

**Phase 5.1 complete** ✅ — all four binding stacks (Python, C++, Go, Rust) at functional parity on the verified core (signal extraction, LTL checking, DBC handling, and the four-tier check interface), plus the matrix gates, DBC text parser, cancellation, doc-example harness, and VAL_ promotion all complete. Host-surface features (the CLI, log-file reading) remain Python-led — see the per-binding notes below. See [PROJECT_STATUS.md](../PROJECT_STATUS.md) for the authoritative status and metrics.

- Core infrastructure (parser, CAN encoding/decoding, DBC parser in the verified Agda kernel)
- LTL verification with streaming architecture
- Formal correctness proofs (parser, CAN encoding, LTL adequacy, DSL roundtrip)
- DBC validator with formal proof — 23 structural checks, proven **sound and complete**; it certifies the DBC is well-formed, the precondition the decode proof relies on (see [PROJECT_STATUS.md](../PROJECT_STATUS.md) for details)
- Python, C++, Go, and Rust APIs with signal operations (in-process shared library, no subprocess)
- Four-tier interface: Check API, YAML, Excel, DSL
- **CLI ships today** — the Python CLI has six subcommands (`python3 -m aletheia {check,validate,extract,signals,format-dbc,mux-query}`); the C++ and Go host CLIs ship five of those (`check` deferred — it needs a verified CAN-log reader); Rust has a typed client today, with a CLI planned for Phase 6.
- CAN log reader (ASC, BLF, CSV, DB, candump .log, MF4, TRC via python-can)
- Enriched violation diagnostics (signal name, value, condition)
- Comprehensive automated test suites across all four bindings (unit, property-based, cross-binding parity, and doc-example harnesses)
- High-throughput streaming via binary FFI across all four bindings (see [BENCHMARKS.md](development/BENCHMARKS.md#canonical-results) for current benchmarks)

**Phase 5**: CAN-FD, binary FFI (streaming + signal extraction + frame build/update), C++/Go/Rust bindings, cross-language benchmarks — all delivered. Phase 6 candidate goals: CLI parity for C++/Go (`check` subcommand) and a Rust CLI, python-can replacement (Agda+proof for ASC/BLF parsers), GHC `--bignum=native` rebuild (LGPL contingency for libgmp), SOME/IP. See [PROJECT_STATUS.md](../PROJECT_STATUS.md) for detailed status.

---

## Honest Assessment

**Strengths**:
- Mathematical guarantees of correctness (unique in CAN tooling)
- Exact rational arithmetic end-to-end — decoded values never drift by a floating-point rounding step
- Proven technology stack (Agda/Haskell used in high-assurance systems)
- Python, C++, Go, and Rust bindings hide the complexity
- CAN-FD support (variable-length payloads up to 64 bytes, DLC 0-15)
- Real-world tested (OpenDBC corpus, multiplexed signals, 29-bit IDs)
- High streaming throughput with real-time headroom — even the slowest binding on the slowest lane clears a live CAN-FD bus by ~3×, and the streaming lanes by far more ([benchmarks](development/BENCHMARKS.md#canonical-results))

**Limitations**:
- Learning curve for Agda core maintenance (binding APIs and Check API are easy)
- Small ecosystem (fewer community resources than mainstream-only tools)
- No published package yet — install is build-from-source (no `pip install aletheia` wheel today)

**Best fit for**:
- Safety-critical CAN verification (ASIL-C/D)
- Temporal property checking (LTL over traces)
- Teams willing to adopt proven but less common tools
- Organizations valuing correctness over development speed

**Not ideal for**:
- Rapid prototyping (use Python/pandas initially)
- Teams requiring a single-language stack with no compiled dependencies
- Projects with no formal verification requirements

---

## Try It

There is no published wheel yet, so start with a one-time build; after that, the lowest-effort way to *use* Aletheia needs no code at all.

**Step 1 — build once (from source):**
```bash
git clone <repository>
cd aletheia
cabal run shake -- build            # one-time: compiles the verified core → libaletheia-ffi.so
cd python
python3 -m venv .venv
source .venv/bin/activate        # fish: source .venv/bin/activate.fish
pip install -e '.[can]'          # editable from source — there is no published wheel yet
cd ..
```

**Step 2 — no code to write (the CLI).** A matched sample set ships in `examples/demo/` (vehicle.dbc, vehicle_checks.yaml, drive.log), so this runs straight through:
```bash
cd examples/demo
aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml drive.log
# The sample drive speeds past its limit, so it exits 1.
# exit 0 = all checks passed · 1 = violations (with timestamps) · 2 = error
```

**Or script it in Python:**
```bash
python3 examples/simple_verification.py
```

See [BUILDING.md](development/BUILDING.md) for detailed instructions.

**Questions?**

- Interfaces: See [Interface Guide](reference/INTERFACES.md) (Check API, YAML, Excel)
- Language APIs: [Python](reference/PYTHON_API.md) · [C++](reference/CPP_API.md) · [Go](reference/GO_API.md) · [Rust](reference/RUST_API.md)
- Architecture: See [Architecture Overview](architecture/DESIGN.md)
- Contributing: See [CONTRIBUTING.md](../CONTRIBUTING.md)

---

## Bottom Line

**For engineers**: Use a proven-correct library — in Python, C++, Go, or Rust — instead of hoping your tests caught everything.

**For team leads**: Formal verification reduces long-term maintenance cost by eliminating a class of bugs.

**For engineering managers**: High-assurance systems justify the upfront investment. For safety-critical work, formal methods are becoming table stakes.

Aletheia brings proof-backed correctness to automotive CAN analysis. The question is whether your use case justifies the investment in learning and integration. For safety-critical systems, the answer is likely yes.
</content>

# Aletheia: Project Pitch

**Formally verified CAN frame analysis with Linear Temporal Logic (LTL)**
**Last Updated**: 2026-04-15

LTL is a formal method for specifying and verifying properties of sequences — in this case, proving that CAN bus signals stay within safe bounds over time.

This document explains what Aletheia is, why it exists, and what it means for your team to adopt it.

---

## What is Aletheia?

Aletheia is a library for analyzing automotive CAN bus data with **mathematical guarantees of correctness**, with bindings for Python, C++, and Go. You write temporal properties (e.g., "Speed never exceeds 220 km/h"), and Aletheia verifies them against CAN traces with proofs that the checker itself is bug-free.

**Elevator pitch**: Testing shows the presence of bugs. Formal verification proves their absence. Aletheia brings proof-backed CAN analysis to engineers (Python, C++, Go) without requiring a PhD in formal methods.

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
   Check.signal("Speed").never_exceeds(220)                          # Python
   ```
   ```cpp
   Check::signal("Speed").never_exceeds(PhysicalValue{220});         // C++
   ```
   ```go
   CheckSignal("Speed").NeverExceeds(220)                            // Go
   ```

2. **Formally verified core**: Signal extraction and LTL checking implemented in Agda with mathematical proofs of correctness

3. **Streaming architecture**: Process gigabyte-scale CAN traces with O(1) memory (verified 1.08× memory growth across a 100× trace increase; ~109k fps on the **Stream LTL** lane of the C++ binary FFI path — CAN 2.0B, 2 always-true range properties, Ryzen 9 5950X, 10k frames × 5 runs. Other lanes — Signal Extraction, Frame Building — and other property shapes have different numbers; see [PROJECT_STATUS.md § Key Metrics](../PROJECT_STATUS.md#key-metrics) for the full table.)

4. **DBC integration**: Parse real-world DBC files (tested against OpenDBC corpus)

**Key insight**: You write Python, C++, or Go. The proof burden lives in Agda. If the code type-checks, it's correct by construction.

---

## Why Formal Verification?

**Testing** shows the presence of bugs. **Formal verification** proves their absence.

| Approach | What it provides | What it misses |
|----------|------------------|----------------|
| Unit tests | Examples of correct behavior | Edge cases, unexpected inputs |
| Property-based testing | Random exploration | Exhaustive coverage guarantees |
| **Formal verification** | **Mathematical proof of correctness** | **Nothing (within specified properties)** |

**What the proofs don't cover** (important to set expectations):

- **Specification errors**: The proofs guarantee the implementation matches the stated properties, not that the properties are the right ones. "Speed extraction returns the value encoded by the DBC" is proven; whether that DBC is correct for your vehicle is an engineering question.
- **Hardware, bus layer, and OS behaviour**: Bit-stuffing errors on the physical CAN bus, ECU faults, timestamp skew from the logger hardware, and kernel scheduling all sit below Aletheia's abstraction boundary.
- **Integration and operator error**: Wiring the wrong log file, missing a property, misreading a YAML threshold — these are normal human-process risks and must be covered by the surrounding tooling and review practices.
- **Third-party components**: Agda's `--safe` kernel, GHC, and the Haskell `base` + `aeson` used in the shim are trusted rather than verified. Compiler and runtime bugs at that level propagate through.

In other words: Aletheia eliminates the class of bugs where "the signal extraction code was wrong" or "the LTL evaluator drifted over a long trace" — not bugs elsewhere in the system.

**Example**:
- Test: "Speed extraction works for 100 km/h" ✓
- Proof: "Speed extraction is correct for all 64-bit integers in all byte orders" ✓✓✓

**Trade-off**: Higher upfront cost (writing proofs), lower long-term cost (no signal extraction bugs, ever).

---

## Technology Stack

Aletheia uses a three-layer architecture:

```
Python / C++ / Go (user-facing APIs, FFI)
   ↓ FFI (shared library via ctypes / dlopen)
Haskell (FFI wrapper → libaletheia-ffi.so)
   ↓
Agda (all logic + proofs, compiled via MAlonzo)
```

**Why these technologies?**

- **Agda**: A proof assistant where code that type-checks is mathematically proven correct — similar to how Rust's compiler guarantees memory safety, but for logical correctness. Used in aerospace, cryptography, and compilers.
- **Haskell**: Mature compiler (GHC) for Agda-generated code. Industry-proven (Meta, Standard Chartered, IOHK). Compiled to a shared library loaded by all bindings.
- **Python / C++ / Go**: Familiar interfaces for automotive engineers. All complexity hidden behind FFI (Foreign Function Interface — each language's standard mechanism for calling compiled code directly, with no subprocess overhead).

**Proven track record**:
- Agda: Used in verified compilers (Agda-to-Haskell compiler itself), verified data structures, and verified network protocols
- Haskell: Used in production at scale (>1M LoC codebases at Meta, Standard Chartered, IOHK)
- Formal methods stack: Same class of tools as CompCert (verified C compiler) and seL4 (verified microkernel)

---

## Risks and Mitigations

### Technical Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Build complexity** | Requires Agda + GHC + Cabal | Low | Documented build process, tested on Ubuntu/Debian/WSL2. |
| **Toolchain maturity** | Agda ecosystem smaller than Python | Low | Agda 2.8.0 is stable. GHC is industry-proven. Only standard library dependencies. |
| **Performance** | Formal verification adds overhead | Low | High-throughput streaming via binary FFI across all three bindings (see [PROJECT_STATUS.md](../PROJECT_STATUS.md#key-metrics) for current benchmarks). Sufficient for 1 Mbps CAN bus real-time analysis. |
| **Agda learning curve** | Modifying core requires expertise | Medium | Python API is stable. Core changes rare. Can contract experts if needed. |

### People Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **Bus factor** | Knowledge concentrated in one person | High initially | Documentation emphasizes maintainability. CLAUDE.md provides AI-assisted development guide. |
| **Hiring difficulty** | Agda experts are rare | Medium | Not needed for Python API users. For core development: remote contractors available, or train interested engineers. |
| **Team resistance** | "Not invented here" / unfamiliar tech | Medium | Start with non-critical use cases. Demonstrate value before mandating adoption. |

### Legal/Compliance Risks

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **License compatibility** | BSD 2-Clause vs. company policy | Low | Permissive license, allows proprietary use. No copyleft. |
| **Patent issues** | Agda/GHC patents | Very Low | Agda is open source (MIT). GHC is open source (BSD 3-Clause). No known patent issues. |
| **Regulatory acceptance** | Formal methods not in compliance checklist | Medium | Formal verification **strengthens** compliance story. ISO 26262 (the automotive functional safety standard) encourages formal methods for ASIL-D (the highest safety integrity level). |

---

## For Engineers

**What you need to know**: How to use the API in your language. That's it.

**What you don't need to know**: Agda, Haskell, formal verification theory.

**Four ways to define checks** (all compile to the same verified core):

Python:
```python
Check.signal("Speed").never_exceeds(220)            # Check API
load_checks("checks.yaml")                          # YAML
load_checks_from_excel("tests.xlsx")                # Excel
Signal("Speed").less_than(220).always()              # Full DSL
```

C++:
```cpp
Check::signal("Speed").never_exceeds(PhysicalValue{220});
load_checks_from_yaml("checks.yaml");
load_checks_from_excel("tests.xlsx");
// LTL formulas via ltl:: namespace (compositional, not fluent DSL):
auto f = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220})));
```

Go:
```go
aletheia.CheckSignal("Speed").NeverExceeds(220)
aletheia.LoadChecksFromYAML("checks.yaml")
aletheia.LoadChecksFromExcel("tests.xlsx")
// LTL formulas via ltl package (compositional):
f := ltl.Always(ltl.Atomic(ltl.LessThan("Speed", 220)))
```

**Streaming workflow** (Python shown; C++ and Go follow the same pattern):

```python
from aletheia import AletheiaClient, Check
from aletheia.dbc_converter import dbc_to_json
from aletheia.can_log import iter_can_log

dbc = dbc_to_json("vehicle.dbc")
checks = [Check.signal("Speed").never_exceeds(220)]

with AletheiaClient() as client:
    client.parse_dbc(dbc)
    client.add_checks(checks)
    client.start_stream()

    for ts, can_id, dlc, data in iter_can_log("drive.blf"):
        response = client.send_frame(ts, can_id, dlc, data)
        if response.get("status") == "fails":
            print(f"Violation at {response['timestamp']['numerator']}us")

    client.end_stream()
```

**Learning curve**: If you can use a standard library in your language, you can use Aletheia. All three bindings follow the same workflow and produce identical verification results — surface APIs use each language's idioms (Python fluent DSL, C++ strong types + `std::expected`, Go interfaces + functional options) but the protocol-level behavior is the same.

**Debugging**: Violations include counterexamples (frame number, signal values). Standard debugging in your language applies.

**Testing**: Write unit tests for your properties, just like any other code. The difference: Aletheia's checker is proven correct, so if your property is right, it will catch bugs.

---

## For Team Leads

**Integration questions**:

**Q: How does this fit into our CI/CD pipeline?**
A: Aletheia provides Python, C++, and Go bindings. Integrate like any test suite in your language. Run `pytest tests/` in CI for Python. Checks can also be defined in YAML for version-controlled CI configurations.

**Q: What's the maintenance burden?**
A: Binding layers: Standard maintenance per language. Agda core: Rarely changes (core logic stable since Phase 3, extensions added in Phases 4-5). Build system: Shake + Cabal, documented in BUILDING.md.

**Q: What if the original developer leaves?**
A: Documentation includes:
- BUILDING.md: Complete build instructions
- CLAUDE.md: AI-assisted development guide (400+ lines)
- CONTRIBUTING.md: Contribution guidelines
- Examples: 11 demo scripts covering all four interface tiers

The core is stable. Most changes will be binding-side (adding checks, integrating with tools).

**Q: Can we extend it?**
A: Yes. Extension points:
- Bindings (Python/C++/Go): Add new DSL methods, integrations, visualizations
- Agda (advanced): Add new LTL operators, signal predicates, DBC features

See CONTRIBUTING.md for guidance on what belongs upstream vs. private.

**Q: What's the performance profile?**
A: Sufficient for real-time analysis of 1 Mbps CAN bus traffic (requires ~8,000 fps). See [PROJECT_STATUS.md](../PROJECT_STATUS.md#key-metrics) for current throughput benchmarks.

**Q: Dependencies?**
A: Build-time: Agda 2.8.0, GHC 9.4.x/9.6.x, Cabal 3.12+. Runtime: `libaletheia-ffi.so` (shared library). Python: 3.12+. No exotic dependencies.

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
- **Upfront**: Integration (1-2 weeks), training (Python engineers: 1 day, Agda maintainer: 1-2 weeks)
- **Ongoing**: Maintenance (minimal for stable core, standard for Python API)

**Risk management**:

| Risk Type | Assessment | Mitigation |
|-----------|------------|------------|
| **Technical** | Medium | Proven toolchain (Agda/GHC), comprehensive docs, AI-assisted maintenance |
| **People** | Medium-High | Clear docs, external contractors available, gradual adoption |
| **Legal** | Low | Permissive license (BSD 2-Clause), no known patent issues |
| **Compliance** | Low (helps) | Formal methods strengthen ISO 26262 / DO-178C compliance story |

**Decision framework**:

**Green light if**:
- Safety-critical CAN analysis (ASIL-C/D — the higher automotive safety integrity levels)
- High cost of signal extraction bugs (recalls, field failures)
- Need mathematical guarantees beyond testing
- Team willing to learn new tools

**Yellow light if**:
- Only non-critical applications (testing may suffice)
- Extremely tight performance requirements beyond current throughput (see [PROJECT_STATUS.md](../PROJECT_STATUS.md#key-metrics))
- Team strongly resistant to new technologies

**Red light if**:
- No CAN bus analysis needs
- Build environment cannot support Linux toolchain
- Legal/compliance team rejects BSD 2-Clause license

**Competitive advantage**: Few tools offer proven-correct CAN analysis. Most automotive testing is example-based. Formal verification is a differentiator for safety-critical systems.

---

## Current Status

**Phase 5.1 complete** ✅ — all four binding stacks (Python, C++, Go, plus the LSP/CLI tooling) are at cross-language parity. See [PROJECT_STATUS.md](../PROJECT_STATUS.md) for the authoritative status and metrics.

- Core infrastructure (parser, CAN encoding/decoding, DBC parser)
- LTL verification with streaming architecture
- Formal correctness proofs (parser, CAN encoding, LTL adequacy, DSL roundtrip)
- DBC validator with formal proof (soundness + completeness; see [PROJECT_STATUS.md](../PROJECT_STATUS.md) for details)
- Python API with signal operations (FFI, no subprocess)
- Four-tier interface: Check API, YAML, Excel, DSL
- CLI tool (`python3 -m aletheia check/validate/extract/signals`)
- CAN log reader (ASC, BLF, CSV, DB, candump .log, MF4, TRC via python-can)
- Enriched violation diagnostics (signal name, value, condition)
- 1000+ tests across Python, C++, and Go (see [PROJECT_STATUS.md](../PROJECT_STATUS.md#key-metrics) for current counts)
- High-throughput streaming via binary FFI across Python/C++/Go (see [PROJECT_STATUS.md](../PROJECT_STATUS.md#key-metrics) for current benchmarks)

**Phase 5**: CAN-FD, binary FFI, C++/Go bindings, cross-language benchmarks — all delivered. Remaining: SOME/IP exploration, binary FFI for signal extraction. See [PROJECT_STATUS.md](../PROJECT_STATUS.md) for detailed status.

---

## Honest Assessment

**Strengths**:
- Mathematical guarantees of correctness (unique in CAN tooling)
- Proven technology stack (Agda/Haskell used in high-assurance systems)
- Python, C++, and Go bindings hide complexity
- CAN-FD support (variable-length payloads up to 64 bytes, DLC 0-15)
- Real-world tested (OpenDBC corpus, multiplexed signals, 29-bit IDs)

**Limitations**:
- Performance: Sufficient for 1 Mbps CAN bus real-time analysis and multi-bus (see Technical Risks table for current throughput numbers)
- Learning curve for Agda core maintenance (binding APIs and Check API are easy)
- Small ecosystem (fewer community resources than mainstream-only tools)

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

**Quick start**:
```bash
git clone <repository>
cd aletheia
cabal run shake -- build
python3 -m venv .venv
source .venv/bin/activate        # fish: source .venv/bin/activate.fish
cd python && pip install -e . && cd ..
python3 examples/simple_verification.py
```

See [BUILDING.md](development/BUILDING.md) for detailed instructions.

**Questions?**

- Interfaces: See [Interface Guide](reference/INTERFACES.md) (Check API, YAML, Excel)
- Python API: See [Python API Guide](reference/PYTHON_API.md)
- Architecture: See [Architecture Overview](architecture/DESIGN.md)
- Contributing: See [CONTRIBUTING.md](../CONTRIBUTING.md)

**For stakeholders / talks**: A standalone HTML slide deck lives at [`docs/presentation/index.html`](presentation/index.html) — open it directly in a browser.

---

## Bottom Line

**For engineers**: Use a proven-correct library — in Python, C++, or Go — instead of hoping your tests caught everything.

**For team leads**: Formal verification reduces long-term maintenance cost by eliminating a class of bugs.

**For engineering managers**: High-assurance systems justify the upfront investment. For safety-critical work, formal methods are becoming table stakes.

Aletheia brings proof-backed correctness to automotive CAN analysis. The question is whether your use case justifies the investment in learning and integration. For safety-critical systems, the answer is likely yes.

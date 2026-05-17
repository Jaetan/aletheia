# Aletheia Documentation Index

**Quick Navigation**: Complete guide to all Aletheia documentation organized by audience and purpose.

---

## For New Users

Start here:

1. **[Quick Start](guides/QUICKSTART.md)** - 5-minute verification walkthrough (assumes built library)
2. **[README](../README.md)** - Project overview
3. **[PITCH](PITCH.md)** - Why use Aletheia? Elevator pitch for stakeholders

---

## Guides

Learn Aletheia step by step:

- **[Quick Start](guides/QUICKSTART.md)** - 5-minute path: define checks, run, interpret results
- **[Tutorials](guides/TUTORIAL.md)** - End-to-end walkthroughs by role (start here if new to Aletheia)
- **[Cookbook](guides/COOKBOOK.md)** - Copy-paste solutions to specific problems: signal bounds, causal checks, CAN logs, signal operations, CLI patterns

---

## API Reference

Complete API documentation:

- **[Interface Guide](reference/INTERFACES.md)** - Check API, YAML loader, Excel loader (start here)
- **[Python API Guide](reference/PYTHON_API.md)** - Raw DSL (Signal, Predicate, Property) and AletheiaClient
- **[CLI Reference](reference/CLI.md)** - `python3 -m aletheia` subcommands: check, validate, extract, signals, format-dbc, mux-query
- **[JSON Protocol](architecture/PROTOCOL.md)** - Low-level protocol specification (advanced)

---

## Architecture & Design

Understand how Aletheia works:

- **[Design Overview](architecture/DESIGN.md)** - Three-layer architecture, design decisions, and rationale
- **[Cancellation Contract](architecture/CANCELLATION.md)** - Cross-binding async/sync cancellation semantics (Python `asyncio`, Go `context.Context`, C++ `std::stop_token`)
- **[cgo / dlopen Notes](architecture/CGO_NOTES.md)** - Go binding's cgo + dlopen rationale, GHC RTS thread pinning, build constraints

---

## Operations

For deployment and on-call:

- **[Operations Runbook](operations/RUNBOOK.md)** - Symptom → cause → action for every structured log event and every documented failure mode (build, runtime, cancellation, input bounds, OOM, validation rejection)
- **[Long-Run Stability Bench](operations/STABILITY.md)** - Per-binding harnesses for RSS / FD / handle-count drift detection across ≥ 1M frames; spec at `docs/STABILITY_BENCH.yaml`, gated by `tools/check_stability_bench.py` (static) + `tools/stability_run.py` (dynamic, opt-in via `ALETHEIA_STABILITY_CHECK=1`)
- **[Mutation Testing](operations/MUTATION.md)** - Per-binding mutation testing infrastructure (Python `mutmut`, Go `gremlins`, C++ `Mull`); threshold model, install procedure, forward-revert verification protocol

---

## Development

Build and contribute:

1. **[Building Guide](development/BUILDING.md)** - Setup, installation, and development workflow
2. **[Distribution Guide](development/DISTRIBUTION.md)** - Packaging and integrating `libaletheia-ffi.so` into C, C++, and Go projects
3. **[Local CI](development/CI_LOCAL.md)** - Three-layer CI architecture (always-on / opt-in / external); pre-push hook; orchestrator (`tools/run_ci.py`)
4. **[Release Guide](development/RELEASE.md)** - Tagging, signing (cosign), publishing, and supply-chain verification procedure
5. **[Parity Plan](development/PARITY_PLAN.md)** - Cross-binding feature parity roadmap (Tracks A–E + post-R17 follow-ups); paired with `docs/FEATURE_MATRIX.yaml`
6. **[Contributing Guide](../CONTRIBUTING.md)** - Contribution policy and workflow
7. **[CLAUDE.md](../CLAUDE.md)** - AI-assisted development guide and module structure
8. **[Project Status](../PROJECT_STATUS.md)** - Current phase, completed deliverables, and roadmap
9. **[CHANGELOG](../CHANGELOG.md)** - Public-API change log (per `[Added]` / `[Changed]` / `[Removed]` per AGENTS.md "Public API stability and CHANGELOG discipline")

---

## Examples

Learn by example:

- **[Examples Directory](../examples/)** - Sample DBC files and verification scripts
- **[Examples README](../examples/README.md)** - Curated index of demo scripts and support files
- **[Demo Scripts](../examples/demo/)** - demo scripts covering Check API, YAML/Excel loaders, DBC validation, streaming, fault injection, and LTL property checking (see the examples README above for the authoritative inventory)

---

## Benchmarks

- **[Benchmarks Guide](development/BENCHMARKS.md)** - Cross-language runner, per-binding scripts, and measurement methodology (canonical numbers in [PROJECT_STATUS.md § Key Metrics](../PROJECT_STATUS.md#key-metrics))

---

## Additional Resources

- **[LICENSE](../LICENSE.md)** - BSD 2-Clause License
- **[Python Package README](../python/README.md)** - Installation via pip
- **[DEPENDENCIES.md](../DEPENDENCIES.md)** - Third-party runtime dependencies and their licenses
- **Deferred / NO-FIX items** - Each item's rationale lives as an in-source comment block at the call site (search `DEFERRED — TRACKED` or `DO NOT RE-RAISE IN REVIEW`).  Round-scope working file: `review-rN-findings.md` (latest round in the repo root).
- **[AGENTS.md](../AGENTS.md)** - Per-language coding standards and review categories (canonical source for AI-assisted and human code review)
- **[Presentation](presentation/index.html)** - Slide deck for talks and demos (open in browser)

---

## Documentation Map

```
aletheia/
├── README.md                          # Main entry point
├── CLAUDE.md                          # AI development guide
├── CONTRIBUTING.md                    # Contribution guidelines
├── PROJECT_STATUS.md                  # Phase tracking (canonical metrics)
├── CHANGELOG.md                       # Public-API change log
├── LICENSE.md                         # Legal
├── AGENTS.md                          # Per-language coding standards / review categories
├── DEPENDENCIES.md                    # Third-party dependencies & licenses
├── review-r20-findings.md             # Round-scope working file (per-round, latest round in repo root)
├── .session-state.md                  # Session recovery + resume instructions (AI-assisted dev)
│
├── docs/
│   ├── INDEX.md                       # THIS FILE - Navigation hub
│   ├── PITCH.md                       # Elevator pitch
│   │
│   ├── guides/
│   │   ├── QUICKSTART.md              # 5-minute quick start
│   │   ├── TUTORIAL.md                # End-to-end walkthroughs
│   │   └── COOKBOOK.md                # Problem-driven recipes
│   │
│   ├── reference/
│   │   ├── INTERFACES.md              # Check API, YAML, Excel
│   │   ├── PYTHON_API.md              # Raw DSL and AletheiaClient
│   │   └── CLI.md                     # CLI subcommands (check / validate / extract / signals / format-dbc / mux-query)
│   │
│   ├── architecture/
│   │   ├── DESIGN.md                  # Architecture overview
│   │   ├── PROTOCOL.md                # JSON protocol spec
│   │   ├── CANCELLATION.md            # Cross-binding cancellation contract
│   │   └── CGO_NOTES.md               # Go cgo + dlopen rationale
│   │
│   ├── operations/
│   │   ├── RUNBOOK.md                 # Symptom → cause → action runbook
│   │   ├── STABILITY.md               # Long-run stability harnesses (RSS / FD drift)
│   │   └── MUTATION.md                # Mutation testing (mutmut / gremlins / Mull)
│   │
│   ├── development/
│   │   ├── BUILDING.md                # Build instructions
│   │   ├── BENCHMARKS.md              # Benchmark suite and methodology
│   │   ├── DISTRIBUTION.md            # Packaging & native integration
│   │   ├── CI_LOCAL.md                # Three-layer CI architecture
│   │   ├── RELEASE.md                 # Tag / sign / publish procedure
│   │   └── PARITY_PLAN.md             # Cross-binding feature parity roadmap
│   │
│   └── presentation/
│       └── index.html                 # Slide deck for talks and demos
│
└── examples/
    ├── README.md                      # Curated index of demo scripts
    ├── example.dbc                    # Sample CAN 2.0B DBC file
    ├── example_canfd.dbc              # Sample CAN-FD DBC file
    ├── simple_verification.py         # Standalone verification example
    └── demo/                          # Demo scripts + support files
```

---

**Maintained By**: Aletheia Team

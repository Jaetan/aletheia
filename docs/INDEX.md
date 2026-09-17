# Aletheia Documentation Index

**Quick Navigation**: Complete guide to all Aletheia documentation organized by audience and purpose.

---

## For New Users

Start here:

1. **[Quick Start](guides/QUICKSTART.md)** - 5-minute verification walkthrough (assumes built library)
2. **[README](../README.md)** - Project overview
3. **[PITCH](PITCH.md)** - Why use Aletheia? Elevator pitch for stakeholders
4. **[Glossary](GLOSSARY.md)** - Plain-language definitions of CAN, LTL, DBC, MAlonzo, and the other domain terms (read this first if the jargon is unfamiliar)

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
- **[C++ API Guide](reference/CPP_API.md)** - `AletheiaClient`, Check API, and the `ltl::` DSL
- **[Go API Guide](reference/GO_API.md)** - `Client`, Check API, and the LTL DSL
- **[Rust API Guide](reference/RUST_API.md)** - `Client`, Check API, the typed DBC model, and the async client
- **[CLI Reference](reference/CLI.md)** - `python3 -m aletheia` subcommands: check, validate, extract, signals, format-dbc, mux-query

---

## Architecture & Design

Understand how Aletheia works:

- **[Design Overview](architecture/DESIGN.md)** - Three-layer architecture, design decisions, and rationale
- **[JSON Protocol](architecture/PROTOCOL.md)** - Low-level FFI protocol + the IssueCode error-code reference
- **[CAN ID Representation](architecture/CANID_REPRESENTATION.md)** - Standard (11-bit) vs extended (29-bit) IDs and the validated `CANID` newtype
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

- **[Building Guide](development/BUILDING.md)** - Setup, installation, the development workflow, and the [toolchain support policy](development/BUILDING.md#toolchain-support-policy)
- **[Distribution Guide](development/DISTRIBUTION.md)** - Packaging and integrating `libaletheia-ffi.so` into C, C++, and Go projects
- **[Local CI](development/CI_LOCAL.md)** - Three-layer CI architecture (always-on / opt-in / external); pre-push hook; orchestrator (`tools/run_ci.py`)
- **[Branch & PR Hygiene](development/BRANCH_PR_HYGIENE.md)** - The local-first + server-enforced gate model, required checks, and merge rules for `main`
- **[Release Guide](development/RELEASE.md)** - Tagging, signing (cosign), publishing, and supply-chain verification procedure
- **[Resource Parameters](development/RESOURCE_PARAMETERS.md)** - How every number in `RESOURCE_BUDGETS.yaml` was arrived at, and what would change it
- **[Feature Matrix](FEATURE_MATRIX.yaml)** - Cross-binding feature parity matrix, the canonical record of which capability each binding (Python / C++ / Go / Rust / CLI) supports, and why any gap exists
- **[SOME/IP Design Draft](development/SOMEIP_DESIGN.md)** - Proposed architecture for SOME/IP support (verified monitor over captured traffic; one shared library; parameterized LTL kernel), a draft and not scheduled
- **[Contributing Guide](../CONTRIBUTING.md)** - Contribution policy and workflow
- **[CLAUDE.md](../CLAUDE.md)** - AI-assisted development guide and module structure
- **[Project Status](../PROJECT_STATUS.md)** - Current phase, completed deliverables, and roadmap
- **[CHANGELOG](../CHANGELOG.md)** - Public-API change log (per `[Added]` / `[Changed]` / `[Removed]` per AGENTS.md "Public API stability and CHANGELOG discipline")

---

## Examples

Learn by example:

- **[Examples Directory](../examples/)** - Sample DBC files and verification scripts
- **[Examples README](../examples/README.md)** - Curated index of demo scripts and support files
- **[Demo Scripts](../examples/demo/)** - demo scripts covering Check API, YAML/Excel loaders, DBC validation, streaming, fault injection, and LTL property checking (see the examples README above for the authoritative inventory)

---

## Benchmarks

- **[Benchmarks Guide](development/BENCHMARKS.md)** - Cross-language runner, per-binding scripts, and measurement methodology (with the canonical results table)

---

## Additional Resources

- **[LICENSE](../LICENSE.md)** - BSD 2-Clause License
- **[Python Package README](../python/README.md)** - Installation via pip
- **[DEPENDENCIES.md](../DEPENDENCIES.md)** - Third-party runtime dependencies and their licenses
- **Deferred / NO-FIX items** - Each item's rationale lives as an in-source comment block at the call site (search `DEFERRED — TRACKED`).
- **[AGENTS.md](../AGENTS.md)** - Per-language coding standards and review categories (canonical source for AI-assisted and human code review), with one file per scope beside it: [Agda](../AGENTS/agda.md), [C++](../AGENTS/cpp.md), [Go](../AGENTS/go.md), [Python](../AGENTS/python.md), [Rust](../AGENTS/rust.md), [documentation](../AGENTS/docs.md) and [continuous integration](../AGENTS/cicd.md)

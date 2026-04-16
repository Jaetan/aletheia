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
- **[CLI Reference](reference/CLI.md)** - `python3 -m aletheia` subcommands: check, validate, extract, signals, mux-query
- **[JSON Protocol](architecture/PROTOCOL.md)** - Low-level protocol specification (advanced)

---

## Architecture & Design

Understand how Aletheia works:

- **[Design Overview](architecture/DESIGN.md)** - Three-layer architecture, design decisions, and rationale

---

## Development

Build and contribute:

1. **[Building Guide](development/BUILDING.md)** - Setup, installation, and development workflow
2. **[Distribution Guide](development/DISTRIBUTION.md)** - Packaging and integrating `libaletheia-ffi.so` into C, C++, and Go projects
3. **[Contributing Guide](../CONTRIBUTING.md)** - Contribution policy and workflow
4. **[CLAUDE.md](../CLAUDE.md)** - AI-assisted development guide and module structure
5. **[Project Status](../PROJECT_STATUS.md)** - Current phase, completed deliverables, and roadmap

---

## Examples

Learn by example:

- **[Examples Directory](../examples/)** - Sample DBC files and verification scripts
- **[Examples README](../examples/README.md)** - Curated index of demo scripts and support files
- **[Demo Scripts](../examples/demo/)** - demo scripts covering Check API, YAML/Excel loaders, DBC validation, streaming, fault injection, and LTL property checking (see the examples README above for the authoritative inventory)

---

## Benchmarks

- **[Python benchmarks README](../python/benchmarks/README.md)** - Cross-language throughput benchmarks and measurement methodology

---

## Additional Resources

- **[LICENSE](../LICENSE.md)** - BSD 2-Clause License
- **[Python Package README](../python/README.md)** - Installation via pip
- **[DEPENDENCIES.md](../DEPENDENCIES.md)** - Third-party runtime dependencies and their licenses
- **[DEFERRALS.md](../DEFERRALS.md)** - Items deliberately deferred out of scope with rationale
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
├── LICENSE.md                         # Legal
├── AGENTS.md                          # Per-language coding standards / review categories
├── DEPENDENCIES.md                    # Third-party dependencies & licenses
├── DEFERRALS.md                       # Deliberately deferred items
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
│   │   └── CLI.md                     # CLI subcommands
│   │
│   ├── architecture/
│   │   ├── DESIGN.md                  # Architecture overview
│   │   └── PROTOCOL.md                # JSON protocol spec
│   │
│   ├── development/
│   │   ├── BUILDING.md                # Build instructions
│   │   └── DISTRIBUTION.md            # Packaging & native integration
│   │
│   └── presentation/
│       └── index.html                 # Slide deck for talks and demos
│
├── examples/
│   ├── README.md                      # Curated index of demo scripts
│   ├── example.dbc                    # Sample CAN 2.0B DBC file
│   ├── example_canfd.dbc              # Sample CAN-FD DBC file
│   ├── simple_verification.py         # Standalone verification example
│   └── demo/                          # Demo scripts + support files
│
└── python/benchmarks/
    └── README.md                      # Cross-language benchmark methodology
```

---

**Last Updated**: 2026-04-15
**Maintained By**: Aletheia Team

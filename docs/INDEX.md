# Aletheia Documentation Index

**Quick Navigation**: Complete guide to all Aletheia documentation organized by audience and purpose.

---

## For New Users

Start here:

1. **[Quick Start](guides/QUICKSTART.md)** - 5 minutes from zero to a working verification
2. **[README](../README.md)** - Project overview
3. **[PITCH](PITCH.md)** - Why use Aletheia? Elevator pitch for stakeholders

---

## Guides

Learn Aletheia step by step:

- **[Quick Start](guides/QUICKSTART.md)** - 5-minute path: define checks, run, interpret results
- **[Tutorials](guides/TUTORIAL.md)** - End-to-end walkthroughs for four audience paths (Technician, Test Engineer, Python Scripter, Developer)
- **[Cookbook](guides/COOKBOOK.md)** - Problem-driven recipes: signal bounds, causal checks, CAN logs, signal operations, CLI patterns

---

## API Reference

Complete API documentation:

- **[Interface Guide](reference/INTERFACES.md)** - Check API, YAML loader, Excel loader (start here)
- **[Python API Guide](reference/PYTHON_API.md)** - Raw DSL (Signal, Predicate, Property) and AletheiaClient
- **[CLI Reference](reference/CLI.md)** - `python -m aletheia` subcommands: check, extract, signals
- **[JSON Protocol](architecture/PROTOCOL.md)** - Low-level protocol specification (advanced)

---

## Architecture & Design

Understand how Aletheia works:

- **[Design Overview](architecture/DESIGN.md)** - Three-layer architecture, design decisions, and rationale

---

## Development

Build and contribute:

1. **[Building Guide](development/BUILDING.md)** - Setup, installation, and development workflow
2. **[Contributing Guide](../CONTRIBUTING.md)** - Contribution policy and workflow
3. **[CLAUDE.md](../CLAUDE.md)** - AI-assisted development guide and module structure
4. **[Project Status](../PROJECT_STATUS.md)** - Current phase, completed deliverables, and roadmap

---

## Examples

Learn by example:

- **[Examples Directory](../examples/)** - Sample DBC files and verification scripts
- **[Demo Scripts](../examples/demo/)** - 11 demo scripts + support files:
  - `demo_check_api.py` - Check API fluent interface (9 checks, all condition types)
  - `demo_yaml_loader.py` - YAML loader with `demo_checks.yaml`
  - `demo_excel_loader.py` - Excel loader: templates, checks, DBC from spreadsheets
  - `demo_all_interfaces.py` - Equivalence proof: DSL == Check API == YAML == Excel
  - `demo.py` - Full presentation: DBC loading, streaming, fault injection
  - `dbc_validation.py` - DBC validation (overlap detection, range consistency)
  - `frame_injection.py` - Real-time frame injection during streaming
  - `drive_log.py` - Sample CAN frame generators
  - `engine_ecu_sim.py` - Engine ECU freeze simulation (staleness demo)
  - `test_engine_naive.py` - Naive unit tests that pass against buggy ECU
  - `demo_ltl_bug.py` - LTL catches frozen alive counter violations
  - `demo_workbook.xlsx` - Persistent Excel workbook for live demos

---

## Additional Resources

- **[LICENSE](../LICENSE.md)** - BSD 2-Clause License
- **[Python Package README](../python/README.md)** - Installation via pip

---

## Documentation Map

```
aletheia/
├── README.md                          # Main entry point
├── CLAUDE.md                          # AI development guide
├── CONTRIBUTING.md                    # Contribution guidelines
├── PROJECT_STATUS.md                  # Phase tracking
├── LICENSE.md                         # Legal
│
├── docs/
│   ├── INDEX.md                       # THIS FILE - Navigation hub
│   ├── PITCH.md                       # Elevator pitch
│   │
│   ├── guides/
│   │   ├── QUICKSTART.md              # 5-minute quick start
│   │   ├── TUTORIAL.md                # End-to-end walkthroughs
│   │   └── COOKBOOK.md                 # Problem-driven recipes
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
│   └── development/
│       └── BUILDING.md                # Build instructions
│
└── examples/
    ├── example.dbc                    # Sample DBC file
    ├── simple_verification.py         # Standalone verification example
    └── demo/                          # Demo scripts + support files
```

---

**Last Updated**: 2026-03-19
**Maintained By**: Aletheia Team

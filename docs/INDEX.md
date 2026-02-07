# Aletheia Documentation Index

**Quick Navigation**: Complete guide to all Aletheia documentation organized by audience and purpose.

---

## For New Users

Start here if you're new to Aletheia:

1. **[README](../README.md)** - Project overview and quick start
2. **[PITCH](PITCH.md)** - Why use Aletheia? Elevator pitch for stakeholders
3. **[Building Guide](development/BUILDING.md)** - Setup and installation instructions
4. **[Interface Guide](development/INTERFACES.md)** - Check API, YAML, Excel (recommended starting point)
5. **[Python API Guide](development/PYTHON_API.md)** - Raw DSL and AletheiaClient reference

---

## API Reference

Complete API documentation:

- **[Interface Guide](development/INTERFACES.md)** - Check API, YAML loader, Excel loader (start here)
- **[Python API Guide](development/PYTHON_API.md)** - Raw DSL (Signal, Predicate, Property) and AletheiaClient
- **[JSON Protocol Specification](architecture/PROTOCOL.md)** - Low-level protocol for advanced users

---

## Architecture & Design

Understand how Aletheia works:

- **[Design Overview](architecture/DESIGN.md)** - Three-layer architecture, design decisions, and rationale

---

## Contributing

Want to contribute to Aletheia?

1. **[Contributing Guide](../CONTRIBUTING.md)** - Contribution policy and workflow
2. **[CLAUDE.md](../CLAUDE.md)** - AI-assisted development guide and module structure
3. **[Project Status](../PROJECT_STATUS.md)** - Current phase, completed deliverables, and roadmap
4. **[Building Guide](development/BUILDING.md)** - Build system and development workflow

---

## Examples & Tutorials

Learn by example:

- **[Examples Directory](../examples/)** - Sample DBC files and verification scripts
- **[Demo Scripts](../examples/demo/)** - Interface demos, DBC validation, frame injection, drive simulation

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
├── .session-state.md                  # Session recovery (internal)
│
├── docs/
│   ├── INDEX.md                       # THIS FILE - Documentation navigation
│   ├── PITCH.md                       # Elevator pitch
│   │
│   ├── architecture/
│   │   ├── DESIGN.md                  # Architecture overview
│   │   └── PROTOCOL.md                # JSON protocol spec
│   │
│   └── development/
│       ├── BUILDING.md                # Build instructions
│       ├── INTERFACES.md              # Check API, YAML, Excel loaders
│       └── PYTHON_API.md              # Raw DSL and AletheiaClient reference
│
└── examples/
    └── demo/                          # Example scripts
        ├── dbc_validation.py          # DBC parsing and validation
        ├── demo.py                    # Drive log generator
        └── frame_injection.py         # Signal extraction and modification
```

---

**Last Updated**: 2026-02-07
**Maintained By**: Aletheia Team

# Aletheia Documentation Index

**Quick Navigation**: Complete guide to all Aletheia documentation organized by audience and purpose.

---

## For New Users

Start here if you're new to Aletheia:

1. **[README](../README.md)** - Project overview and quick start
2. **[PITCH](PITCH.md)** - Why use Aletheia? Elevator pitch for stakeholders
3. **[Building Guide](development/BUILDING.md)** - Setup and installation instructions
4. **[Python API Guide](development/PYTHON_API.md)** - Complete Python DSL reference
5. **[Batch Operations Tutorial](tutorials/BATCH_OPERATIONS.md)** - First hands-on tutorial

---

## API Reference

Complete API documentation:

- **[Python API Guide](development/PYTHON_API.md)** - Signal DSL, temporal operators, AletheiaClient
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
- **[Batch Operations Tutorial](tutorials/BATCH_OPERATIONS.md)** - 6 complete examples with explanations
- **[Integration Testing](../tests/integration/INTEGRATION_TESTING.md)** - Test suite documentation

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
└── docs/
    ├── INDEX.md                       # THIS FILE - Documentation navigation
    ├── PITCH.md                       # Elevator pitch
    │
    ├── architecture/
    │   ├── DESIGN.md                  # Architecture overview
    │   └── PROTOCOL.md                # JSON protocol spec
    │
    ├── development/
    │   ├── BUILDING.md                # Build instructions
    │   └── PYTHON_API.md              # Python API reference
    │
    └── tutorials/
        └── BATCH_OPERATIONS.md        # Tutorial with examples
```

---

**Last Updated**: 2026-01-08
**Maintained By**: Aletheia Team

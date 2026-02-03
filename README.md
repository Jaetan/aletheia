# Aletheia (Ἀλήθεια)

**Formally verified CAN frame analysis with Linear Temporal Logic**

Aletheia provides mathematically proven tools for verifying automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

## Features

- **Formally Verified**: Core logic implemented in Agda with correctness proofs
- **CAN Frame Processing**: Proven correct encoding/decoding of CAN signals
- **LTL Verification**: Model checking of temporal properties over CAN traces
- **Python Interface**: Simple API for automotive engineers
- **Robust DBC Parsing**: Handles real-world DBC files with clear warnings

## Quick Start

### Prerequisites

### Installation

```bash
# Quick build (see BUILDING.md for detailed instructions)
cabal run shake -- build
```

For complete build instructions, troubleshooting, and development workflow, see [Building Guide](docs/development/BUILDING.md).

### Basic Usage

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC specification (converts .dbc to JSON)
dbc_json = dbc_to_json("vehicle.dbc")

# Define temporal properties using fluent DSL
speed_limit = Signal("Speed").less_than(220).always()
brake_check = Signal("BrakePressed").equals(1).eventually()

# Stream CAN frames and check properties
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([speed_limit.to_dict(), brake_check.to_dict()])
    client.start_stream()

    for timestamp, can_id, data in can_trace:
        response = client.send_frame(timestamp, can_id, data)
        if response.get("status") == "violation":
            print(f"Violation: {response['reason']}")

    client.end_stream()
```

See [Python API Guide](docs/development/PYTHON_API.md) for complete API reference and examples.

### Signal Operations

AletheiaClient also provides signal extraction and frame building:

```python
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)

    # Build a frame from signal values
    frame = client.build_frame(can_id=0x100, signals={"Speed": 72.0})

    # Extract signals from a frame
    result = client.extract_signals(can_id=0x100, data=frame)
    speed = result.get("Speed")  # 72.0

    # Update specific signals in a frame
    modified = client.update_frame(can_id=0x100, frame=frame, signals={"Speed": 130.0})
```

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── python/              # User-facing Python API
├── docs/                # Documentation
└── examples/            # Sample DBC files and demos
```

## Documentation

**📚 [Complete Documentation Index](docs/INDEX.md)** - Full navigation guide

### Getting Started
- [Building Guide](docs/development/BUILDING.md) - Setup and installation
- [Python API Guide](docs/development/PYTHON_API.md) - Complete DSL reference

### Architecture & Design
- [Design Overview](docs/architecture/DESIGN.md) - Three-layer architecture
- [JSON Protocol](docs/architecture/PROTOCOL.md) - Low-level protocol specification

### Contributing
- [Contributing Guide](CONTRIBUTING.md) - How to contribute
- [CLAUDE.md](CLAUDE.md) - AI-assisted development
- [Project Status](PROJECT_STATUS.md) - Current phase and roadmap

### Additional
- [Project Pitch](docs/PITCH.md) - Why Aletheia?
- [Examples](examples/) - Sample DBC files and demos

## Project Status

**Current Phase**: See [PROJECT_STATUS.md](PROJECT_STATUS.md) for current phase and detailed status

Complete information on deliverables, quality gates, and roadmap available in PROJECT_STATUS.md.

## Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) to understand what kinds of contributions belong upstream, extension points for customization, and submission guidelines.

## License

This project is licensed under the **BSD 2-Clause License**. See [LICENSE.md](LICENSE.md) for details.

### License Philosophy

This project uses the BSD 2-Clause License to allow broad use of the software—including in proprietary and commercial environments—while keeping the core simple, stable, and easy to maintain.

Rather than relying on licensing to force contributions, the project encourages collaboration through clear extension points, good documentation, and an upstream-first development process for generally useful improvements. This approach minimizes friction for adopters while still allowing the project to benefit from shared maintenance and evolution.

This license choice reflects a preference for architectural and social solutions over legal compulsion.

## Etymology

Aletheia (Ἀλήθεια) - Greek for "truth" or "disclosure". In philosophy, it represents the uncovering or revealing of truth, which aligns with our goal of formally verifying correctness.

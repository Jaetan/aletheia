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
from aletheia import StreamingClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC specification (converts .dbc to JSON)
dbc_json = dbc_to_json("vehicle.dbc")

# Define temporal properties using fluent DSL
speed_limit = Signal("Speed").less_than(220).always()
brake_check = Signal("BrakePressed").equals(1).eventually()

# Stream CAN frames and check properties
with StreamingClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([speed_limit.to_dict(), brake_check.to_dict()])
    client.start_stream()

    for timestamp, can_id, data in can_trace:
        response = client.send_frame(timestamp, can_id, data)
        if response.get("type") == "property":
            print(f"Violation: {response['message']}")

    client.end_stream()
```

See [Python API Guide](docs/development/PYTHON_API.md) for complete API reference and examples.

### Batch Signal Operations

Aletheia also provides standalone tools for building and extracting CAN signals:

```python
from aletheia import FrameBuilder, SignalExtractor
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("vehicle.dbc")

# Build a CAN frame from signals
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    frame = (builder
        .set("EngineSpeed", 2000)
        .set("EngineTemp", 90)
        .set("Throttle", 75)
        .build())

# Extract all signals from a frame
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame)
    speed = result.get("EngineSpeed")  # 2000.0
```

See [Batch Operations Tutorial](docs/tutorials/BATCH_OPERATIONS.md) for detailed usage and [examples](examples/batch_operations/).

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── python/              # User-facing Python API
├── docs/                # Documentation
└── examples/            # Sample DBC files and traces
```

## Documentation

**📚 [Complete Documentation Index](docs/INDEX.md)** - Full navigation guide

### Getting Started
- [Building Guide](docs/development/BUILDING.md) - Setup and installation
- [Python API Guide](docs/development/PYTHON_API.md) - Complete DSL reference
- [Batch Operations Tutorial](docs/tutorials/BATCH_OPERATIONS.md) - Hands-on examples

### Architecture & Design
- [Design Overview](docs/architecture/DESIGN.md) - Three-layer architecture
- [JSON Protocol](docs/architecture/PROTOCOL.md) - Low-level protocol specification

### Contributing
- [Contributing Guide](CONTRIBUTING.md) - How to contribute
- [CLAUDE.md](CLAUDE.md) - AI-assisted development
- [Project Status](PROJECT_STATUS.md) - Current phase and roadmap

### Additional
- [Project Pitch](docs/PITCH.md) - Why Aletheia?
- [Examples](examples/) - Sample DBC files and scripts
- [Integration Tests](tests/integration/INTEGRATION_TESTING.md) - Test suite

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

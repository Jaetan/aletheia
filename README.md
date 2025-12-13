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

See [Building Guide](docs/development/BUILDING.md) for detailed installation instructions.

### Installation

```bash
# Build the system
cabal run shake -- build

# Install Python package
cabal run shake -- install-python
```

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

### Batch Signal Operations

Aletheia also provides standalone tools for building and extracting CAN signals, independent from streaming verification:

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
    temp = result.get("EngineTemp")    # 90.0

    if result.has_errors():
        print(f"Extraction errors: {result.errors}")
```

**Use cases**:
- Build test frames for simulation
- Extract signals from captured CAN traces
- Modify specific signals in existing frames
- Debug signal encoding/decoding issues

See [Batch Operations Tutorial](docs/tutorials/BATCH_OPERATIONS.md) and [examples](examples/batch_operations/) for detailed usage.

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── python/              # User-facing Python API
└── examples/            # Sample DBC files and traces
```

## Documentation

### Getting Started
- [Building Guide](docs/development/BUILDING.md) - Build instructions and dependencies
- [Python API Guide](docs/development/PYTHON_API.md) - Complete Python API reference
- [Batch Operations Tutorial](docs/tutorials/BATCH_OPERATIONS.md) - Learn batch signal operations

### Architecture & Design
- [Design Document](docs/architecture/DESIGN.md) - Detailed architecture and formal verification
- [CLAUDE.md](CLAUDE.md) - Project rules, development workflow, and contributing guidelines

### Examples
- [Batch Operations Examples](examples/batch_operations/) - 6 complete examples with explanations

## Status

**Current**: Production-ready JSON streaming protocol with LTL verification

See [Design Document](docs/architecture/DESIGN.md) for detailed architecture and roadmap.

## License

TBD

## Etymology

Aletheia (Ἀλήθεια) - Greek for "truth" or "disclosure". In philosophy, it represents the uncovering or revealing of truth, which aligns with our goal of formally verifying correctness.

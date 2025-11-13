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

See [BUILDING.md](BUILDING.md) for detailed installation instructions.

### Installation

```bash
# Build the system
cabal run shake -- build

# Install Python package
cabal run shake -- install-python
```

### Basic Usage

```python
from aletheia import CANDecoder, LTL, verify

# Load DBC specification
decoder = CANDecoder.from_dbc("vehicle.dbc.yaml")

# Define temporal property
property = LTL.always(
    LTL.implies(
        decoder.signal("speed") > 0,
        LTL.eventually(decoder.signal("brake_pressed") == 1, within=5.0)
    )
)

# Verify against trace
result = verify(decoder, "recording.yaml", [property])
print(result)
```

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── python/              # User-facing Python API
└── examples/            # Sample DBC files and traces
```

## Documentation

- [BUILDING.md](BUILDING.md) - Build instructions and dependencies
- [DEVELOPMENT.md](DEVELOPMENT.md) - Architecture and development guide
- [DESIGN.md](DESIGN.md) - Detailed design document

## Status

**Current Phase**: 1 - Core Infrastructure

See [DESIGN.md](DESIGN.md) for implementation phases and roadmap.

## License

TBD

## Etymology

Aletheia (Ἀλήθεια) - Greek for "truth" or "disclosure". In philosophy, it represents the uncovering or revealing of truth, which aligns with our goal of formally verifying correctness.

# Aletheia (Ἀλήθεια)

**Formally verified CAN frame analysis with Linear Temporal Logic**

Aletheia provides mathematically proven tools for verifying automotive software by applying Linear Temporal Logic (LTL) over traces of CAN frames.

## Features

- **Formally Verified**: Core logic implemented in Agda with correctness proofs — eliminates signal extraction bugs entirely, not just for tested inputs
- **CAN Frame Processing**: Proven correct encoding/decoding guarantees roundtrip correctness for valid DBC specifications
- **LTL Verification**: Streaming model checker with O(1) memory — verified 1.08× growth across a 100× trace increase. Sustained ~109k frames/s on the C++ binary FFI path (CAN 2.0B, Ryzen 9 5950X); a 1 GB trace at ~200 bytes/frame processes in roughly 50s in that configuration. See [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics) for the full throughput table and methodology.
- **Four Interface Tiers**: Check API (engineers), YAML (CI/CD), Excel (technicians), and full LTL DSL (developers) — choose the level that fits your team
- **Python, C++, and Go Interfaces**: All run in-process via shared library (ctypes/dlopen FFI) — no subprocess, no IPC overhead
- **Robust DBC Parsing**: Handles real-world edge cases (multiplexed signals, 29-bit IDs, signed integers) with clear validation warnings

## Quick Start

### Installation

```bash
# Quick build (see BUILDING.md for detailed instructions)
cabal run shake -- build
```

For complete build instructions, troubleshooting, and development workflow, see [Building Guide](docs/development/BUILDING.md).

### Basic Usage

> **Which style should I use?** New users should start with the **Check API** or YAML/Excel loaders shown under [Higher-Level Interfaces](#higher-level-interfaces) below — they cover the common cases. The raw DSL (`Signal`, `set_properties`) shown here is the escape hatch for full LTL control (e.g., metric operators, custom predicates). See the [Interface Guide](docs/reference/INTERFACES.md) for an end-to-end comparison.

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json
from aletheia.can_log import iter_can_log  # installed via `pip install aletheia[can]`

# Load DBC specification (converts .dbc to JSON)
dbc_json = dbc_to_json("vehicle.dbc")

# Define temporal properties using fluent DSL (raw LTL)
speed_limit = Signal("Speed").less_than(220).always()
brake_check = Signal("BrakePressed").equals(1).eventually()

# Stream CAN frames from a .blf / .asc / .log / .mf4 trace and check properties
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([speed_limit.to_dict(), brake_check.to_dict()])
    client.start_stream()

    for timestamp, can_id, dlc, data in iter_can_log("drive.blf"):
        response = client.send_frame(timestamp, can_id, dlc, data)
        if response.get("status") == "fails":
            ts = response['timestamp']['numerator']
            print(f"Violation at {ts}us")

    client.end_stream()
```

See [Python API Guide](docs/reference/PYTHON_API.md) for the complete DSL reference.

### Higher-Level Interfaces

For users who don't need full LTL control, Aletheia provides three
higher-level interfaces that compile to the same verified core (recommended
entry point for new users):

```python
from aletheia import Check, load_checks, load_checks_from_excel

# Check API — industry vocabulary
Check.signal("Speed").never_exceeds(220)
Check.when("BrakePedal").exceeds(50).then("BrakeLight").equals(1).within(100)

# YAML — declarative config files
checks = load_checks("checks.yaml")

# Excel — spreadsheet templates for technicians
checks = load_checks_from_excel("checks.xlsx")
```

See [Interface Guide](docs/reference/INTERFACES.md) for end-to-end workflows.

### Signal Operations

AletheiaClient also provides signal extraction and frame building:

```python
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)

    # Build a frame from signal values
    frame = client.build_frame(can_id=0x100, dlc=8, signals={"Speed": 72.0})

    # Extract signals from a frame
    result = client.extract_signals(can_id=0x100, dlc=8, data=frame)
    speed = result.get("Speed", default=0.0)  # 72.0

    # Update specific signals in a frame
    modified = client.update_frame(can_id=0x100, dlc=8, frame=frame, signals={"Speed": 130.0})
```

## Project Structure

```
aletheia/
├── src/Aletheia/        # Agda core (formal verification)
├── haskell-shim/        # Minimal I/O layer
├── include/             # C header (aletheia.h)
├── python/              # Python API
├── cpp/                 # C++23 binding
├── go/                  # Go binding
├── benchmarks/          # Cross-language benchmarks
├── docs/                # Documentation
└── examples/            # Sample DBC files and demos
```

## Documentation

**📚 [Complete Documentation Index](docs/INDEX.md)** - Full navigation guide

### Getting Started
- [Quick Start](docs/guides/QUICKSTART.md) - 5-minute tutorial
- [Building Guide](docs/development/BUILDING.md) - Setup and installation

### Guides
- [Tutorials](docs/guides/TUTORIAL.md) - End-to-end walkthroughs (Technician, Test Engineer, Scripter, Developer)
- [Cookbook](docs/guides/COOKBOOK.md) - Problem-driven recipes

### Reference
- [Interface Guide](docs/reference/INTERFACES.md) - Check API, YAML, Excel loaders
- [Python API Guide](docs/reference/PYTHON_API.md) - Raw DSL and AletheiaClient reference
- [CLI Reference](docs/reference/CLI.md) - `python3 -m aletheia` subcommands

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

BSD 2-Clause was chosen to allow broad adoption (including proprietary use) while encouraging collaboration through architecture and process rather than legal compulsion.

## Etymology

Aletheia (Ἀλήθεια) - Greek for "truth" or "disclosure". In philosophy, it represents the uncovering or revealing of truth, which aligns with our goal of formally verifying correctness.

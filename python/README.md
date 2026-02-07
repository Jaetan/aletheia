# Aletheia Python Package

Python interface for the Aletheia formally verified CAN frame analyzer.

## Installation

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) for detailed build instructions.

Quick start:
```bash
cabal run shake -- build           # Build Agda + Haskell components
cabal run shake -- install-python  # Install Python package
```

## Usage

The Aletheia Python API provides a unified client with streaming LTL verification and signal operations. See the main README and package docstrings for complete examples.

```python
from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

# Load DBC specification
dbc_json = dbc_to_json("vehicle.dbc")

# Define properties using fluent DSL
speed_limit = Signal("Speed").less_than(220).always()

# Stream CAN frames and check properties
with AletheiaClient() as client:
    client.parse_dbc(dbc_json)
    client.set_properties([speed_limit.to_dict()])
    client.start_stream()

    for timestamp, can_id, data in can_trace:
        response = client.send_frame(timestamp, can_id, data)
        if response.get("status") == "violation":
            print(f"Violation: {response['reason']}")

    client.end_stream()
```

For more details, see:
- [Interface Guide](../docs/development/INTERFACES.md) - Check API, YAML, Excel loaders
- [Python API Guide](../docs/development/PYTHON_API.md) - Raw DSL and AletheiaClient reference
- Tests: `python/tests/`

## Testing

```bash
cd python
python -m pytest tests/ -v
```

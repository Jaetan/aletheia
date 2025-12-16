# Aletheia Examples

This directory contains example DBC files and verification scripts demonstrating Aletheia's JSON streaming protocol with LTL verification.

## Files

- `example.dbc` - Sample DBC file with engine and brake signals (standard Vector DBC format)
- `simple_verification.py` - Complete verification example using StreamingClient API

## Running Examples

See [../docs/development/BUILDING.md](../docs/development/BUILDING.md) for build instructions.

```bash
# From repository root, ensure everything is built and venv is active
source venv/bin/activate

# Install package in development mode
cd python && pip install -e ".[dev]" && cd ..

# Run simple example
cd examples
python3 simple_verification.py
```

## Example DBC Structure

The `example.dbc` file defines two CAN messages:

**Message 0x100 (EngineStatus)**:
- `EngineSpeed` (16-bit): 0-8000 rpm, scale 0.25, offset 0
- `EngineTemp` (8-bit): -40 to 215 °C, scale 1.0, offset -40

**Message 0x200 (BrakeStatus)**:
- `BrakePressure` (16-bit): 0-6553.5 bar, scale 0.1, offset 0
- `BrakePressed` (1-bit): 0 or 1, scale 1.0, offset 0

## LTL Properties Example

The example script demonstrates three temporal properties:

1. **Range constraint**: `Signal("EngineSpeed").between(0, 8000).always()`
2. **Temperature bounds**: `Signal("EngineTemp").between(-40, 215).always()`
3. **Safety limit**: `Signal("BrakePressure").less_than(6553.5).always()`

## Python DSL Usage

Aletheia provides a fluent Signal interface for building LTL properties:

```python
from aletheia import Signal

# Basic predicates
Signal("Speed").equals(0)
Signal("Speed").less_than(220)
Signal("Speed").between(0, 300)
Signal("Speed").changed_by(10)

# Temporal operators
Signal("Speed").equals(0).always()      # □(Speed = 0)
Signal("Speed").equals(0).eventually()  # ◇(Speed = 0)
Signal("Speed").equals(0).never()       # □¬(Speed = 0)

# Bounded temporal operators
Signal("DoorClosed").equals(1).within(100)  # Within 100ms

# Composition
brake = Signal("BrakePressed").equals(1)
stopped = Signal("Speed").equals(0)
brake.implies(stopped.within(500))  # Brake → Stop within 500ms
```

See `python/aletheia/dsl.py` for complete DSL documentation.

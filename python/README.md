# Aletheia Python Package

Python interface for the Aletheia formally verified CAN frame analyzer.

## Installation

```bash
# From repository root
shake build          # Build Agda + Haskell components
shake install-python # Install Python package
```

## Usage

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

## Testing

```bash
cd python
python -m pytest tests/ -v
```

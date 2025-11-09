# Aletheia Examples

This directory contains example DBC files, CAN traces, and verification scripts.

## Files

- `sample.dbc.yaml` - Sample DBC with engine and brake signals
- `sample_trace.yaml` - Sample CAN trace (4 frames over 150ms)
- `simple_verification.py` - Basic verification example

## Running Examples

```bash
# From repository root, ensure everything is built
shake build

# Run simple example
cd examples
python3 simple_verification.py
```

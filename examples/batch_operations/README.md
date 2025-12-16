# Batch Operations Examples

This directory contains 6 complete examples demonstrating batch signal operations in Aletheia.

## Prerequisites

See [../../docs/development/BUILDING.md](../../docs/development/BUILDING.md) for build instructions.

```bash
# From repository root
cd /path/to/aletheia
source venv/bin/activate  # Activate Python environment

# Ensure you have a DBC file (examples use ../example.dbc)
ls ../example.dbc
```

## Examples

### 1. Simple Frame Builder (`simple_frame_builder.py`)

**What it demonstrates**:
- Loading DBC files
- Building CAN frames with multiple signals
- Fluent builder interface
- Verifying frames by extraction
- Building multiple frames efficiently

**Run it**:
```bash
python3 simple_frame_builder.py
```

**Key concepts**: Immutable builder pattern, context managers, subprocess reuse

---

### 2. Signal Extractor (`signal_extractor.py`)

**What it demonstrates**:
- Extracting all signals from frames
- Rich result objects (values/errors/absent)
- Safe value access with defaults
- Processing multiple frames
- Error handling patterns

**Run it**:
```bash
python3 signal_extractor.py
```

**Key concepts**: Result partitioning, default values, batch extraction

---

### 3. Frame Updater (`frame_updater.py`)

**What it demonstrates**:
- Updating individual signals in frames
- Updating multiple signals at once
- Immutability (original frame unchanged)
- Processing frame sequences
- Trace file modification

**Run it**:
```bash
python3 frame_updater.py
```

**Key concepts**: Immutable updates, preserving unchanged signals, trace modification

---

### 4. Multiplexed Signals (`multiplexed_signals.py`)

**What it demonstrates**:
- Understanding multiplexing concepts
- Building frames with multiplexed signals
- Extracting multiplexed signals
- Handling absent signals (normal, not an error)
- Switching between multiplexor modes

**Run it**:
```bash
python3 multiplexed_signals.py
```

**Key concepts**: Multiplexing, absent vs error signals, multiplexor values

**Note**: If your DBC doesn't have multiplexed signals, this example demonstrates the concepts with synthetic data.

---

### 5. Frame Debugging (`frame153_debugging.py`)

**What it demonstrates**:
- Debugging signal encoding/decoding issues
- Testing with known values
- Boundary condition testing
- Byte-by-byte frame comparison
- Identifying DBC definition problems

**Run it**:
```bash
python3 frame153_debugging.py
```

**Key concepts**: Round-trip verification, boundary testing, debugging checklist

**Use this when**: You suspect DBC definitions don't match actual CAN protocol

---

### 6. Batch Trace Processing (`batch_trace_processing.py`)

**What it demonstrates**:
- Reading/writing trace files
- Extracting signals from all frames
- Filtering frames by criteria
- Modifying signals in traces
- Statistical analysis
- Anomaly detection

**Run it**:
```bash
python3 batch_trace_processing.py
```

**Key concepts**: Complete workflows, trace analysis, offline processing

**Use this for**: Real-world trace processing patterns

---

## Learning Path

**Beginners**: Start with examples 1-3
1. `simple_frame_builder.py` - Learn frame building basics
2. `signal_extractor.py` - Learn signal extraction basics
3. `frame_updater.py` - Learn frame modification

**Intermediate**: Continue with examples 4-5
4. `multiplexed_signals.py` - Handle multiplexed signals
5. `frame153_debugging.py` - Debug encoding issues

**Advanced**: Complete with example 6
6. `batch_trace_processing.py` - Full trace workflows

## Common Patterns

All examples demonstrate these core patterns:

1. **Context Managers**: Always use `with` statement for automatic cleanup
   ```python
   with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
       frame = builder.set("Signal", value).build()
   ```

2. **Subprocess Reuse**: One subprocess handles multiple operations
   ```python
   with SignalExtractor(dbc=dbc) as extractor:
       for frame in frames:  # Subprocess reused
           result = extractor.extract(can_id, frame)
   ```

3. **Immutability**: Operations return new data, originals unchanged
   ```python
   updated = extractor.update(can_id, frame, signals)
   # `frame` is unchanged, `updated` is new
   ```

4. **Safe Value Access**: Use defaults to avoid KeyError
   ```python
   speed = result.get("EngineSpeed", default=0.0)
   ```

5. **Error Handling**: Check result.errors and result.absent
   ```python
   if result.has_errors():
       print(f"Errors: {result.errors}")
   if result.absent:
       print(f"Absent: {result.absent}")  # Normal for multiplexing
   ```

## Troubleshooting

### Binary Not Found

```
FileNotFoundError: Aletheia binary not found at /path/to/build/aletheia
```

**Solution**: Build the binary first (see [build instructions](../../docs/development/BUILDING.md))
```bash
cd /path/to/aletheia
cabal run shake -- build
```

### DBC File Not Found

```
FileNotFoundError: DBC file not found: /path/to/example.dbc
```

**Solution**: Ensure example.dbc exists or modify the script to use your DBC file
```python
dbc_path = Path("/path/to/your.dbc")
```

### Import Errors

```
ModuleNotFoundError: No module named 'aletheia'
```

**Solution**: Activate the Python virtual environment (see [venv setup guide](../../docs/development/BUILDING.md#2-set-up-python-virtual-environment))
```bash
source venv/bin/activate
```

### Signal Not Found

```
RuntimeError: Command failed: Signal 'SignalName' not found
```

**Solution**: Check that the signal exists in your DBC file and matches the message CAN ID

## Further Reading

- **Tutorial**: `docs/tutorials/BATCH_OPERATIONS.md` - Complete tutorial with 10+ examples
- **API Reference**: `docs/development/PYTHON_API.md` - Full Python API documentation
- **Architecture**: `docs/architecture/DESIGN.md` - System design and verification
- **Building**: `docs/development/BUILDING.md` - Build system documentation

## Questions?

See the main project README.md or the documentation in `docs/` for more information.

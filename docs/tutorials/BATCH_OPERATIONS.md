# Batch Signal Operations Tutorial

**Version**: Phase 2B.1
**Last Updated**: 2025-12-09

---

## Table of Contents

1. [Introduction](#introduction)
2. [Quick Start (5 Minutes)](#quick-start-5-minutes)
3. [Core Concepts](#core-concepts)
4. [Building CAN Frames](#building-can-frames)
5. [Extracting Signals](#extracting-signals)
6. [Updating Frames](#updating-frames)
7. [Handling Multiplexed Signals](#handling-multiplexed-signals)
8. [Error Handling](#error-handling)
9. [Performance Tips](#performance-tips)
10. [Common Patterns](#common-patterns)

---

## Introduction

### What Are Batch Operations?

Batch signal operations provide a high-level toolbox for building, extracting, and updating CAN frames with multiple signals at once. They are independent from streaming verification and designed for:

- **Frame construction**: Build CAN frames from signal name-value pairs
- **Signal extraction**: Extract all signals from a frame with rich error reporting
- **Frame updates**: Modify specific signals in existing frames

### When to Use Batch Operations

**Use batch operations when you need to**:
- Build CAN frames for testing or simulation
- Extract multiple signals from captured frames
- Update signals in trace files
- Debug signal encoding issues
- Process trace files offline

**Don't use batch operations for**:
- Real-time streaming verification (use `StreamingClient` instead)
- LTL property checking (use `StreamingClient` with properties)

### Key Features

- **Immutable builder pattern**: Clear, readable frame construction
- **Rich error reporting**: Explicit partitioning of values/errors/absent signals
- **Batch-only API**: Single signals are 1-element batches (consistent interface)
- **Context manager support**: Automatic subprocess cleanup
- **Agda validation**: Overlap detection, bounds checking, multiplexing handled correctly

---

## Quick Start (5 Minutes)

### Prerequisites

```bash
# Build the Aletheia binary
cd /path/to/aletheia
cabal run shake -- build

# Activate Python environment
source venv/bin/activate

# Install dependencies if needed
pip install cantools
```

### Example 1: Build a Simple Frame

```python
from aletheia import FrameBuilder
from aletheia.dbc_converter import dbc_to_json

# Load DBC file
dbc = dbc_to_json("examples/example.dbc")

# Build a frame with multiple signals
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    frame = (builder
        .set("EngineSpeed", 2000)
        .set("EngineTemp", 90)
        .build())

    print(f"Frame bytes: {frame}")
    # Output: [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]
```

**What's happening**:
- `FrameBuilder` starts a subprocess with DBC pre-loaded
- `set()` adds signals (returns new builder - immutable pattern)
- `build()` encodes all signals into an 8-byte CAN frame
- Context manager (`with`) ensures subprocess cleanup

### Example 2: Extract Signals from a Frame

```python
from aletheia import SignalExtractor
from aletheia.dbc_converter import dbc_to_json

# Load DBC file
dbc = dbc_to_json("examples/example.dbc")

# Extract signals from a frame
frame_data = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    # Access successfully extracted values
    print(f"EngineSpeed: {result.get('EngineSpeed')}")  # 2000.0
    print(f"EngineTemp: {result.get('EngineTemp')}")    # 90.0

    # Check for errors
    if result.has_errors():
        print(f"Errors: {result.errors}")

    # Check for absent multiplexed signals
    print(f"Absent signals: {result.absent}")
```

**What's happening**:
- `SignalExtractor` starts a subprocess with DBC pre-loaded
- `extract()` decodes all signals in the frame
- `result.values` contains successfully extracted signals
- `result.errors` contains signals that failed extraction (with reasons)
- `result.absent` lists multiplexed signals not present in this frame

### Example 3: Update Signals in a Frame

```python
from aletheia import SignalExtractor
from aletheia.dbc_converter import dbc_to_json

# Load DBC file
dbc = dbc_to_json("examples/example.dbc")

# Original frame
original_frame = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

with SignalExtractor(dbc=dbc) as extractor:
    # Update specific signals, leave others unchanged
    updated_frame = extractor.update(
        can_id=0x100,
        frame=original_frame,
        signals={
            "EngineSpeed": 2500,  # Update to 2500 RPM
            "EngineTemp": 95      # Update to 95°C
        }
    )

    print(f"Original: {original_frame}")
    print(f"Updated:  {updated_frame}")

    # Verify the update
    result = extractor.extract(can_id=0x100, data=updated_frame)
    print(f"New EngineSpeed: {result.get('EngineSpeed')}")  # 2500.0
    print(f"New EngineTemp: {result.get('EngineTemp')}")    # 95.0
```

**What's happening**:
- `update()` modifies specific signals in an existing frame
- Original frame is unchanged (immutable operation)
- Other signals in the frame remain untouched
- Agda validates that signal updates don't overlap

---

## Core Concepts

### Immutable Builder Pattern

`FrameBuilder` uses an immutable builder pattern for clarity and safety:

```python
# Each set() returns a NEW builder
builder1 = FrameBuilder(can_id=0x100, dbc=dbc)
builder2 = builder1.set("EngineSpeed", 2000)
builder3 = builder2.set("EngineTemp", 90)

# builder1 is unchanged - still has no signals
# builder2 has EngineSpeed only
# builder3 has both signals

# Fluent interface makes this readable:
frame = (FrameBuilder(can_id=0x100, dbc=dbc)
    .set("EngineSpeed", 2000)
    .set("EngineTemp", 90)
    .build())
```

**Why immutable?**
- Clear data flow - no hidden state mutations
- Safe to share builders across code
- Easy to reason about - no action at a distance
- Functional programming style

**Important**: All builders share the same subprocess for efficiency. Only close the original builder.

### Rich Result Objects

`SignalExtractionResult` partitions extraction results into three categories:

```python
result = extractor.extract(can_id=0x100, data=frame_data)

# Successfully extracted signals
result.values: Dict[str, float]
# Example: {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

# Extraction errors (signal exists but couldn't decode)
result.errors: Dict[str, str]
# Example: {"BrokenSignal": "Value out of bounds: got 500, max 255"}

# Multiplexed signals not present in this frame
result.absent: List[str]
# Example: ["Gear", "Clutch"]  # These need multiplexor value match
```

**Why three categories?**
- `values`: Signals decoded successfully - safe to use
- `errors`: Something wrong with frame data or DBC definition - investigate
- `absent`: Normal for multiplexed signals - not an error

### Subprocess Management

Both `FrameBuilder` and `SignalExtractor` manage subprocesses for efficiency:

```python
# Option 1: Context manager (recommended)
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    # Use builder here
    pass
# Subprocess automatically cleaned up

# Option 2: Manual cleanup
builder = FrameBuilder(can_id=0x100, dbc=dbc)
try:
    # Use builder here
    pass
finally:
    builder.close()  # Ensure cleanup
```

**Why subprocess?**
- DBC is parsed once, then reused for all operations
- Much faster than parsing DBC for each operation
- Context manager ensures proper cleanup

### Signal Overlap Detection

Agda validates that signals don't overlap in the frame:

```python
# This will fail if EngineSpeed and EngineTemp overlap in the DBC
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    try:
        frame = (builder
            .set("EngineSpeed", 2000)
            .set("EngineTemp", 90)
            .build())
    except RuntimeError as e:
        print(f"Overlap detected: {e}")
        # "Signal overlap detected: EngineSpeed overlaps with EngineTemp"
```

**What Agda checks**:
- Start bit + length doesn't exceed 64 bits
- Signals don't overlap in bit positions
- All signals fit within 8-byte frame
- Values are within min/max bounds

---

## Building CAN Frames

### Basic Frame Building

```python
from aletheia import FrameBuilder
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("examples/example.dbc")

with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    # Build frame with 2 signals
    frame = (builder
        .set("EngineSpeed", 2000)
        .set("EngineTemp", 90)
        .build())

    print(f"Frame: {[f'0x{b:02X}' for b in frame]}")
```

### Building Multiple Frames

```python
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    # Build multiple frames efficiently (subprocess reused)
    frames = []

    for speed in range(1000, 3000, 100):
        frame = builder.set("EngineSpeed", speed).build()
        frames.append(frame)

    print(f"Built {len(frames)} frames")
```

### Building Frames with Different IDs

```python
# Need different FrameBuilder for each CAN ID
dbc = dbc_to_json("examples/example.dbc")

# Frame 1: Engine data (CAN ID 0x100)
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    engine_frame = (builder
        .set("EngineSpeed", 2000)
        .set("EngineTemp", 90)
        .build())

# Frame 2: Brake data (CAN ID 0x200)
with FrameBuilder(can_id=0x200, dbc=dbc) as builder:
    brake_frame = (builder
        .set("BrakePressure", 50)
        .set("ABSActive", 1)
        .build())
```

### Handling Build Errors

```python
with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
    try:
        frame = (builder
            .set("EngineSpeed", 999999)  # Value too large
            .build())
    except RuntimeError as e:
        if "out of bounds" in str(e):
            print("Signal value exceeds DBC limits")
        elif "not found" in str(e):
            print("Signal doesn't exist in this message")
        elif "overlap" in str(e):
            print("Signals overlap in frame")
        else:
            raise
```

---

## Extracting Signals

### Basic Signal Extraction

```python
from aletheia import SignalExtractor
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("examples/example.dbc")
frame_data = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    # Access all successfully extracted signals
    for name, value in result.values.items():
        print(f"{name}: {value}")
```

### Using Default Values

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    # Get with default if signal not in values
    speed = result.get("EngineSpeed", default=0.0)
    temp = result.get("EngineTemp", default=20.0)

    # Safe even if signal had extraction error
    unknown = result.get("NonExistentSignal", default=-1.0)  # Returns -1.0
```

### Checking Extraction Status

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    print(f"Extracted {len(result.values)} signals successfully")
    print(f"Found {len(result.errors)} extraction errors")
    print(f"Found {len(result.absent)} absent multiplexed signals")

    # Check for any errors
    if result.has_errors():
        print("Warning: Some signals failed extraction")
        for signal_name, error_msg in result.errors.items():
            print(f"  {signal_name}: {error_msg}")
```

### Processing Multiple Frames

```python
trace_frames = [
    (0x100, [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]),
    (0x100, [0x00, 0x09, 0xC4, 0x64, 0x00, 0x00, 0x00, 0x00]),
    (0x100, [0x00, 0x0B, 0xB8, 0x6E, 0x00, 0x00, 0x00, 0x00]),
]

with SignalExtractor(dbc=dbc) as extractor:
    speeds = []

    for can_id, frame_data in trace_frames:
        result = extractor.extract(can_id=can_id, data=frame_data)
        speed = result.get("EngineSpeed", default=0.0)
        speeds.append(speed)

    print(f"Speed range: {min(speeds)} - {max(speeds)}")
```

---

## Updating Frames

### Basic Frame Update

```python
from aletheia import SignalExtractor
from aletheia.dbc_converter import dbc_to_json

dbc = dbc_to_json("examples/example.dbc")
original_frame = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

with SignalExtractor(dbc=dbc) as extractor:
    # Update one signal, leave others unchanged
    updated = extractor.update(
        can_id=0x100,
        frame=original_frame,
        signals={"EngineSpeed": 2500}
    )

    # Verify update
    result = extractor.extract(can_id=0x100, data=updated)
    print(f"New speed: {result.get('EngineSpeed')}")  # 2500.0
    print(f"Temp unchanged: {result.get('EngineTemp')}")  # Still 90.0
```

### Updating Multiple Signals

```python
with SignalExtractor(dbc=dbc) as extractor:
    updated = extractor.update(
        can_id=0x100,
        frame=original_frame,
        signals={
            "EngineSpeed": 2500,
            "EngineTemp": 95,
            "Throttle": 75
        }
    )
```

### Processing Trace Files

```python
def update_trace_file(input_path, output_path, can_id, signal_updates):
    """Update specific signals in all frames with given CAN ID"""
    dbc = dbc_to_json("examples/example.dbc")

    with SignalExtractor(dbc=dbc) as extractor:
        with open(input_path, 'r') as infile, open(output_path, 'w') as outfile:
            for line in infile:
                # Parse line (format: CAN_ID DATA0 DATA1 ... DATA7)
                parts = line.strip().split()
                frame_id = int(parts[0], 16)
                frame_data = [int(b, 16) for b in parts[1:9]]

                # Update if this is the target frame
                if frame_id == can_id:
                    frame_data = extractor.update(
                        can_id=frame_id,
                        frame=frame_data,
                        signals=signal_updates
                    )

                # Write updated frame
                outfile.write(f"{frame_id:03X} ")
                outfile.write(" ".join(f"{b:02X}" for b in frame_data))
                outfile.write("\n")

# Usage
update_trace_file(
    "trace_original.txt",
    "trace_modified.txt",
    can_id=0x100,
    signal_updates={"EngineSpeed": 2500}
)
```

---

## Handling Multiplexed Signals

### Understanding Multiplexing

Multiplexed signals share the same frame bits but are selected by a multiplexor signal value:

```
Message 0x153:
  Multiplexor signal: Mode (bits 0-7)

  When Mode == 0x01:
    - Signal A (bits 8-15)
    - Signal B (bits 16-23)

  When Mode == 0x02:
    - Signal C (bits 8-15)
    - Signal D (bits 16-23)
```

### Extracting Multiplexed Signals

```python
dbc = dbc_to_json("examples/multiplexed.dbc")

with SignalExtractor(dbc=dbc) as extractor:
    # Frame with Mode=0x01
    frame_mode1 = [0x01, 0xAA, 0xBB, 0x00, 0x00, 0x00, 0x00, 0x00]
    result1 = extractor.extract(can_id=0x153, data=frame_mode1)

    # Present signals
    print(f"Signal A: {result1.get('SignalA')}")  # Extracted
    print(f"Signal B: {result1.get('SignalB')}")  # Extracted

    # Absent signals (wrong multiplexor value)
    print(f"Absent: {result1.absent}")  # ['SignalC', 'SignalD']

    # Frame with Mode=0x02
    frame_mode2 = [0x02, 0xCC, 0xDD, 0x00, 0x00, 0x00, 0x00, 0x00]
    result2 = extractor.extract(can_id=0x153, data=frame_mode2)

    # Now SignalC and SignalD are present
    print(f"Signal C: {result2.get('SignalC')}")  # Extracted
    print(f"Signal D: {result2.get('SignalD')}")  # Extracted
    print(f"Absent: {result2.absent}")  # ['SignalA', 'SignalB']
```

### Building Multiplexed Frames

```python
with FrameBuilder(can_id=0x153, dbc=dbc) as builder:
    # Build frame with Mode=0x01 signals
    frame_mode1 = (builder
        .set("Mode", 1)      # Set multiplexor
        .set("SignalA", 10)  # Only set signals for Mode=0x01
        .set("SignalB", 20)
        .build())

    # Build frame with Mode=0x02 signals
    frame_mode2 = (builder
        .set("Mode", 2)      # Set multiplexor
        .set("SignalC", 30)  # Only set signals for Mode=0x02
        .set("SignalD", 40)
        .build())
```

### Filtering Out Absent Signals

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x153, data=frame_data)

    # Only process signals that are actually present
    present_signals = {
        name: value
        for name, value in result.values.items()
        if name not in result.absent
    }

    print(f"Present signals: {present_signals}")
```

---

## Error Handling

### Understanding Error Categories

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    # Category 1: Successfully extracted (in result.values)
    # - Signal decoded without issues
    # - Value is within min/max bounds
    # - Multiplexor value matches (if multiplexed)

    # Category 2: Extraction errors (in result.errors)
    # - Value out of bounds
    # - Decoding failed
    # - Scaling/offset computation error

    # Category 3: Absent signals (in result.absent)
    # - Multiplexed signal with non-matching multiplexor value
    # - NOT an error - this is normal for multiplexing
```

### Handling Specific Error Types

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    for signal_name, error_msg in result.errors.items():
        if "out of bounds" in error_msg:
            # Value exceeds DBC min/max limits
            print(f"{signal_name}: Frame data has invalid value")
            # Possible causes:
            # - Corrupted frame data
            # - Incorrect DBC definition
            # - Different DBC version

        elif "decoding failed" in error_msg:
            # Couldn't decode raw value
            print(f"{signal_name}: Decoding error")
            # Possible causes:
            # - Bit manipulation error
            # - Endianness mismatch

        else:
            # Unknown error
            print(f"{signal_name}: {error_msg}")
```

### Validating Frame Data

```python
def validate_frame(extractor, can_id, frame_data):
    """Validate that all expected signals extract successfully"""
    result = extractor.extract(can_id=can_id, data=frame_data)

    if result.has_errors():
        print(f"Validation failed for CAN ID 0x{can_id:X}")
        print(f"Errors:")
        for signal, error in result.errors.items():
            print(f"  - {signal}: {error}")
        return False

    # Check if we got expected signals (excluding multiplexed absent ones)
    expected_signals = ["EngineSpeed", "EngineTemp", "Throttle"]
    missing = [
        sig for sig in expected_signals
        if sig not in result.values and sig not in result.absent
    ]

    if missing:
        print(f"Missing signals: {missing}")
        return False

    print("Frame validation passed")
    return True

# Usage
with SignalExtractor(dbc=dbc) as extractor:
    is_valid = validate_frame(extractor, 0x100, frame_data)
```

### Recovering from Errors

```python
with SignalExtractor(dbc=dbc) as extractor:
    result = extractor.extract(can_id=0x100, data=frame_data)

    # Use defaults for failed extractions
    speed = result.get("EngineSpeed", default=0.0)
    temp = result.get("EngineTemp", default=20.0)

    # Log errors but continue processing
    if result.has_errors():
        for signal, error in result.errors.items():
            print(f"Warning: {signal} extraction failed: {error}")

    # Process successfully extracted signals
    for signal, value in result.values.items():
        process_signal(signal, value)
```

---

## Performance Tips

### Subprocess Reuse

**DO** reuse the same `FrameBuilder` or `SignalExtractor` for multiple operations:

```python
# GOOD: Single subprocess handles 1000 frames
with SignalExtractor(dbc=dbc) as extractor:
    for frame_data in frames:  # 1000 frames
        result = extractor.extract(can_id=0x100, data=frame_data)
        process(result)
# ~1ms per frame (subprocess reused)

# BAD: Creates 1000 subprocesses
for frame_data in frames:
    with SignalExtractor(dbc=dbc) as extractor:  # New subprocess each time!
        result = extractor.extract(can_id=0x100, data=frame_data)
        process(result)
# ~100ms per frame (subprocess overhead)
```

### Builder Sharing

All builders created from `set()` share the same subprocess:

```python
with FrameBuilder(can_id=0x100, dbc=dbc) as base_builder:
    # These all share the subprocess
    builder1 = base_builder.set("EngineSpeed", 2000)
    builder2 = builder1.set("EngineTemp", 90)
    builder3 = builder2.set("Throttle", 75)

    # Build multiple frames efficiently
    frames = [
        builder1.build(),
        builder2.build(),
        builder3.build()
    ]
# Only close base_builder (subprocess cleanup)
```

### Batch vs Single Operations

The API is batch-only by design. Single-signal operations use 1-element lists internally:

```python
# "Single" signal extraction (actually a 1-element batch)
result = extractor.extract(can_id=0x100, data=frame_data)
speed = result.get("EngineSpeed")

# Same performance as extracting multiple signals
# All signals in the frame are decoded at once
```

### Memory Efficiency

Frame data is immutable - operations create new frames:

```python
original = [0x00, 0x07, 0xD0, 0x5A, 0x00, 0x00, 0x00, 0x00]

# update() creates NEW frame, original unchanged
updated = extractor.update(can_id=0x100, frame=original, signals={"EngineSpeed": 2500})

# If processing large traces, don't keep all frames in memory
for frame in read_trace_streaming():  # Generator
    result = extractor.extract(can_id=frame.id, data=frame.data)
    process(result)
    # frame can be garbage collected after processing
```

---

## Common Patterns

### Pattern 1: Frame Builder Pipeline

```python
def build_engine_frame(speed, temp, throttle, dbc):
    """Build engine frame with validation"""
    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        return (builder
            .set("EngineSpeed", max(0, min(speed, 8000)))    # Clamp 0-8000
            .set("EngineTemp", max(-40, min(temp, 200)))     # Clamp -40-200
            .set("Throttle", max(0, min(throttle, 100)))     # Clamp 0-100
            .build())

# Usage
frame = build_engine_frame(speed=2000, temp=90, throttle=75, dbc=dbc)
```

### Pattern 2: Extract and Validate

```python
def extract_and_validate(extractor, can_id, frame_data, required_signals):
    """Extract signals and ensure all required signals are present"""
    result = extractor.extract(can_id=can_id, data=frame_data)

    # Check for errors
    if result.has_errors():
        raise ValueError(f"Extraction errors: {result.errors}")

    # Check for missing required signals
    missing = [sig for sig in required_signals if sig not in result.values]
    if missing:
        raise ValueError(f"Missing required signals: {missing}")

    return result

# Usage
with SignalExtractor(dbc=dbc) as extractor:
    result = extract_and_validate(
        extractor,
        can_id=0x100,
        frame_data=frame_data,
        required_signals=["EngineSpeed", "EngineTemp"]
    )
```

### Pattern 3: Frame Comparison

```python
def compare_frames(extractor, can_id, frame1, frame2, tolerance=0.01):
    """Compare signals in two frames within tolerance"""
    result1 = extractor.extract(can_id=can_id, data=frame1)
    result2 = extractor.extract(can_id=can_id, data=frame2)

    differences = {}
    all_signals = set(result1.values.keys()) | set(result2.values.keys())

    for signal in all_signals:
        val1 = result1.get(signal, 0.0)
        val2 = result2.get(signal, 0.0)

        if abs(val1 - val2) > tolerance:
            differences[signal] = (val1, val2)

    return differences

# Usage
with SignalExtractor(dbc=dbc) as extractor:
    diffs = compare_frames(extractor, 0x100, original_frame, modified_frame)
    if diffs:
        print("Signal differences:")
        for sig, (v1, v2) in diffs.items():
            print(f"  {sig}: {v1} → {v2}")
```

### Pattern 4: Trace File Processing

```python
def process_trace(trace_path, dbc_path, frame_filter=None):
    """Process trace file and extract all signals"""
    dbc = dbc_to_json(dbc_path)
    results = []

    with SignalExtractor(dbc=dbc) as extractor:
        with open(trace_path, 'r') as f:
            for line_num, line in enumerate(f, 1):
                try:
                    # Parse line (format: TIMESTAMP CAN_ID DATA0 DATA1 ... DATA7)
                    parts = line.strip().split()
                    timestamp = float(parts[0])
                    can_id = int(parts[1], 16)
                    frame_data = [int(b, 16) for b in parts[2:10]]

                    # Apply filter if provided
                    if frame_filter and not frame_filter(can_id):
                        continue

                    # Extract signals
                    result = extractor.extract(can_id=can_id, data=frame_data)

                    results.append({
                        "line": line_num,
                        "timestamp": timestamp,
                        "can_id": can_id,
                        "signals": result.values,
                        "errors": result.errors
                    })

                except Exception as e:
                    print(f"Error processing line {line_num}: {e}")

    return results

# Usage
results = process_trace(
    "trace.log",
    "example.dbc",
    frame_filter=lambda can_id: can_id == 0x100  # Only process 0x100
)

# Analyze results
for r in results:
    if r["errors"]:
        print(f"Line {r['line']}: Errors {r['errors']}")
```

### Pattern 5: Signal Monitoring

```python
def monitor_signal_range(extractor, frames, signal_name):
    """Monitor signal across multiple frames"""
    values = []
    errors = 0

    for can_id, frame_data in frames:
        result = extractor.extract(can_id=can_id, data=frame_data)

        if signal_name in result.values:
            values.append(result.values[signal_name])
        elif signal_name in result.errors:
            errors += 1

    if not values:
        return None

    return {
        "min": min(values),
        "max": max(values),
        "avg": sum(values) / len(values),
        "count": len(values),
        "errors": errors
    }

# Usage
with SignalExtractor(dbc=dbc) as extractor:
    stats = monitor_signal_range(extractor, trace_frames, "EngineSpeed")
    print(f"EngineSpeed: {stats['min']}-{stats['max']} (avg {stats['avg']:.1f})")
```

---

## Next Steps

### Where to Go from Here

1. **Try the examples**: Copy-paste examples above and modify them for your DBC files
2. **Read the API reference**: See `docs/development/PYTHON_API.md` for complete API documentation
3. **Explore example scripts**: Check `examples/batch_operations/` for full working examples
4. **Learn about streaming**: See `docs/tutorials/STREAMING.md` for LTL verification

### Getting Help

- **Build issues**: See `docs/development/BUILDING.md`
- **API questions**: See `docs/development/PYTHON_API.md`
- **Agda details**: See `docs/architecture/DESIGN.md`
- **Project status**: See `PROJECT_STATUS.md`

### Related Documentation

- **Streaming Protocol**: For real-time LTL verification
- **DBC Format**: Understanding CAN database files
- **Signal Encoding**: How signals map to frame bits
- **Multiplexing**: Advanced signal multiplexing patterns

---

**End of Tutorial**

#!/usr/bin/env python3
"""
Batch Trace Processing Example

Demonstrates complete workflows for processing CAN trace files:
- Reading trace files
- Extracting signals from all frames
- Filtering frames by criteria
- Modifying signals in trace
- Writing modified trace
- Statistical analysis

This example shows real-world patterns for offline trace processing.

Usage:
    python3 batch_trace_processing.py
"""

from pathlib import Path
import sys
from typing import List, Dict, Tuple, Optional
import tempfile
import os

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

from aletheia import SignalExtractor, FrameBuilder
from aletheia.dbc_converter import dbc_to_json


# Trace file format: TIMESTAMP CAN_ID DATA0 DATA1 DATA2 DATA3 DATA4 DATA5 DATA6 DATA7
# Example: 0.001234 0x100 00 07 D0 5A 00 00 00 00


def create_sample_trace(filename: str, dbc) -> int:
    """Create a sample trace file for demonstration"""
    print(f"   Creating sample trace: {filename}")

    with FrameBuilder(can_id=0x100, dbc=dbc) as builder:
        with open(filename, 'w') as f:
            # Generate 100 frames over 10 seconds
            for i in range(100):
                timestamp = i * 0.1  # Every 100ms
                speed = 1000 + (i * 10) % 3000  # Varying speed
                temp = 80 + (i // 10) % 40  # Slowly increasing temp
                throttle = 50 + (i % 50)  # Oscillating throttle

                # Build frame
                frame = (builder
                    .set("EngineSpeed", speed)
                    .set("EngineTemp", temp)
                    .set("Throttle", throttle)
                    .build())

                # Write to trace file
                f.write(f"{timestamp:.6f} 0x100 ")
                f.write(" ".join(f"{b:02X}" for b in frame))
                f.write("\n")

    print(f"   ✓ Created trace with 100 frames")
    return 100


def read_trace_file(filename: str) -> List[Tuple[float, int, List[int]]]:
    """Parse trace file into structured data"""
    frames = []

    with open(filename, 'r') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith('#'):
                continue

            try:
                parts = line.split()
                timestamp = float(parts[0])
                can_id = int(parts[1], 16)
                data = [int(b, 16) for b in parts[2:10]]

                if len(data) != 8:
                    print(f"   Warning: Line {line_num} has {len(data)} bytes (expected 8)")
                    continue

                frames.append((timestamp, can_id, data))

            except (ValueError, IndexError) as e:
                print(f"   Warning: Line {line_num} parse error: {e}")

    return frames


def write_trace_file(filename: str, frames: List[Tuple[float, int, List[int]]]):
    """Write frames to trace file"""
    with open(filename, 'w') as f:
        for timestamp, can_id, data in frames:
            f.write(f"{timestamp:.6f} 0x{can_id:X} ")
            f.write(" ".join(f"{b:02X}" for b in data))
            f.write("\n")


def main():
    print("=" * 70)
    print("Batch Trace Processing Example")
    print("=" * 70)

    # Load DBC file
    dbc_path = Path(__file__).parent.parent / "example.dbc"
    print(f"\n1. Loading DBC file: {dbc_path}")

    try:
        dbc = dbc_to_json(dbc_path)
        print("   ✓ DBC loaded successfully")
    except FileNotFoundError:
        print(f"   ✗ DBC file not found: {dbc_path}")
        return 1
    except Exception as e:
        print(f"   ✗ Failed to load DBC: {e}")
        return 1

    # Create temporary directory for trace files
    with tempfile.TemporaryDirectory() as tmpdir:
        trace_original = os.path.join(tmpdir, "trace_original.txt")
        trace_filtered = os.path.join(tmpdir, "trace_filtered.txt")
        trace_modified = os.path.join(tmpdir, "trace_modified.txt")

        # Workflow 1: Create sample trace
        print("\n" + "=" * 70)
        print("WORKFLOW 1: Create Sample Trace")
        print("=" * 70)

        frame_count = create_sample_trace(trace_original, dbc)

        # Workflow 2: Extract and analyze signals
        print("\n" + "=" * 70)
        print("WORKFLOW 2: Extract and Analyze Signals")
        print("=" * 70)

        print("\n   Reading trace file...")
        frames = read_trace_file(trace_original)
        print(f"   ✓ Loaded {len(frames)} frames")

        print("\n   Extracting signals from all frames...")

        with SignalExtractor(dbc=dbc) as extractor:
            # Collect all signal values
            speeds = []
            temps = []
            throttles = []
            error_count = 0

            for timestamp, can_id, data in frames:
                result = extractor.extract(can_id=can_id, data=data)

                if result.has_errors():
                    error_count += 1
                    continue

                speeds.append(result.get("EngineSpeed", 0.0))
                temps.append(result.get("EngineTemp", 0.0))
                throttles.append(result.get("Throttle", 0.0))

            print(f"\n   ✓ Extracted signals from {len(speeds)} frames")
            print(f"   - Errors: {error_count}")

            # Compute statistics
            print("\n   Signal Statistics:")

            if speeds:
                print(f"   EngineSpeed:")
                print(f"   - Min:     {min(speeds):8.2f} RPM")
                print(f"   - Max:     {max(speeds):8.2f} RPM")
                print(f"   - Average: {sum(speeds)/len(speeds):8.2f} RPM")

            if temps:
                print(f"   EngineTemp:")
                print(f"   - Min:     {min(temps):8.2f}°C")
                print(f"   - Max:     {max(temps):8.2f}°C")
                print(f"   - Average: {sum(temps)/len(temps):8.2f}°C")

            if throttles:
                print(f"   Throttle:")
                print(f"   - Min:     {min(throttles):8.2f}%")
                print(f"   - Max:     {max(throttles):8.2f}%")
                print(f"   - Average: {sum(throttles)/len(throttles):8.2f}%")

        # Workflow 3: Filter trace by criteria
        print("\n" + "=" * 70)
        print("WORKFLOW 3: Filter Trace by Criteria")
        print("=" * 70)

        print("\n   Filtering frames where EngineSpeed > 2000 RPM...")

        with SignalExtractor(dbc=dbc) as extractor:
            filtered_frames = []

            for timestamp, can_id, data in frames:
                result = extractor.extract(can_id=can_id, data=data)

                speed = result.get("EngineSpeed", 0.0)
                if speed > 2000:
                    filtered_frames.append((timestamp, can_id, data))

            print(f"   ✓ Found {len(filtered_frames)} frames with EngineSpeed > 2000")

            # Write filtered trace
            write_trace_file(trace_filtered, filtered_frames)
            print(f"   ✓ Written to {trace_filtered}")

        # Workflow 4: Modify signals in trace
        print("\n" + "=" * 70)
        print("WORKFLOW 4: Modify Signals in Trace")
        print("=" * 70)

        print("\n   Modifying trace: Cap EngineSpeed at 2500 RPM...")

        with SignalExtractor(dbc=dbc) as extractor:
            modified_frames = []
            modified_count = 0

            for timestamp, can_id, data in frames:
                # Extract current signals
                result = extractor.extract(can_id=can_id, data=data)
                speed = result.get("EngineSpeed", 0.0)

                # Modify if needed
                if speed > 2500:
                    data = extractor.update(
                        can_id=can_id,
                        frame=data,
                        signals={"EngineSpeed": 2500}
                    )
                    modified_count += 1

                modified_frames.append((timestamp, can_id, data))

            print(f"   ✓ Modified {modified_count} frames")

            # Write modified trace
            write_trace_file(trace_modified, modified_frames)
            print(f"   ✓ Written to {trace_modified}")

            # Verify modification
            print("\n   Verifying modification...")
            max_speed_after = 0.0

            for timestamp, can_id, data in modified_frames:
                result = extractor.extract(can_id=can_id, data=data)
                speed = result.get("EngineSpeed", 0.0)
                max_speed_after = max(max_speed_after, speed)

            print(f"   Max EngineSpeed in modified trace: {max_speed_after:.2f} RPM")

            if max_speed_after <= 2500:
                print("   ✓ Verification passed - all speeds capped at 2500")
            else:
                print(f"   ✗ Verification failed - found speed {max_speed_after}")

        # Workflow 5: Find anomalies
        print("\n" + "=" * 70)
        print("WORKFLOW 5: Find Anomalies")
        print("=" * 70)

        print("\n   Searching for anomalous frames...")

        with SignalExtractor(dbc=dbc) as extractor:
            anomalies = []

            for i, (timestamp, can_id, data) in enumerate(frames):
                result = extractor.extract(can_id=can_id, data=data)

                # Check for anomalies
                speed = result.get("EngineSpeed", 0.0)
                temp = result.get("EngineTemp", 0.0)

                # Anomaly: High speed with low temp
                if speed > 2500 and temp < 85:
                    anomalies.append({
                        "frame": i,
                        "timestamp": timestamp,
                        "type": "High speed with low temp",
                        "speed": speed,
                        "temp": temp
                    })

                # Anomaly: Extraction errors
                if result.has_errors():
                    anomalies.append({
                        "frame": i,
                        "timestamp": timestamp,
                        "type": "Extraction error",
                        "errors": result.errors
                    })

            print(f"   ✓ Found {len(anomalies)} anomalies")

            if anomalies:
                print("\n   Anomaly details:")
                for anom in anomalies[:5]:  # Show first 5
                    print(f"   - Frame {anom['frame']} @ {anom['timestamp']:.3f}s:")
                    print(f"     Type: {anom['type']}")
                    if "speed" in anom:
                        print(f"     Speed={anom['speed']:.0f} RPM, Temp={anom['temp']:.0f}°C")
                    if "errors" in anom:
                        print(f"     Errors: {anom['errors']}")

                if len(anomalies) > 5:
                    print(f"   ... and {len(anomalies) - 5} more")

        # Workflow 6: Generate summary report
        print("\n" + "=" * 70)
        print("WORKFLOW 6: Generate Summary Report")
        print("=" * 70)

        print("\n   Processing trace for summary report...")

        with SignalExtractor(dbc=dbc) as extractor:
            # Collect data
            frame_stats = {
                "total_frames": len(frames),
                "time_span": frames[-1][0] - frames[0][0] if frames else 0,
                "unique_ids": len(set(can_id for _, can_id, _ in frames)),
                "errors": 0,
                "signals": {}
            }

            for timestamp, can_id, data in frames:
                result = extractor.extract(can_id=can_id, data=data)

                if result.has_errors():
                    frame_stats["errors"] += 1

                # Collect signal statistics
                for signal_name, value in result.values.items():
                    if signal_name not in frame_stats["signals"]:
                        frame_stats["signals"][signal_name] = {
                            "count": 0,
                            "min": value,
                            "max": value,
                            "sum": 0.0
                        }

                    stats = frame_stats["signals"][signal_name]
                    stats["count"] += 1
                    stats["min"] = min(stats["min"], value)
                    stats["max"] = max(stats["max"], value)
                    stats["sum"] += value

            # Print report
            print("\n   " + "=" * 66)
            print("   TRACE SUMMARY REPORT")
            print("   " + "=" * 66)

            print(f"\n   Trace Statistics:")
            print(f"   - Total Frames:  {frame_stats['total_frames']}")
            print(f"   - Time Span:     {frame_stats['time_span']:.3f} seconds")
            print(f"   - Unique CAN IDs: {frame_stats['unique_ids']}")
            print(f"   - Error Frames:  {frame_stats['errors']}")

            print(f"\n   Signal Statistics:")
            for signal_name, stats in sorted(frame_stats["signals"].items()):
                avg = stats["sum"] / stats["count"] if stats["count"] > 0 else 0
                print(f"\n   {signal_name}:")
                print(f"   - Occurrences: {stats['count']}")
                print(f"   - Min:         {stats['min']:8.2f}")
                print(f"   - Max:         {stats['max']:8.2f}")
                print(f"   - Average:     {avg:8.2f}")

            print("\n   " + "=" * 66)

    print("\n" + "=" * 70)
    print("Example completed successfully!")
    print("=" * 70)
    print("\nKey Takeaways:")
    print("- Subprocess reused for efficient batch processing")
    print("- Trace files can be read, filtered, modified, and written")
    print("- Statistical analysis easy with extracted signals")
    print("- Anomaly detection patterns straightforward")
    print("- Perfect for offline trace analysis and debugging")
    print("\nCommon Use Cases:")
    print("- Analyze CAN logs from vehicle testing")
    print("- Filter traces by signal criteria")
    print("- Modify signals for simulation/replay")
    print("- Find anomalies or violations")
    print("- Generate summary reports")
    print("\nNext Steps:")
    print("- Review docs/tutorials/BATCH_OPERATIONS.md for more patterns")
    print("- See PYTHON_API.md for complete API reference")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())

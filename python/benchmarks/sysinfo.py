#!/usr/bin/env python3
"""
System Info & Docker Sizing Benchmark

Runs a short benchmark and prints resource usage, throughput, and Docker
sizing recommendations. Designed for quick execution (~5s) so it can be
run in CI or during container setup.

Usage:
    python3 sysinfo.py
"""

import platform
import resource
import sys
import time
from multiprocessing import cpu_count
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.dbc_converter import dbc_to_json

NUM_FRAMES = 2000


def get_rss_mb() -> float:
    """Get current max RSS in MB (works on Linux and macOS)."""
    usage = resource.getrusage(resource.RUSAGE_SELF)
    ru_maxrss = usage.ru_maxrss  # KB on Linux, bytes on macOS
    if platform.system() == "Darwin":
        return ru_maxrss / (1024 * 1024)
    return ru_maxrss / 1024


def load_dbc() -> dict:
    """Load the example DBC file."""
    dbc_path = Path(__file__).parent.parent.parent / "examples" / "example.dbc"
    return dbc_to_json(str(dbc_path))


def main() -> int:
    print("=" * 60)
    print("Aletheia System Info & Docker Sizing")
    print("=" * 60)

    # --- System info ---
    print(f"\nPython:    {sys.version.split()[0]}")
    print(f"Platform:  {platform.platform()}")
    print(f"CPU cores: {cpu_count()}")
    print(f"Arch:      {platform.machine()}")

    # --- Memory: baseline ---
    rss_baseline = get_rss_mb()

    # --- Memory: after hs_init ---
    dbc = load_dbc()
    client = AletheiaClient()
    client.__enter__()
    rss_after_init = get_rss_mb()

    # --- Memory: after parse_dbc ---
    client.parse_dbc(dbc)
    rss_after_dbc = get_rss_mb()

    # --- Throughput: streaming LTL ---
    properties = [
        Signal("EngineSpeed").between(0, 8000).always(),
        Signal("EngineTemp").between(-40, 215).always(),
        Signal("BrakePressure").less_than(6553.5).always(),
    ]
    client.set_properties([p.to_dict() for p in properties])
    client.start_stream()

    frame = [0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]

    # Warmup (100 frames)
    for i in range(100):
        client.send_frame(timestamp=i, can_id=0x100, data=frame)

    start = time.perf_counter()
    for i in range(NUM_FRAMES):
        client.send_frame(timestamp=100 + i, can_id=0x100, data=frame)
    streaming_elapsed = time.perf_counter() - start
    streaming_fps = NUM_FRAMES / streaming_elapsed

    client.end_stream()
    rss_after_streaming = get_rss_mb()

    # --- Throughput: signal extraction ---
    # Warmup
    for _ in range(100):
        client.extract_signals(can_id=0x100, data=frame)

    start = time.perf_counter()
    for _ in range(NUM_FRAMES):
        client.extract_signals(can_id=0x100, data=frame)
    extraction_elapsed = time.perf_counter() - start
    extraction_fps = NUM_FRAMES / extraction_elapsed

    # --- Throughput: frame building ---
    signals = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

    # Warmup
    for _ in range(100):
        client.build_frame(can_id=0x100, signals=signals)

    start = time.perf_counter()
    for _ in range(NUM_FRAMES):
        client.build_frame(can_id=0x100, signals=signals)
    building_elapsed = time.perf_counter() - start
    building_fps = NUM_FRAMES / building_elapsed

    client.close()

    rss_peak = get_rss_mb()

    # --- Report ---
    print(f"\n{'Memory (max RSS)':-<60}")
    print(f"  After hs_init:    {rss_after_init:6.1f} MB")
    print(f"  After parse_dbc:  {rss_after_dbc:6.1f} MB")
    print(f"  After streaming:  {rss_after_streaming:6.1f} MB")
    print(f"  Peak:             {rss_peak:6.1f} MB")

    print(f"\n{'Throughput (2K frames, 1 run)':-<60}")
    print(f"  Streaming LTL:    {streaming_fps:8,.0f} fps  ({1e6 / streaming_fps:6.0f} us/frame)")
    print(f"  Signal Extraction:{extraction_fps:8,.0f} fps  ({1e6 / extraction_fps:6.0f} us/frame)")
    print(f"  Frame Building:   {building_fps:8,.0f} fps  ({1e6 / building_fps:6.0f} us/frame)")

    # --- Docker recommendation ---
    # Use peak RSS + 50% headroom for GC spikes
    recommended_mem_mb = int(rss_peak * 1.5)
    # Round up to next 32 MB boundary for clean Docker values
    recommended_mem_mb = ((recommended_mem_mb + 31) // 32) * 32

    print(f"\n{'Docker Sizing Recommendation':-<60}")
    print(f"  --cpus=1          (GHC RTS is single-threaded)")
    print(f"  --memory={recommended_mem_mb}m       (peak {rss_peak:.0f} MB + 50% headroom)")
    print(f"\n  docker run --cpus=1 --memory={recommended_mem_mb}m your-image")

    print("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())

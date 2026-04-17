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
import sys
import time
from multiprocessing import cpu_count

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient, Signal
# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from ._common import (
    CAN20_CAN_ID, CAN20_DLC, CAN20_FRAME,
    get_rss_mb, load_dbc,
)

NUM_FRAMES = 2000


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
    with AletheiaClient() as client:
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

        # Warmup (100 frames)
        for i in range(100):
            client.send_frame(timestamp=i, can_id=CAN20_CAN_ID, dlc=CAN20_DLC, data=CAN20_FRAME)

        start = time.perf_counter()
        for i in range(NUM_FRAMES):
            client.send_frame(
                timestamp=100 + i, can_id=CAN20_CAN_ID, dlc=CAN20_DLC, data=CAN20_FRAME,
            )
        streaming_elapsed = time.perf_counter() - start
        streaming_fps = NUM_FRAMES / streaming_elapsed

        client.end_stream()
        rss_after_streaming = get_rss_mb()

        # --- Throughput: signal extraction ---
        # Warmup
        for _ in range(100):
            client.extract_signals(can_id=CAN20_CAN_ID, dlc=CAN20_DLC, data=CAN20_FRAME)

        start = time.perf_counter()
        for _ in range(NUM_FRAMES):
            client.extract_signals(can_id=CAN20_CAN_ID, dlc=CAN20_DLC, data=CAN20_FRAME)
        extraction_elapsed = time.perf_counter() - start
        extraction_fps = NUM_FRAMES / extraction_elapsed

        # --- Throughput: frame building ---
        signals = {"EngineSpeed": 2000.0, "EngineTemp": 90.0}

        # Warmup
        for _ in range(100):
            client.build_frame(can_id=CAN20_CAN_ID, dlc=CAN20_DLC, signals=signals)

        start = time.perf_counter()
        for _ in range(NUM_FRAMES):
            client.build_frame(can_id=CAN20_CAN_ID, dlc=CAN20_DLC, signals=signals)
        building_elapsed = time.perf_counter() - start
        building_fps = NUM_FRAMES / building_elapsed

        # Capture peak RSS while resources are still alive (before __exit__).
        rss_peak = get_rss_mb()

    # --- Report ---
    print(f"\n{'Memory (max RSS)':-<60}")
    print(f"  Baseline:         {rss_baseline:6.1f} MB")
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

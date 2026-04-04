#!/usr/bin/env python3
"""Profile CAN-FD extraction to identify bottlenecks.

Breaks down the per-frame cost into:
  A. Python argument preparation (ctypes array construction)
  B. FFI call (Haskell/Agda: Vec construction + extraction + JSON output)
  C. Response parsing (json.loads)
  D. Python result construction (parse_values_list etc.)

Also compares CAN 2.0B (2 signals, 8 bytes) vs CAN-FD (26 signals, 64 bytes)
to show per-signal scaling.

Usage: python3 benchmarks/profile_extraction.py
"""

import ctypes
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "python"))

from aletheia import AletheiaClient
from aletheia.client._helpers import (
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from aletheia.client._types import dlc_to_bytes, validate_can_id
from aletheia.dbc_converter import dbc_to_json

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
ITERATIONS = 5000
WARMUP = 500


def profile_extraction(
    client: AletheiaClient,
    can_id: int,
    dlc: int,
    data: bytearray,
    extended: bool,
    label: str,
) -> None:
    """Profile extraction broken into phases."""
    assert client._lib is not None and client._state is not None
    lib = client._lib
    state = client._state
    expected_bytes = dlc_to_bytes(dlc)
    ext_val = 1 if extended else 0

    # Warmup
    for _ in range(WARMUP):
        client.extract_signals(can_id=can_id, dlc=dlc, data=data)

    # Phase A: argument preparation
    t_prep = 0
    t_ffi = 0
    t_parse = 0
    t_build = 0
    t_free = 0

    for _ in range(ITERATIONS):
        # A: Prepare arguments
        a0 = time.perf_counter_ns()
        validate_can_id(can_id, extended=extended)
        data_array = (ctypes.c_uint8 * len(data))(*data)
        c_can_id = ctypes.c_uint32(can_id)
        c_ext = ctypes.c_uint8(ext_val)
        c_dlc = ctypes.c_uint8(dlc)
        c_len = ctypes.c_uint8(len(data))
        a1 = time.perf_counter_ns()

        # B: FFI call
        result_ptr = lib.aletheia_extract_signals(
            state, c_can_id, c_ext, c_dlc, data_array, c_len,
        )
        a2 = time.perf_counter_ns()

        # C: Parse response (cast + decode + json.loads + free)
        result_bytes = ctypes.cast(result_ptr, ctypes.c_char_p).value
        result_str = result_bytes.decode("utf-8")
        a3 = time.perf_counter_ns()

        response = json.loads(result_str)
        a4 = time.perf_counter_ns()

        lib.aletheia_free_str(result_ptr)

        # D: Build result objects
        values = parse_values_list(response.get("values", []))
        errors = parse_errors_list(response.get("errors", []))
        absent = parse_absent_list(response.get("absent", []))
        a5 = time.perf_counter_ns()

        t_prep += a1 - a0
        t_ffi += a2 - a1
        t_parse += a4 - a3
        t_build += a5 - a4
        t_free += a3 - a2  # cast + decode (before json.loads)

    total = t_prep + t_ffi + t_free + t_parse + t_build
    n = ITERATIONS

    print(f"\n{'=' * 60}")
    print(f"{label} ({n} iterations)")
    print(f"{'=' * 60}")
    print(f"  {'Phase':<35} {'ns/call':>10} {'%':>7}")
    print(f"  {'-' * 55}")
    print(f"  {'A. Arg preparation (ctypes)':<35} {t_prep // n:>10,} {t_prep / total * 100:>6.1f}%")
    print(f"  {'B. FFI call (Haskell/Agda)':<35} {t_ffi // n:>10,} {t_ffi / total * 100:>6.1f}%")
    print(f"  {'C1. cast + decode UTF-8':<35} {t_free // n:>10,} {t_free / total * 100:>6.1f}%")
    print(f"  {'C2. json.loads':<35} {t_parse // n:>10,} {t_parse / total * 100:>6.1f}%")
    print(f"  {'D. Result construction':<35} {t_build // n:>10,} {t_build / total * 100:>6.1f}%")
    print(f"  {'-' * 55}")
    print(f"  {'TOTAL':<35} {total // n:>10,} {'':>7}")
    print(f"  {'fps':<35} {1_000_000_000 * n // total:>10,}")

    # Also print response size
    print(f"\n  Response JSON size: {len(result_str)} bytes")
    print(f"  Signals extracted: {len(values)} values, {len(errors)} errors, {len(absent)} absent")


def profile_ffi_roundtrip(client: AletheiaClient) -> None:
    """Measure bare FFI roundtrip with minimal work (format_dbc — ~no computation)."""
    assert client._lib is not None and client._state is not None
    lib = client._lib
    state = client._state

    # Warmup
    for _ in range(WARMUP):
        ptr = lib.aletheia_format_dbc(state)
        lib.aletheia_free_str(ptr)

    t_total = 0
    for _ in range(ITERATIONS):
        a0 = time.perf_counter_ns()
        ptr = lib.aletheia_format_dbc(state)
        a1 = time.perf_counter_ns()
        lib.aletheia_free_str(ptr)
        t_total += a1 - a0

    print(f"\n{'=' * 60}")
    print(f"FFI roundtrip baseline: format_dbc ({ITERATIONS} iterations)")
    print(f"{'=' * 60}")
    print(f"  Mean: {t_total // ITERATIONS:,} ns/call")


def main() -> int:
    dbc_20 = dbc_to_json(str(EXAMPLES_DIR / "example.dbc"))
    dbc_fd = dbc_to_json(str(EXAMPLES_DIR / "example_canfd.dbc"))

    # CAN 2.0B: 2 signals, 8 bytes
    frame_20 = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])

    # CAN-FD: 26 signals, 64 bytes
    frame_fd = bytearray(
        [0x00, 0xE1, 0xF5, 0x05]
        + [0x00, 0x6C, 0xDC, 0x02]
        + [0xE8, 0x03]
        + [0xD0, 0x07]
        + [0x00, 0x00] * 4
        + [0xE8, 0x03] * 4
        + [0x00] * 36
    )

    print("Aletheia Extraction Profiler")
    print(f"Iterations: {ITERATIONS}, Warmup: {WARMUP}")

    with AletheiaClient() as client:
        # CAN 2.0B
        client.parse_dbc(dbc_20)
        profile_ffi_roundtrip(client)
        profile_extraction(client, 0x100, 8, frame_20, False, "CAN 2.0B (2 signals, 8 bytes)")

    with AletheiaClient() as client:
        # CAN-FD
        client.parse_dbc(dbc_fd)
        profile_extraction(client, 0x200, 15, frame_fd, False, "CAN-FD (26 signals, 64 bytes)")

    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
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

from __future__ import annotations

import ctypes
import json
import time
from pathlib import Path
from typing import NamedTuple, TypedDict, cast

from aletheia import AletheiaClient
from aletheia.client._backend import FFIBackend
from aletheia.client._helpers.json_codec import (
    parse_absent_list,
    parse_errors_list,
    parse_values_list,
)
from aletheia.client._types import validate_can_id
from aletheia.dbc import dbc_to_json
from aletheia.protocols import DLCCode

# --- White-box access note ----------------------------------------------------
# This profiler must reach the raw FFI handles (``client._backend._lib`` +
# ``client._state``) and call ``aletheia_*`` directly so each extraction phase
# (arg prep / FFI / parse / build) can be timed separately -- the backend's
# public methods do all phases in one call and cannot be broken down.  That is
# the same intentional white-box access the C++/Go profilers do against their
# own dlopen handles, and the reason ``benchmarks/**`` carries the ruff S101 /
# SLF001 per-file ignores.  basedpyright's ``reportPrivateUsage`` and pylint's
# protected-access (W0212) are deliberately NOT disabled dir-wide -- they stay
# on across the project; instead each of the handful of private-handle reads
# below is suppressed inline.
# ------------------------------------------------------------------------------


class _ExtractResponse(TypedDict, total=False):
    """The signal-extraction FFI response shape this profiler reads."""

    values: list[object]
    errors: list[object]
    absent: list[object]


class _FrameCase(NamedTuple):
    """One frame to profile (bundled so ``profile_extraction`` stays 2-arg)."""

    can_id: int
    dlc: int
    data: bytearray
    extended: bool
    label: str


class _PhaseTimings(NamedTuple):
    """Accumulated ns across all iterations, per extraction phase."""

    prep: int
    ffi: int
    free: int
    parse: int
    build: int


class _ExtractStats(NamedTuple):
    """Last-iteration response shape, for the human-readable footer."""

    response_bytes: int
    n_values: int
    n_errors: int
    n_absent: int


EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
ITERATIONS = 5000
WARMUP = 500


def _measure_extraction(
    lib: ctypes.CDLL,
    state: int,
    case: _FrameCase,
) -> tuple[_PhaseTimings, _ExtractStats]:
    """Time the four extraction phases over ITERATIONS; return totals + stats."""
    ext_val = 1 if case.extended else 0
    t = [0, 0, 0, 0, 0]  # prep, ffi, free, parse, build
    stats = _ExtractStats(0, 0, 0, 0)
    for _ in range(ITERATIONS):
        prev = time.perf_counter_ns()
        # A: argument preparation (ctypes construction)
        validate_can_id(case.can_id, extended=case.extended)
        ffi_args = (
            ctypes.c_uint32(case.can_id),
            ctypes.c_uint8(ext_val),
            ctypes.c_uint8(case.dlc),
            (ctypes.c_uint8 * len(case.data))(*case.data),
            ctypes.c_uint8(len(case.data)),
        )
        now = time.perf_counter_ns()
        t[0] += now - prev
        prev = now
        # B: FFI call
        result_ptr = lib.aletheia_extract_signals(state, *ffi_args)
        now = time.perf_counter_ns()
        t[1] += now - prev
        prev = now
        # C1: cast + UTF-8 decode
        result_str = cast("bytes", ctypes.cast(result_ptr, ctypes.c_char_p).value).decode("utf-8")
        now = time.perf_counter_ns()
        t[2] += now - prev
        prev = now
        # C2: parse the JSON response
        response = cast("_ExtractResponse", json.loads(result_str))
        now = time.perf_counter_ns()
        t[3] += now - prev
        prev = now
        # D: free the FFI buffer + build Python result objects
        lib.aletheia_free_str(result_ptr)
        stats = _ExtractStats(
            len(result_str),
            len(parse_values_list(response.get("values", []))),
            len(parse_errors_list(response.get("errors", []))),
            len(parse_absent_list(response.get("absent", []))),
        )
        t[4] += time.perf_counter_ns() - prev
    return _PhaseTimings(*t), stats


def _print_extraction_report(label: str, timings: _PhaseTimings, stats: _ExtractStats) -> None:
    """Print the per-phase breakdown table for one profiled frame."""
    total = sum(timings)
    n = ITERATIONS
    rows = (
        ("A. Arg preparation (ctypes)", timings.prep),
        ("B. FFI call (Haskell/Agda)", timings.ffi),
        ("C1. cast + decode UTF-8", timings.free),
        ("C2. json.loads", timings.parse),
        ("D. Result construction", timings.build),
    )
    print(f"\n{'=' * 60}")
    print(f"{label} ({n} iterations)")
    print(f"{'=' * 60}")
    print(f"  {'Phase':<35} {'ns/call':>10} {'%':>7}")
    print(f"  {'-' * 55}")
    for name, ns in rows:
        print(f"  {name:<35} {ns // n:>10,} {ns / total * 100:>6.1f}%")
    print(f"  {'-' * 55}")
    print(f"  {'TOTAL':<35} {total // n:>10,} {'':>7}")
    print(f"  {'fps':<35} {1_000_000_000 * n // total:>10,}")
    print(f"\n  Response JSON size: {stats.response_bytes} bytes")
    print(
        f"  Signals extracted: {stats.n_values} values, "
        + f"{stats.n_errors} errors, {stats.n_absent} absent",
    )


def profile_extraction(client: AletheiaClient, case: _FrameCase) -> None:
    """Profile extraction broken into phases for one frame case."""
    backend = client._backend  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212
    state = client._state  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212
    assert isinstance(backend, FFIBackend)
    assert state is not None
    lib = backend._lib  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212

    for _ in range(WARMUP):
        client.extract_signals(can_id=case.can_id, dlc=DLCCode(case.dlc), data=case.data)

    timings, stats = _measure_extraction(lib, state, case)
    _print_extraction_report(case.label, timings, stats)


def profile_ffi_roundtrip(client: AletheiaClient) -> None:
    """Measure bare FFI roundtrip with minimal work (format_dbc — ~no computation)."""
    backend = client._backend  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212
    state = client._state  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212
    assert isinstance(backend, FFIBackend)
    assert state is not None
    lib = backend._lib  # pyright: ignore[reportPrivateUsage]  # pylint: disable=W0212

    for _ in range(WARMUP):
        lib.aletheia_free_str(lib.aletheia_format_dbc(state))

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


def _canfd_frame() -> bytearray:
    """Build the 64-byte CAN-FD sample frame (26 signals)."""
    return bytearray(
        [0x00, 0xE1, 0xF5, 0x05]
        + [0x00, 0x6C, 0xDC, 0x02]
        + [0xE8, 0x03]
        + [0xD0, 0x07]
        + [0x00, 0x00] * 4
        + [0xE8, 0x03] * 4
        + [0x00] * 36
    )


def main() -> int:
    """Run the FFI-roundtrip baseline and the CAN 2.0B / CAN-FD extraction profiles."""
    dbc_20 = dbc_to_json(str(EXAMPLES_DIR / "example.dbc"))
    dbc_fd = dbc_to_json(str(EXAMPLES_DIR / "example_canfd.dbc"))

    # CAN 2.0B: 2 signals, 8 bytes
    frame_20 = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
    case_20 = _FrameCase(0x100, 8, frame_20, extended=False, label="CAN 2.0B (2 signals, 8 bytes)")
    case_fd = _FrameCase(
        0x200, 15, _canfd_frame(), extended=False, label="CAN-FD (26 signals, 64 bytes)"
    )

    print("Aletheia Extraction Profiler")
    print(f"Iterations: {ITERATIONS}, Warmup: {WARMUP}")

    with AletheiaClient() as client:
        client.parse_dbc(dbc_20)
        profile_ffi_roundtrip(client)
        profile_extraction(client, case_20)

    with AletheiaClient() as client:
        client.parse_dbc(dbc_fd)
        profile_extraction(client, case_fd)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

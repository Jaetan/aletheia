"""Microbenchmark: response parsing overhead on the Python side.

Measures the cost of each step in the ack response path:
1. ctypes.cast to c_char_p + .value  (simulated with bytes)
2. Byte-level ack comparison (current fast path)
3. Full json.loads (slow path / baseline)
4. Dict construction (return {"status": "ack"})
5. UTF-8 decode of violation JSON
6. json.loads of violation JSON

Run: python3 benchmarks/response_overhead.py
"""

from __future__ import annotations

import json
import time
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Callable

ITERATIONS = 2_000_000
WARMUP = 100_000

# Simulated raw bytes from FFI (what ctypes.cast().value returns)
ACK_BYTES = b'{"status":"ack"}'
ACK_BYTES_SPACED = b'{"status": "ack"}'

VIOLATION_BYTES = (
    b'{"type":"property","status":"fails","property_index":0,'
    b'"timestamp":1234567890,"reason":"Signal EngineSpeed exceeded 220"}'
)

# Pre-built constants (matching client code)
_ACK_BYTES = b'{"status":"ack"}'
_ACK_BYTES_SPACED = b'{"status": "ack"}'
_BINARY_ACK = b"\x00"


# --- Ack-path step functions (return discarded; only timing matters) ---
def _ack_byte_cmp() -> bool:
    return ACK_BYTES in (_ACK_BYTES, _ACK_BYTES_SPACED)


def _ack_dict() -> dict[str, str]:
    return {"status": "ack"}


def _ack_fast_path() -> dict[str, str] | None:
    if ACK_BYTES in (_ACK_BYTES, _ACK_BYTES_SPACED):
        return {"status": "ack"}
    return None


def _ack_json_loads() -> object:
    return json.loads(ACK_BYTES)


def _ack_decode_json() -> object:
    return json.loads(ACK_BYTES.decode("utf-8"))


def _ack_binary_read() -> int:
    return _BINARY_ACK[0]


def _ack_binary_full() -> dict[str, str] | None:
    if _BINARY_ACK[0] == 0:
        return {"status": "ack"}
    return None


# --- Violation-path step functions ---
def _viol_decode() -> str:
    return VIOLATION_BYTES.decode("utf-8")


def _viol_json() -> object:
    return json.loads(VIOLATION_BYTES)


def _viol_full() -> object:
    return json.loads(VIOLATION_BYTES.decode("utf-8"))


def bench(name: str, func: Callable[[], object], iterations: int = ITERATIONS) -> float:
    """Run ``func()`` ``iterations`` times, return ns/op (the return is discarded)."""
    # Warmup
    for _ in range(WARMUP):
        func()
    # Timed
    start = time.perf_counter_ns()
    for _ in range(iterations):
        func()
    elapsed = time.perf_counter_ns() - start
    ns_per_op = elapsed / iterations
    print(f"  {name:45s}  {ns_per_op:8.1f} ns/op")
    return ns_per_op


def main() -> None:
    """Run the ack/violation response-parsing microbenchmarks and print a report."""
    print("Response parsing overhead (Python)")
    print(f"Iterations: {ITERATIONS:,}\n")

    print("=== Ack response (hot path, ~99% of frames) ===")
    bench("byte comparison (in tuple)", _ack_byte_cmp)
    bench("dict construction", _ack_dict)
    t_fast = bench("full fast path (cmp + dict)", _ack_fast_path)
    t_json = bench("json.loads(ack_bytes)", _ack_json_loads)
    bench("decode + json.loads", _ack_decode_json)
    bench("binary: read status byte", _ack_binary_read)
    t_bin_full = bench("binary: read byte + dict", _ack_binary_full)

    print()
    print(f"  Fast path saves vs json.loads:   {t_json - t_fast:8.1f} ns/frame")
    print(f"  Binary would save vs fast path:  {t_fast - t_bin_full:8.1f} ns/frame")
    print(f"  Binary would save vs json.loads: {t_json - t_bin_full:8.1f} ns/frame")

    print("\n=== Violation response (rare, <1% of frames) ===")
    bench("decode UTF-8", _viol_decode, iterations=500_000)
    bench("json.loads(violation_bytes)", _viol_json, iterations=500_000)
    bench("decode + json.loads", _viol_full, iterations=500_000)

    print("\n=== Context ===")
    frame_budget_ns = 1_000_000_000 / 48_000  # ~20.8 us at 48k fps
    print(f"  Per-frame budget at 48k fps:     {frame_budget_ns:8.0f} ns")
    print(f"  Fast path % of budget:           {t_fast / frame_budget_ns * 100:8.1f}%")
    print(f"  json.loads % of budget:          {t_json / frame_budget_ns * 100:8.1f}%")
    print(f"  Binary % of budget:              {t_bin_full / frame_budget_ns * 100:8.1f}%")


if __name__ == "__main__":
    main()

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

import json
import time

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


def bench(name: str, func, iterations: int = ITERATIONS) -> float:
    """Run func() iterations times, return ns/op."""
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
    print("Response parsing overhead (Python)")
    print(f"Iterations: {ITERATIONS:,}\n")

    # --- Ack path components ---
    print("=== Ack response (hot path, ~99% of frames) ===")

    # 1. Byte comparison (current fast path)
    def ack_byte_cmp():
        return ACK_BYTES in (_ACK_BYTES, _ACK_BYTES_SPACED)

    # 2. Dict construction
    def ack_dict():
        return {"status": "ack"}

    # 3. Full fast path (compare + dict)
    def ack_fast_path():
        if ACK_BYTES in (_ACK_BYTES, _ACK_BYTES_SPACED):
            return {"status": "ack"}
        return None

    # 4. json.loads (what we'd pay without fast path)
    def ack_json_loads():
        return json.loads(ACK_BYTES)

    # 5. Decode + json.loads
    def ack_decode_json():
        s = ACK_BYTES.decode("utf-8")
        return json.loads(s)

    # 6. Hypothetical binary: read first byte
    binary_ack = b'\x00'
    def ack_binary_read():
        return binary_ack[0]

    # 7. Hypothetical binary: read byte + return dict
    def ack_binary_full():
        if binary_ack[0] == 0:
            return {"status": "ack"}
        return None

    t_cmp = bench("byte comparison (in tuple)", ack_byte_cmp)
    t_dict = bench("dict construction", ack_dict)
    t_fast = bench("full fast path (cmp + dict)", ack_fast_path)
    t_json = bench("json.loads(ack_bytes)", ack_json_loads)
    t_dec_json = bench("decode + json.loads", ack_decode_json)
    t_bin_read = bench("binary: read status byte", ack_binary_read)
    t_bin_full = bench("binary: read byte + dict", ack_binary_full)

    print()
    print(f"  Fast path saves vs json.loads:   {t_json - t_fast:8.1f} ns/frame")
    print(f"  Binary would save vs fast path:  {t_fast - t_bin_full:8.1f} ns/frame")
    print(f"  Binary would save vs json.loads: {t_json - t_bin_full:8.1f} ns/frame")

    # --- Violation path ---
    print("\n=== Violation response (rare, <1% of frames) ===")

    def viol_decode():
        return VIOLATION_BYTES.decode("utf-8")

    def viol_json():
        return json.loads(VIOLATION_BYTES)

    def viol_full():
        s = VIOLATION_BYTES.decode("utf-8")
        return json.loads(s)

    bench("decode UTF-8", viol_decode, iterations=500_000)
    bench("json.loads(violation_bytes)", viol_json, iterations=500_000)
    bench("decode + json.loads", viol_full, iterations=500_000)

    # --- Context: per-frame budget ---
    print("\n=== Context ===")
    frame_budget_ns = 1_000_000_000 / 48_000  # ~20.8 us at 48k fps
    print(f"  Per-frame budget at 48k fps:     {frame_budget_ns:8.0f} ns")
    print(f"  Fast path % of budget:           {t_fast / frame_budget_ns * 100:8.1f}%")
    print(f"  json.loads % of budget:          {t_json / frame_budget_ns * 100:8.1f}%")
    print(f"  Binary % of budget:              {t_bin_full / frame_budget_ns * 100:8.1f}%")


if __name__ == "__main__":
    main()

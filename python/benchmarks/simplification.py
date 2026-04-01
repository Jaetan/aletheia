#!/usr/bin/env python3
"""
Simplification Stress Benchmark

Tests whether Rosu formula simplification keeps the formula tree bounded
for different LTL formula patterns. Measures FPS at increasing trace lengths
to detect tree growth (FPS degradation = tree growth).

Formula categories tested:
  - Simple safety:    G(p)                  (Always absorption fires)
  - Compound safety:  G(p ∧ q ∧ r)         (And inside Always)
  - Implication:      G(p → q)             (Or/Not inside Always)
  - Liveness:         F(p)                  (Eventually, p keeps failing)
  - Infinitely often: G(F(p))              (nested Always/Eventually)
  - Stability:        F(G(p))              (nested Eventually/Always)
  - Until (atomic):   p U q                (q keeps failing, p succeeds)
  - Until (temporal): G(p) U q             (temporal inner, stress test)
  - Release (atomic): p R q               (dual of Until)
  - Bounded response: G(p → q within 100) (implication + MetricEventually)
  - Multi-property:   5× independent G(pᵢ) (parallel evaluation)

Usage:
    python3 simplification.py [--quick] [--json]
"""

import argparse
import json
import os
import platform
import resource
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from aletheia import AletheiaClient, Signal
from aletheia.dsl import Property, infinitely_often, eventually_always
from aletheia.dbc_converter import dbc_to_json

EXAMPLES_DIR = Path(__file__).parent.parent.parent / "examples"

# Frame data: EngineSpeed=2000, EngineTemp=90 (all signals in normal range)
CAN20_FRAME = bytearray([0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00])
CAN20_CAN_ID = 0x100
CAN20_DLC = 8

# Timestamp spacing: 10 time-units per frame.
# Metric windows use the same unit, so within(1000) = 100 frames.
TS_STEP = 10


def load_dbc() -> dict:
    return dbc_to_json(str(EXAMPLES_DIR / "example.dbc"))


def get_rss_mb() -> float:
    """Current max RSS in MB."""
    usage = resource.getrusage(resource.RUSAGE_SELF)
    if platform.system() == "Darwin":
        return usage.ru_maxrss / (1024 * 1024)
    return usage.ru_maxrss / 1024


# ============================================================================
# Formula definitions
# ============================================================================
# Each returns a list of property dicts.
#
# Invariant: with CAN20_FRAME data (EngineSpeed=2000, EngineTemp=90):
#   between(0, 8000) → True     less_than(1000) → False
#   between(-40, 215) → True    less_than(50)   → False
#   less_than(8000)   → True    greater_than(3000) → False

def simple_safety() -> list[dict]:
    """G(speed ∈ [0,8000]) — Always absorption fires every frame."""
    return [Signal("EngineSpeed").between(0, 8000).always().to_dict()]


def compound_safety() -> list[dict]:
    """G(speed ∈ [0,8000] ∧ temp ∈ [-40,215]) — And inside Always."""
    p = Signal("EngineSpeed").between(0, 8000).and_(
        Signal("EngineTemp").between(-40, 215)
    ).always()
    return [p.to_dict()]


def implication_safety() -> list[dict]:
    """G(speed < 1000 → temp < 100) — Or/Not inside Always.
    Antecedent is False (speed=2000), so implication trivially True each frame."""
    p = Signal("EngineSpeed").less_than(1000).implies(
        Signal("EngineTemp").less_than(100)
    ).always()
    return [p.to_dict()]


def simple_liveness() -> list[dict]:
    """F(speed > 3000) — Eventually; predicate stays False, formula self-loops."""
    return [Signal("EngineSpeed").greater_than(3000).eventually().to_dict()]


def infinitely_often_pattern() -> list[dict]:
    """G(F(speed > 3000)) — Nested Always/Eventually.
    Eventually never resolves (speed=2000), Always wraps it."""
    p = infinitely_often(Signal("EngineSpeed").greater_than(3000))
    return [p.to_dict()]


def stability_pattern() -> list[dict]:
    """F(G(speed < 8000)) — Nested Eventually/Always.
    Always(speed<8000) succeeds immediately, so Eventually resolves at first frame."""
    p = eventually_always(Signal("EngineSpeed").less_than(8000))
    return [p.to_dict()]


def until_atomic() -> list[dict]:
    """(speed < 8000) U (temp < 50) — Until with atomic predicates.
    LHS True (2000<8000), RHS False (90≮50). Until stays active.
    Atomic predicates resolve immediately → no tree growth."""
    lhs = Signal("EngineSpeed").less_than(8000).always()  # wrap for Property type
    rhs = Signal("EngineTemp").less_than(50).always()
    # Build Until directly via JSON (Until of raw predicates)
    p: dict = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).to_formula(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    return [p]


def until_temporal() -> list[dict]:
    """G(speed < 8000) U (temp < 50) — Until with temporal inner formula.
    G(speed<8000) returns Continue (Always self-loop), temp<50 stays False.
    Tests whether And-And idempotency keeps the tree bounded."""
    p: dict = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).always().to_dict(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    return [p]


def release_atomic() -> list[dict]:
    """(temp < 50) R (speed < 8000) — Release with atomic predicates.
    LHS False (90≮50), RHS True (2000<8000). Release stays active."""
    p: dict = {
        "operator": "release",
        "left": Signal("EngineTemp").less_than(50).to_formula(),
        "right": Signal("EngineSpeed").less_than(8000).to_formula(),
    }
    return [p]


def bounded_response() -> list[dict]:
    """G(speed > 3000 → temp < 50 within 100) — implication + metric.
    Antecedent False (speed=2000), so MetricEventually never activates."""
    inner = Signal("EngineSpeed").greater_than(3000).implies(
        Signal("EngineTemp").less_than(50).within(100)
    )
    p = inner.always()
    return [p.to_dict()]


def bounded_response_active() -> list[dict]:
    """G(speed < 8000 → temp < 50 within 1000) — implication + metric.
    Antecedent True (speed=2000), MetricEventually activates but temp<50 never
    holds, so window expires and Violated. Tests metric operator churn."""
    inner = Signal("EngineSpeed").less_than(8000).implies(
        Signal("EngineTemp").less_than(50).within(1000)
    )
    p = inner.always()
    return [p.to_dict()]


def multi_property() -> list[dict]:
    """5 independent G(pᵢ) properties — parallel formula evaluation."""
    return [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
        Signal("EngineSpeed").less_than(7000).always().to_dict(),
        Signal("EngineTemp").less_than(200).always().to_dict(),
        Signal("EngineSpeed").between(500, 7500).always().to_dict(),
    ]


def nested_until() -> list[dict]:
    """(speed < 8000 U temp < 50) ∧ G(speed < 8000) — Until + parallel Always.
    Tests interaction of Until accumulation with Always absorption."""
    until: dict = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).to_formula(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    always = Signal("EngineSpeed").less_than(8000).always().to_dict()
    return [until, always]


# ============================================================================
# Benchmark runner
# ============================================================================

FORMULAS: list[tuple[str, callable]] = [
    ("G(p)              simple safety", simple_safety),
    ("G(p∧q)            compound safety", compound_safety),
    ("G(p→q)            implication", implication_safety),
    ("F(p)              liveness", simple_liveness),
    ("G(F(p))           infinitely often", infinitely_often_pattern),
    ("F(G(p))           stability", stability_pattern),
    ("p U q             until (atomic)", until_atomic),
    ("G(p) U q          until (temporal)", until_temporal),
    ("p R q             release (atomic)", release_atomic),
    ("G(p→q w/in 100)   bounded response", bounded_response),
    ("G(p→q w/in 1000)  bounded active", bounded_response_active),
    ("5×G(pᵢ)           multi-property", multi_property),
    ("(p U q) ∧ G(p)    until + always", nested_until),
]


def bench_formula(
    dbc: dict,
    properties: list[dict],
    num_frames: int,
) -> float:
    """Run a single benchmark. Returns frames/sec."""
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        for i in range(num_frames):
            client.send_frame(
                timestamp=i * TS_STEP,
                can_id=CAN20_CAN_ID,
                dlc=CAN20_DLC,
                data=CAN20_FRAME,
            )
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed


def main() -> int:
    parser = argparse.ArgumentParser(description="Simplification stress benchmark")
    parser.add_argument("--quick", action="store_true", help="Fewer frames")
    parser.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    args = parser.parse_args()

    out = sys.stderr if args.json else sys.stdout
    sizes = [1000, 10000, 50000] if args.quick else [1000, 10000, 50000, 100000]

    print("=" * 90, file=out)
    print("Aletheia Simplification Stress Benchmark", file=out)
    print("=" * 90, file=out)
    print(f"Trace sizes: {', '.join(f'{s:,}' for s in sizes)} frames", file=out)
    print(f"Timestamp step: {TS_STEP} per frame", file=out)
    print(file=out)

    dbc = load_dbc()

    # Warmup
    print("Warming up...", file=out)
    bench_formula(dbc, simple_safety(), 500)
    print(file=out)

    # Header
    size_headers = "".join(f"{'%dk' % (s // 1000):>10}" for s in sizes)
    print(f"{'Formula':<30}{size_headers}{'Ratio':>8}{'RSS MB':>8}", file=out)
    print("-" * (30 + 10 * len(sizes) + 16), file=out)

    all_results = []

    for label, make_props in FORMULAS:
        properties = make_props()

        fps_values = []
        for size in sizes:
            fps = bench_formula(dbc, properties, size)
            fps_values.append(fps)

        rss = get_rss_mb()

        # Ratio: last / first (< 1.0 means degradation)
        ratio = fps_values[-1] / fps_values[0] if fps_values[0] > 0 else 0

        fps_strs = "".join(f"{fps:>10,.0f}" for fps in fps_values)
        print(f"{label:<30}{fps_strs}{ratio:>7.2f}x{rss:>7.1f}", file=out)

        all_results.append({
            "formula": label.strip(),
            "fps": {f"{s // 1000}k": round(fps, 1) for s, fps in zip(sizes, fps_values)},
            "ratio_last_first": round(ratio, 3),
            "rss_mb": round(rss, 1),
        })

    print("-" * (30 + 10 * len(sizes) + 16), file=out)
    print(file=out)
    print("Ratio = fps(last) / fps(first). Values near 1.0 = constant throughput.", file=out)
    print("Values << 1.0 indicate tree growth (simplification not keeping up).", file=out)
    print("RSS is max RSS after each formula's runs (monotonically increasing).", file=out)

    if args.json:
        output = {
            "benchmark": "simplification",
            "language": "python",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "system": {
                "cpu": platform.processor() or platform.machine(),
                "cores": os.cpu_count() or 0,
                "platform": platform.system(),
                "python": platform.python_version(),
            },
            "trace_sizes": sizes,
            "results": all_results,
        }
        print(json.dumps(output, indent=2))

    return 0


if __name__ == "__main__":
    sys.exit(main())

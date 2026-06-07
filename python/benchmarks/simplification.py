#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Simplification Stress Benchmark.

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

from __future__ import annotations

import argparse
import sys
import time
from typing import IO, TYPE_CHECKING, TypedDict

# Shared vocabulary lives in ``_common``; see PY-31-1 for the dedup rationale.
from benchmarks._common import (
    CAN20_SPEC,
    emit_json_report,
    get_rss_mb,
    load_dbc,
)

# See ``throughput.py`` — benchmarks import the installed package to keep
# the wheel / setuptools shim cost inside the measurement.
from aletheia import AletheiaClient, Signal
from aletheia.dsl import eventually_always, infinitely_often

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.types import (
        DBCDefinition,
        LTLFormula,
        ReleaseFormula,
        UntilFormula,
    )


class _FormulaResult(TypedDict):
    """One row of the simplification-stress table (per-formula across trace sizes)."""

    formula: str
    fps: dict[str, float]
    ratio_last_first: float
    rss_mb: float


class _SimplificationReport(TypedDict):
    """JSON-report payload combining the size sweep with per-formula rows."""

    trace_sizes: list[int]
    formulas: list[_FormulaResult]


# Timestamp spacing: 10 time-units per frame.
# Metric windows use the same unit, so within(1000) = 100 frames.
TS_STEP = 10


# ============================================================================
# Formula definitions
# ============================================================================
# Each returns a list of property dicts.
#
# Invariant: with CAN20_FRAME data (EngineSpeed=2000, EngineTemp=90):
#   between(0, 8000) → True     less_than(1000) → False
#   between(-40, 215) → True    less_than(50)   → False
#   less_than(8000)   → True    greater_than(3000) → False


def simple_safety() -> list[LTLFormula]:
    """G(speed ∈ [0,8000]) — Always absorption fires every frame."""
    return [Signal("EngineSpeed").between(0, 8000).always().to_dict()]


def compound_safety() -> list[LTLFormula]:
    """G(speed ∈ [0,8000] ∧ temp ∈ [-40,215]) — And inside Always."""
    p = Signal("EngineSpeed").between(0, 8000).and_(Signal("EngineTemp").between(-40, 215)).always()
    return [p.to_dict()]


def implication_safety() -> list[LTLFormula]:
    """G(speed < 1000 → temp < 100) — Or/Not inside Always.

    Antecedent is False (speed=2000), so implication trivially True each frame.
    """
    p = Signal("EngineSpeed").less_than(1000).implies(Signal("EngineTemp").less_than(100)).always()
    return [p.to_dict()]


def simple_liveness() -> list[LTLFormula]:
    """F(speed > 3000) — Eventually; predicate stays False, formula self-loops."""
    return [Signal("EngineSpeed").greater_than(3000).eventually().to_dict()]


def infinitely_often_pattern() -> list[LTLFormula]:
    """G(F(speed > 3000)) — Nested Always/Eventually.

    Eventually never resolves (speed=2000), Always wraps it.
    """
    p = infinitely_often(Signal("EngineSpeed").greater_than(3000))
    return [p.to_dict()]


def stability_pattern() -> list[LTLFormula]:
    """F(G(speed < 8000)) — Nested Eventually/Always.

    Always(speed<8000) succeeds immediately, so Eventually resolves at first frame.
    """
    p = eventually_always(Signal("EngineSpeed").less_than(8000))
    return [p.to_dict()]


def until_atomic() -> list[LTLFormula]:
    """(speed < 8000) U (temp < 50) — Until with atomic predicates.

    LHS True (2000<8000), RHS False (90≮50). Until stays active.
    Atomic predicates resolve immediately → no tree growth.
    """
    # Build Until directly via TypedDict (Until of raw predicates)
    p: UntilFormula = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).to_formula(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    return [p]


def until_temporal() -> list[LTLFormula]:
    """G(speed < 8000) U (temp < 50) — Until with temporal inner formula.

    G(speed<8000) returns Continue (Always self-loop), temp<50 stays False.
    Tests whether And-And idempotency keeps the tree bounded.
    """
    p: UntilFormula = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).always().to_dict(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    return [p]


def release_atomic() -> list[LTLFormula]:
    """(temp < 50) R (speed < 8000) — Release with atomic predicates.

    LHS False (90≮50), RHS True (2000<8000). Release stays active.
    """
    p: ReleaseFormula = {
        "operator": "release",
        "left": Signal("EngineTemp").less_than(50).to_formula(),
        "right": Signal("EngineSpeed").less_than(8000).to_formula(),
    }
    return [p]


def bounded_response() -> list[LTLFormula]:
    """G(speed > 3000 → temp < 50 within 100) — implication + metric.

    Antecedent False (speed=2000), so MetricEventually never activates.
    """
    inner = (
        Signal("EngineSpeed")
        .greater_than(3000)
        .implies(Signal("EngineTemp").less_than(50).within(100))
    )
    p = inner.always()
    return [p.to_dict()]


def bounded_response_active() -> list[LTLFormula]:
    """G(speed < 8000 → temp < 50 within 1000) — implication + metric.

    Antecedent True (speed=2000), MetricEventually activates but temp<50 never
    holds, so window expires and Violated. Tests metric operator churn.
    """
    inner = (
        Signal("EngineSpeed")
        .less_than(8000)
        .implies(Signal("EngineTemp").less_than(50).within(1000))
    )
    p = inner.always()
    return [p.to_dict()]


def multi_property() -> list[LTLFormula]:
    """5 independent G(pᵢ) properties — parallel formula evaluation."""
    return [
        Signal("EngineSpeed").between(0, 8000).always().to_dict(),
        Signal("EngineTemp").between(-40, 215).always().to_dict(),
        Signal("EngineSpeed").less_than(7000).always().to_dict(),
        Signal("EngineTemp").less_than(200).always().to_dict(),
        Signal("EngineSpeed").between(500, 7500).always().to_dict(),
    ]


def nested_until() -> list[LTLFormula]:
    """(speed < 8000 U temp < 50) ∧ G(speed < 8000) — Until + parallel Always.

    Tests interaction of Until accumulation with Always absorption.
    """
    until: UntilFormula = {
        "operator": "until",
        "left": Signal("EngineSpeed").less_than(8000).to_formula(),
        "right": Signal("EngineTemp").less_than(50).to_formula(),
    }
    always = Signal("EngineSpeed").less_than(8000).always().to_dict()
    return [until, always]


# ============================================================================
# Benchmark runner
# ============================================================================

FORMULAS: list[tuple[str, Callable[[], list[LTLFormula]]]] = [
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


def bench_formula(dbc: DBCDefinition, properties: list[LTLFormula], num_frames: int) -> float:
    """Run a single benchmark. Returns frames/sec."""
    spec = CAN20_SPEC
    with AletheiaClient() as client:
        client.parse_dbc(dbc)
        client.set_properties(properties)
        client.start_stream()

        start = time.perf_counter()
        # R0801 false positive: this per-frame send loop IS the throughput
        # being measured; the only cross-benchmark difference is the timestamp
        # expression. Extracting a shared helper would add a call per frame and
        # skew the measurement, so the loop is kept inline in each benchmark.
        # pylint: disable=duplicate-code
        for i in range(num_frames):
            client.send_frame(
                timestamp=i * TS_STEP,
                can_id=spec.can_id,
                dlc=spec.dlc,
                data=spec.payload,
            )
        # pylint: enable=duplicate-code
        elapsed = time.perf_counter() - start

        client.end_stream()

    return num_frames / elapsed


def _run_one_formula(
    label: str,
    make_props: Callable[[], list[LTLFormula]],
    dbc: DBCDefinition,
    sizes: list[int],
    file: IO[str],
) -> _FormulaResult:
    """Sweep one formula across all trace sizes; print + return one row."""
    properties = make_props()
    fps_values = [bench_formula(dbc, properties, size) for size in sizes]
    rss = get_rss_mb()
    ratio = fps_values[-1] / fps_values[0] if fps_values[0] > 0 else 0
    fps_strs = "".join(f"{fps:>10,.0f}" for fps in fps_values)
    print(f"{label:<30}{fps_strs}{ratio:>7.2f}x{rss:>7.1f}", file=file)
    return {
        "formula": label.strip(),
        "fps": {f"{s // 1000}k": round(fps, 1) for s, fps in zip(sizes, fps_values, strict=True)},
        "ratio_last_first": round(ratio, 3),
        "rss_mb": round(rss, 1),
    }


def main() -> int:
    """CLI entry point — sweep every FORMULAS row across trace sizes."""
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
    size_headers = "".join(f"{f'{s // 1000}k':>10}" for s in sizes)
    print(f"{'Formula':<30}{size_headers}{'Ratio':>8}{'RSS MB':>8}", file=out)
    print("-" * (30 + 10 * len(sizes) + 16), file=out)

    all_results = [
        _run_one_formula(label, make_props, dbc, sizes, out) for label, make_props in FORMULAS
    ]

    print("-" * (30 + 10 * len(sizes) + 16), file=out)
    print(file=out)
    print("Ratio = fps(last) / fps(first). Values near 1.0 = constant throughput.", file=out)
    print("Values << 1.0 indicate tree growth (simplification not keeping up).", file=out)
    print("RSS is max RSS after each formula's runs (monotonically increasing).", file=out)

    if args.json:
        report: _SimplificationReport = {"trace_sizes": sizes, "formulas": all_results}
        emit_json_report("simplification", report)

    return 0


if __name__ == "__main__":
    sys.exit(main())

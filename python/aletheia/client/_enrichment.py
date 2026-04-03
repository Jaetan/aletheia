"""Formula enrichment helpers — formatting, signal collection, diagnostics.

Module-level functions, testable without an AletheiaClient instance.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from ..protocols import LTLFormula
from ._types import PropertyDiagnostic

_MAX_FORMULA_DEPTH = 100

_UNARY_OPS = frozenset({
    "not", "next", "always", "eventually", "metricAlways", "metricEventually",
})
_BINARY_OPS = frozenset({
    "and", "or", "until", "release", "metricUntil", "metricRelease",
})


def _walk_formula(
    formula: dict[str, object],
    on_atomic: Callable[[dict[str, object]], None],
    depth: int = 0,
) -> None:
    """Walk a formula tree, calling on_atomic for each atomic node.

    Raises ValueError if nesting exceeds _MAX_FORMULA_DEPTH.
    """
    if depth > _MAX_FORMULA_DEPTH:
        raise ValueError(
            f"Formula nesting depth exceeds {_MAX_FORMULA_DEPTH}"
        )
    op = formula.get("operator")
    if op == "atomic":
        on_atomic(cast(dict[str, object], formula["predicate"]))
    elif op in _UNARY_OPS:
        _walk_formula(
            cast(dict[str, object], formula["formula"]),
            on_atomic, depth + 1,
        )
    elif op in _BINARY_OPS:
        _walk_formula(
            cast(dict[str, object], formula["left"]),
            on_atomic, depth + 1,
        )
        _walk_formula(
            cast(dict[str, object], formula["right"]),
            on_atomic, depth + 1,
        )


_COMPARISON_OPS: dict[str, str] = {
    "equals": "=", "lessThan": "<", "greaterThan": ">",
    "lessThanOrEqual": "<=", "greaterThanOrEqual": ">=",
}


def _format_predicate(pred: dict[str, object]) -> str:
    """Format a predicate dict as a human-readable string."""
    kind = pred.get("predicate")
    signal = str(pred.get("signal", ""))
    op = _COMPARISON_OPS.get(str(kind))
    if op is not None:
        return f"{signal} {op} {pred['value']:g}"
    if kind == "between":
        return f"{pred['min']:g} <= {signal} <= {pred['max']:g}"
    if kind == "changedBy":
        d = pred['delta']
        if d >= 0:
            return f"\u0394{signal} >= {d:g}"
        return f"\u0394{signal} <= {d:g}"
    if kind == "stableWithin":
        return f"|\u0394{signal}| <= {pred['tolerance']:g}"
    return "<unknown predicate>"


def _format_timebound(us: int) -> str:
    """Format microseconds as a human-readable time bound."""
    if us % 1_000_000 == 0:
        return f"{us // 1_000_000}s "
    if us % 1_000 == 0:
        return f"{us // 1_000}ms "
    return f"{us}\u00b5s "


def _get_timebound(formula: dict[str, object]) -> str:
    """Extract and format the timebound from a metric formula."""
    tb = formula.get("timebound")
    if isinstance(tb, (int, float)) and not isinstance(tb, bool):
        return _format_timebound(int(tb))
    return ""


def format_formula(  # pylint: disable=too-many-return-statements,too-many-branches
    formula: dict[str, object], depth: int = 0,
) -> str:
    """Format an LTL formula dict as a human-readable string.

    Raises ValueError if nesting exceeds _MAX_FORMULA_DEPTH.
    """
    if depth > _MAX_FORMULA_DEPTH:
        raise ValueError(
            f"Formula nesting depth exceeds {_MAX_FORMULA_DEPTH}"
        )
    op = formula.get("operator")
    if op == "atomic":
        return _format_predicate(cast(dict[str, object], formula["predicate"]))
    if op == "not":
        return "not(" + format_formula(cast(dict[str, object], formula["formula"]), depth + 1) + ")"
    if op == "and":
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " and "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    if op == "or":
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " or "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    if op == "next":
        return "next(" + format_formula(cast(dict[str, object], formula["formula"]), depth + 1) + ")"
    if op == "always":
        inner = cast(dict[str, object], formula["formula"])
        # Detect Never pattern: always(not(atomic(p)))
        if inner.get("operator") == "not":
            inner_not = cast(dict[str, object], inner["formula"])
            if inner_not.get("operator") == "atomic":
                return "never " + _format_predicate(cast(dict[str, object], inner_not["predicate"]))
        return "always(" + format_formula(inner, depth + 1) + ")"
    if op == "eventually":
        return "eventually(" + format_formula(cast(dict[str, object], formula["formula"]), depth + 1) + ")"
    if op == "until":
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " until "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    if op == "release":
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " release "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    if op == "metricAlways":
        tb = _get_timebound(formula)
        return ("always within " + tb + "("
                + format_formula(cast(dict[str, object], formula["formula"]), depth + 1) + ")")
    if op == "metricEventually":
        tb = _get_timebound(formula)
        return ("eventually within " + tb + "("
                + format_formula(cast(dict[str, object], formula["formula"]), depth + 1) + ")")
    if op == "metricUntil":
        tb = _get_timebound(formula)
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " until within " + tb + " "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    if op == "metricRelease":
        tb = _get_timebound(formula)
        return (format_formula(cast(dict[str, object], formula["left"]), depth + 1)
                + " release within " + tb + " "
                + format_formula(cast(dict[str, object], formula["right"]), depth + 1))
    return "<unknown>"


def collect_signals(formula: dict[str, object]) -> list[str]:
    """Collect all signal names from a formula, deduplicated, in order.

    Raises ValueError if nesting exceeds _MAX_FORMULA_DEPTH.
    """
    signals: list[str] = []
    seen: set[str] = set()

    def on_atomic(pred: dict[str, object]) -> None:
        name = str(pred.get("signal", ""))
        if name and name not in seen:
            seen.add(name)
            signals.append(name)

    _walk_formula(formula, on_atomic)
    return signals


def build_diagnostic(formula: LTLFormula) -> PropertyDiagnostic:
    """Build a PropertyDiagnostic from a formula. Always succeeds."""
    f = cast(dict[str, object], formula)
    return PropertyDiagnostic(
        signals=collect_signals(f),
        formula_desc=format_formula(f),
    )


def format_enriched_reason(
    diag: PropertyDiagnostic, values: dict[str, float | None],
) -> str:
    """Build the enriched reason string."""
    parts: list[str] = []
    for sig in diag.signals:
        val = values.get(sig)
        if val is not None:
            parts.append(f"{sig} = {val:g}")
    if not parts:
        return "violated: " + diag.formula_desc
    return ", ".join(parts) + " (formula: " + diag.formula_desc + ")"

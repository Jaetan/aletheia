"""Formula enrichment helpers — formatting, signal collection, diagnostics.

Module-level functions, testable without an AletheiaClient instance.
"""

from __future__ import annotations

from typing import cast

from ..protocols import LTLFormula
from ._types import PropertyDiagnostic


def _format_predicate(pred: dict[str, object]) -> str:  # pylint: disable=too-many-return-statements
    """Format a predicate dict as a human-readable string."""
    kind = pred.get("predicate")
    signal = str(pred.get("signal", ""))
    if kind == "equals":
        return f"{signal} = {pred['value']:g}"
    if kind == "lessThan":
        return f"{signal} < {pred['value']:g}"
    if kind == "greaterThan":
        return f"{signal} > {pred['value']:g}"
    if kind == "lessThanOrEqual":
        return f"{signal} <= {pred['value']:g}"
    if kind == "greaterThanOrEqual":
        return f"{signal} >= {pred['value']:g}"
    if kind == "between":
        return f"{pred['min']:g} <= {signal} <= {pred['max']:g}"
    if kind == "changedBy":
        return f"|\u0394{signal}| > {pred['delta']:g}"
    return "<unknown predicate>"


def _format_timebound(ms: int) -> str:
    """Format milliseconds as a human-readable time bound."""
    if ms % 1_000 == 0:
        return f"{ms // 1_000}s "
    return f"{ms}ms "


def _get_timebound(formula: dict[str, object]) -> str:
    """Extract and format the timebound from a metric formula."""
    tb = formula.get("timebound")
    if isinstance(tb, (int, float)) and not isinstance(tb, bool):
        return _format_timebound(int(tb))
    return ""


def format_formula(formula: dict[str, object]) -> str:  # pylint: disable=too-many-return-statements,too-many-branches
    """Format an LTL formula dict as a human-readable string."""
    op = formula.get("operator")
    if op == "atomic":
        return _format_predicate(cast(dict[str, object], formula["predicate"]))
    if op == "not":
        return "not(" + format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "and":
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " and "
                + format_formula(cast(dict[str, object], formula["right"])))
    if op == "or":
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " or "
                + format_formula(cast(dict[str, object], formula["right"])))
    if op == "next":
        return "next(" + format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "always":
        inner = cast(dict[str, object], formula["formula"])
        # Detect Never pattern: always(not(atomic(p)))
        if inner.get("operator") == "not":
            inner_not = cast(dict[str, object], inner["formula"])
            if inner_not.get("operator") == "atomic":
                return "never " + _format_predicate(cast(dict[str, object], inner_not["predicate"]))
        return "always(" + format_formula(inner) + ")"
    if op == "eventually":
        return "eventually(" + format_formula(cast(dict[str, object], formula["formula"])) + ")"
    if op == "until":
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " until "
                + format_formula(cast(dict[str, object], formula["right"])))
    if op == "release":
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " release "
                + format_formula(cast(dict[str, object], formula["right"])))
    if op == "metricAlways":
        tb = _get_timebound(formula)
        return ("always within " + tb + "("
                + format_formula(cast(dict[str, object], formula["formula"])) + ")")
    if op == "metricEventually":
        tb = _get_timebound(formula)
        return ("eventually within " + tb + "("
                + format_formula(cast(dict[str, object], formula["formula"])) + ")")
    if op == "metricUntil":
        tb = _get_timebound(formula)
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " until within " + tb + " "
                + format_formula(cast(dict[str, object], formula["right"])))
    if op == "metricRelease":
        tb = _get_timebound(formula)
        return (format_formula(cast(dict[str, object], formula["left"]))
                + " release within " + tb + " "
                + format_formula(cast(dict[str, object], formula["right"])))
    return "<unknown>"


def collect_signals(formula: dict[str, object]) -> list[str]:
    """Collect all signal names from a formula, deduplicated, in order."""
    signals: list[str] = []
    seen: set[str] = set()
    _collect_signals_into(formula, signals, seen)
    return signals


def _collect_signals_into(
    formula: dict[str, object], signals: list[str], seen: set[str],
) -> None:
    """Walk a formula collecting signal names."""
    op = formula.get("operator")
    if op == "atomic":
        pred = cast(dict[str, object], formula["predicate"])
        name = str(pred.get("signal", ""))
        if name and name not in seen:
            seen.add(name)
            signals.append(name)
    elif op in ("not", "next", "always", "eventually", "metricAlways", "metricEventually"):
        _collect_signals_into(cast(dict[str, object], formula["formula"]), signals, seen)
    elif op in ("and", "or", "until", "release", "metricUntil", "metricRelease"):
        _collect_signals_into(cast(dict[str, object], formula["left"]), signals, seen)
        _collect_signals_into(cast(dict[str, object], formula["right"]), signals, seen)


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

"""Formula enrichment helpers — formatting, signal collection, diagnostics.

Module-level functions, testable without an AletheiaClient instance.
"""

from collections.abc import Callable
from fractions import Fraction
from typing import cast

from ..protocols import LTLFormula
from ._types import PropertyDiagnostic, ValidationError

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

    Raises ValidationError if nesting exceeds _MAX_FORMULA_DEPTH.
    """
    if depth > _MAX_FORMULA_DEPTH:
        raise ValidationError(
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


def _coerce_to_float(v: object) -> float:
    """Best-effort numeric \u2192 float conversion for the pretty-printer.

    Predicate values now flow as :class:`Fraction` per the DecRat universal
    principle (cluster 17 / PY-D-19.1); the pretty-printer's role is only
    human-readable display, so converting through float is fine here.
    """
    if isinstance(v, (int, float, Fraction)):
        return float(v)
    return 0.0


def _format_rational(v: object) -> str:
    """Render a predicate value: terminating decimal via :g, else reduced N/D.

    Fraction values whose reduced denominator does not divide a power of 10
    (e.g. 1/3, 2/7) are rendered as literal "N/D" instead of being truncated
    by float formatting.  int and float inputs always render via :g.
    """
    if not isinstance(v, Fraction):
        return f"{_coerce_to_float(v):g}"
    n, d = v.numerator, v.denominator
    test = d
    while test % 2 == 0:
        test //= 2
    while test % 5 == 0:
        test //= 5
    if test == 1:
        return f"{float(v):g}"
    return f"{n}/{d}"


def _format_predicate(pred: dict[str, object]) -> str:
    """Format a predicate dict as a human-readable string."""
    kind = pred.get("predicate")
    signal = str(pred.get("signal", ""))
    op = _COMPARISON_OPS.get(str(kind))
    if op is not None:
        return f"{signal} {op} {_format_rational(pred.get('value', 0))}"
    if kind == "between":
        lo = _format_rational(pred.get("min", 0))
        hi = _format_rational(pred.get("max", 0))
        return f"{lo} <= {signal} <= {hi}"
    if kind == "changedBy":
        delta = pred.get("delta", 0)
        if _coerce_to_float(delta) >= 0:
            return f"\u0394{signal} >= {_format_rational(delta)}"
        return f"\u0394{signal} <= {_format_rational(delta)}"
    if kind == "stableWithin":
        return f"|\u0394{signal}| <= {_format_rational(pred.get('tolerance', 0))}"
    return "<unknown predicate>"


def _format_timebound(us: int) -> str:
    """Format microseconds as a human-readable time bound."""
    if us % 1_000_000 == 0:
        return f"{us // 1_000_000}s "
    if us % 1_000 == 0:
        return f"{us // 1_000}ms "
    return f"{us}\u03bcs "


def _get_timebound(formula: dict[str, object]) -> str:
    """Extract and format the timebound from a metric formula."""
    tb = formula.get("timebound")
    if isinstance(tb, (int, float)) and not isinstance(tb, bool):
        return _format_timebound(int(tb))
    return ""


def format_formula(  # pylint: disable=too-many-return-statements,too-many-branches
    formula: dict[str, object], depth: int = 0,
    *, _parenthesize_binary: bool = False,
) -> str:
    """Format an LTL formula dict as a human-readable string.

    Raises ValidationError if nesting exceeds _MAX_FORMULA_DEPTH.
    """
    if depth > _MAX_FORMULA_DEPTH:
        raise ValidationError(
            f"Formula nesting depth exceeds {_MAX_FORMULA_DEPTH}"
        )
    inner = _format_formula_inner(formula, depth, parenthesize_binary=_parenthesize_binary)
    return inner


def _format_formula_inner(  # pylint: disable=too-many-return-statements,too-many-branches
    formula: dict[str, object], depth: int,
    *, parenthesize_binary: bool,
) -> str:
    """Inner formatter with parenthesization for binary operators."""
    if depth > _MAX_FORMULA_DEPTH:
        raise ValidationError(
            f"Formula nesting depth exceeds {_MAX_FORMULA_DEPTH}"
        )
    recur = _format_formula_inner
    op = formula.get("operator")
    if op == "atomic":
        return _format_predicate(cast(dict[str, object], formula["predicate"]))
    if op == "not":
        return "not(" + recur(cast(dict[str, object], formula["formula"]),
                              depth + 1, parenthesize_binary=False) + ")"
    if op == "and":
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " and "
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    if op == "or":
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " or "
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    if op == "next":
        inner = cast(dict[str, object], formula["formula"])
        return "next(" + recur(inner, depth + 1, parenthesize_binary=False) + ")"
    if op == "always":
        inner = cast(dict[str, object], formula["formula"])
        # Detect Never pattern: always(not(atomic(p)))
        if inner.get("operator") == "not":
            inner_not = cast(dict[str, object], inner["formula"])
            if inner_not.get("operator") == "atomic":
                return "never " + _format_predicate(cast(dict[str, object], inner_not["predicate"]))
        return "always(" + recur(inner, depth + 1, parenthesize_binary=False) + ")"
    if op == "eventually":
        inner = cast(dict[str, object], formula["formula"])
        return "eventually(" + recur(inner, depth + 1, parenthesize_binary=False) + ")"
    if op == "until":
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " until "
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    if op == "release":
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " release "
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    if op == "metricAlways":
        tb = _get_timebound(formula)
        return ("always within " + tb + "("
                + recur(cast(dict[str, object], formula["formula"]),
                        depth + 1, parenthesize_binary=False) + ")")
    if op == "metricEventually":
        tb = _get_timebound(formula)
        return ("eventually within " + tb + "("
                + recur(cast(dict[str, object], formula["formula"]),
                        depth + 1, parenthesize_binary=False) + ")")
    if op == "metricUntil":
        tb = _get_timebound(formula)
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " until within " + tb
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    if op == "metricRelease":
        tb = _get_timebound(formula)
        s = (recur(cast(dict[str, object], formula["left"]),
                   depth + 1, parenthesize_binary=True)
             + " release within " + tb
             + recur(cast(dict[str, object], formula["right"]),
                     depth + 1, parenthesize_binary=True))
        return "(" + s + ")" if parenthesize_binary else s
    return "<unknown>"


def collect_signals(formula: dict[str, object]) -> list[str]:
    """Collect all signal names from a formula, deduplicated, in order.

    Raises ValidationError if nesting exceeds _MAX_FORMULA_DEPTH.
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
        signals=tuple(collect_signals(f)),
        formula_desc=format_formula(f),
    )


def format_enriched_reason(
    diag: PropertyDiagnostic, values: dict[str, Fraction | None],
    core_reason: str = "",
) -> str:
    """Build the enriched reason string.

    When ``core_reason`` is non-empty it is appended as ``[core: ...]``
    context, matching Go and C++ enrichment output.
    """
    parts: list[str] = []
    for sig in diag.signals:
        val = values.get(sig)
        if val is not None:
            parts.append(f"{sig} = {val:g}")
    if not parts:
        base = "violated: " + diag.formula_desc
    else:
        base = ", ".join(parts) + " (formula: " + diag.formula_desc + ")"
    if core_reason:
        return base + " [core: " + core_reason + "]"
    return base

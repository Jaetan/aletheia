# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Formula enrichment helpers — formatting, signal collection, diagnostics.

Module-level functions.  Rational rendering is delegated to the Agda
kernel via the FFI's ``aletheia_format_rational``; the FFI library is
registered eagerly by :class:`FFIBackend` and lazily loaded otherwise so
direct callers like ``format_formula(my_dict)`` keep working without an
explicit backend.
"""

from __future__ import annotations

import ctypes
import threading
from typing import TYPE_CHECKING

from aletheia._time_units import MICROSECONDS_PER_MILLISECOND, MICROSECONDS_PER_SECOND
from aletheia.client._ffi import configure_ffi_signatures, find_ffi_library
from aletheia.client._types import PropertyDiagnostic, ValidationError
from aletheia.limits import MAX_NESTING_DEPTH

if TYPE_CHECKING:
    from collections.abc import Callable
    from fractions import Fraction
    from typing import TypeGuard

    from aletheia.protocols import (
        AlwaysFormula,
        AndFormula,
        EqualsPredicate,
        EventuallyFormula,
        GreaterThanOrEqualPredicate,
        GreaterThanPredicate,
        LessThanOrEqualPredicate,
        LessThanPredicate,
        LTLFormula,
        MetricAlwaysFormula,
        MetricEventuallyFormula,
        MetricReleaseFormula,
        MetricUntilFormula,
        NextFormula,
        NotFormula,
        OrFormula,
        ReleaseFormula,
        SignalPredicate,
        UntilFormula,
        WeakNextFormula,
    )

    # Formatting-dispatch sub-unions of the LTL taxonomy (implementation
    # detail of this module — kept local rather than widening protocols.py's
    # public surface).  Each groups the formula/predicate TypedDicts that
    # share the structural shape a family handler depends on.
    _UnaryFormula = (
        NotFormula
        | NextFormula
        | WeakNextFormula
        | AlwaysFormula
        | EventuallyFormula
        | MetricAlwaysFormula
        | MetricEventuallyFormula
    )
    _BinaryFormula = (
        AndFormula
        | OrFormula
        | UntilFormula
        | ReleaseFormula
        | MetricUntilFormula
        | MetricReleaseFormula
    )
    # R0801 false positive: these five arms coincide with the first five of
    # ``aletheia.protocols.SignalPredicate``, but this alias is intentionally a
    # subset (no Between/ChangedBy/StableWithin) — it must stay narrower.
    # pylint: disable=duplicate-code
    _ComparisonPredicate = (
        EqualsPredicate
        | LessThanPredicate
        | GreaterThanPredicate
        | LessThanOrEqualPredicate
        | GreaterThanOrEqualPredicate
    )
    # pylint: enable=duplicate-code

# Depth cap mirrors the kernel SSOT (`Aletheia.Limits.max-nesting-depth`,
# exposed as `aletheia.limits.MAX_NESTING_DEPTH`): a deeper formula would
# pass this local check, serialize to JSON, then get rejected on the wire
# as `bound_kind_nesting_depth`.  Mirroring the kernel cap surfaces the
# rejection immediately as `ValidationError` instead of as a wire round-trip
# error.

_UNARY_OPS = frozenset(
    {
        "not",
        "next",
        "weakNext",
        "always",
        "eventually",
        "metricAlways",
        "metricEventually",
    }
)
_BINARY_OPS = frozenset(
    {
        "and",
        "or",
        "until",
        "release",
        "metricUntil",
        "metricRelease",
    }
)
_COMPARISON_OPS: dict[str, str] = {
    "equals": "=",
    "lessThan": "<",
    "greaterThan": ">",
    "lessThanOrEqual": "<=",
    "greaterThanOrEqual": ">=",
}


def _is_unary(formula: LTLFormula) -> TypeGuard[_UnaryFormula]:
    """Narrow *formula* to a unary operator (single ``formula`` child)."""
    return formula["operator"] in _UNARY_OPS


def _is_binary(formula: LTLFormula) -> TypeGuard[_BinaryFormula]:
    """Narrow *formula* to a binary operator (``left`` / ``right`` children)."""
    return formula["operator"] in _BINARY_OPS


def _is_comparison(pred: SignalPredicate) -> TypeGuard[_ComparisonPredicate]:
    """Narrow *pred* to a comparison predicate (single ``value`` field)."""
    return pred["predicate"] in _COMPARISON_OPS


def _walk_formula(
    formula: LTLFormula,
    on_atomic: Callable[[SignalPredicate], None],
    depth: int = 0,
) -> None:
    """Walk a formula tree, calling on_atomic for each atomic node.

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
    """
    if depth > MAX_NESTING_DEPTH:
        msg = f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
        raise ValidationError(msg)
    if formula["operator"] == "atomic":
        on_atomic(formula["predicate"])
    elif _is_unary(formula):
        _walk_formula(formula["formula"], on_atomic, depth + 1)
    elif _is_binary(formula):
        _walk_formula(formula["left"], on_atomic, depth + 1)
        _walk_formula(formula["right"], on_atomic, depth + 1)


# Module-level FFI library reference for the cross-binding-identical
# Rational renderer.  Registered eagerly by
# :meth:`aletheia.client._backend.FFIBackend.__init__` so production
# paths use the loaded backend's library.  When unset (e.g. tests
# calling ``format_formula`` directly without instantiating a client),
# :func:`_get_or_load_renderer_lib` lazily loads ``libaletheia-ffi.so``
# and initialises the GHC RTS on first call.
# A one-element cell behind a module constant: the binding is never rebound,
# so set_renderer_lib / _get_or_load_renderer_lib mutate the cell contents
# rather than declaring ``global`` (which would rebind a lowercase module var).
_RENDERER_LIB: list[ctypes.CDLL | None] = [None]
_RENDERER_LOCK = threading.Lock()


def set_renderer_lib(lib: ctypes.CDLL) -> None:
    """Register the FFI library used for Rational rendering.

    Called by :meth:`FFIBackend.__init__` after configuring ctypes
    signatures.  Subsequent calls overwrite the registration; this is
    safe because the underlying ``.so`` is loaded once per process and
    every backend instance holds a reference to the same library.
    """
    _RENDERER_LIB[0] = lib


def _get_or_load_renderer_lib() -> ctypes.CDLL:
    """Return the registered FFI library, lazily loading it if needed.

    Production callers go through :class:`FFIBackend`, which registers
    eagerly via :func:`set_renderer_lib`.  Direct callers of
    :func:`format_formula` / :func:`build_diagnostic` (typically tests
    or scripts) trigger the lazy load on first Rational render.
    """
    # Thread-safe lazy-load.  Mirrors Go's sync.Once and C++'s
    # std::call_once — without the lock, two concurrent first-callers
    # both see _renderer_lib is None, both dlopen the .so, last-write wins.
    # GHC RTS init is idempotent per the renderer.cpp comment, so the race
    # is benign in practice; the lock is defensive thread-safety hygiene.
    with _RENDERER_LOCK:
        lib = _RENDERER_LIB[0]
        if lib is None:
            path = find_ffi_library()
            lib = ctypes.CDLL(str(path))
            # ``hs_init`` initialises the GHC RTS; it is idempotent across
            # multiple ``CDLL`` handles to the same ``.so`` (the runtime
            # tracks initialisation state internally), so re-calling here
            # when an FFIBackend later instantiates does no harm.
            lib.hs_init(None, None)
            configure_ffi_signatures(lib)
            _RENDERER_LIB[0] = lib
    return lib


def _format_rational(value: Fraction) -> str:
    """Render an exact rational via the Agda kernel renderer.

    Delegates to :func:`Aletheia.DBC.RationalRenderer.formatRational` in
    the Agda kernel (the ``aletheia_format_rational`` FFI export in
    ``haskell-shim/src/AletheiaFFI.hs``).  Cross-binding parity is an
    architectural invariant: the same Agda function backs the Python, Go,
    and C++ enrichment paths, so a given rational renders byte-identically
    everywhere.  Predicate values are exact :class:`Fraction` per the
    DecRat universal principle, so the renderer only ever sees ℚ.
    """
    lib = _get_or_load_renderer_lib()
    raw = lib.aletheia_format_rational(
        ctypes.c_int64(value.numerator),
        ctypes.c_int64(value.denominator),
    )
    if not raw:
        # Defensive: the Agda function always returns a non-null CString
        # (the ``denom = 0`` branch returns the literal ``"0"``).  Reach
        # here only on a catastrophic Haskell-side allocation failure.
        return "0"
    try:
        return ctypes.cast(raw, ctypes.c_char_p).value.decode()  # type: ignore[union-attr]
    finally:
        lib.aletheia_free_str(raw)


def _format_predicate(pred: SignalPredicate) -> str:
    """Format a signal predicate as a human-readable string."""
    if _is_comparison(pred):
        op = _COMPARISON_OPS[pred["predicate"]]
        return f"{pred['signal']} {op} {_format_rational(pred['value'])}"
    if pred["predicate"] == "between":
        lo = _format_rational(pred["min"])
        hi = _format_rational(pred["max"])
        return f"{lo} <= {pred['signal']} <= {hi}"
    if pred["predicate"] == "changedBy":
        delta = pred["delta"]
        sign = ">=" if delta >= 0 else "<="
        return f"Δ{pred['signal']} {sign} {_format_rational(delta)}"
    if pred["predicate"] == "stableWithin":
        return f"|Δ{pred['signal']}| <= {_format_rational(pred['tolerance'])}"
    return "<unknown predicate>"


def _format_timebound(us: int) -> str:
    """Format microseconds as a human-readable time bound."""
    if us % MICROSECONDS_PER_SECOND == 0:
        return f"{us // MICROSECONDS_PER_SECOND}s "
    if us % MICROSECONDS_PER_MILLISECOND == 0:
        return f"{us // MICROSECONDS_PER_MILLISECOND}ms "
    return f"{us}μs "


# Token tables for the formula pretty-printer — one handler per operator
# family (see _format_unary / _format_binary); the operator-specific text
# lives here so the dispatch in _format_formula_inner stays flat.
_UNARY_WRAP: dict[str, str] = {
    "not": "not(",
    "next": "next(",
    "weakNext": "weak_next(",
    "eventually": "eventually(",
    "always": "always(",
}
_METRIC_UNARY_PREFIX: dict[str, str] = {
    "metricAlways": "always within ",
    "metricEventually": "eventually within ",
}
_BINARY_INFIX: dict[str, str] = {
    "and": " and ",
    "or": " or ",
    "until": " until ",
    "release": " release ",
}
_METRIC_BINARY_INFIX: dict[str, str] = {
    "metricUntil": " until within ",
    "metricRelease": " release within ",
}


def format_formula(
    formula: LTLFormula,
    depth: int = 0,
    *,
    _parenthesize_binary: bool = False,
) -> str:
    """Format an LTL formula as a human-readable string.

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
    """
    if depth > MAX_NESTING_DEPTH:
        msg = f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
        raise ValidationError(msg)
    return _format_formula_inner(formula, depth, parenthesize_binary=_parenthesize_binary)


def _format_never(inner: LTLFormula) -> str | None:
    """Render ``always(not(atomic(p)))`` as ``never <p>``; else ``None``.

    The ``never`` shorthand is reserved for the safety pattern where an
    atomic predicate must hold globally; any other ``always`` body falls
    through to the generic ``always(...)`` rendering.
    """
    if inner["operator"] != "not":
        return None
    return _never_if_atomic(inner["formula"])


def _never_if_atomic(negated: LTLFormula) -> str | None:
    """Render ``never <p>`` when *negated* is ``atomic(p)``, else ``None``.

    Split out so the ``atomic`` discriminator narrows a fresh *parameter*.
    Narrowing the inline ``inner["formula"]`` item access instead leaves an
    ``Unknown`` arm — item access on the recursive ``LTLFormula`` forward-ref
    bottoms out in ``Unknown``, which discriminator narrowing on
    ``["operator"]`` cannot subtract; a parameter-typed ``LTLFormula`` narrows
    cleanly (cf. ``_format_formula_inner`` / ``_walk_formula``).
    """
    if negated["operator"] != "atomic":
        return None
    return "never " + _format_predicate(negated["predicate"])


def _format_unary(formula: _UnaryFormula, depth: int) -> str:
    """Render a unary operator (not/next/eventually/always/metric-*)."""
    op = formula["operator"]
    inner = formula["formula"]
    if op == "always":
        never = _format_never(inner)
        if never is not None:
            return never
    body = _format_formula_inner(inner, depth + 1, parenthesize_binary=False)
    if formula["operator"] == "metricAlways" or formula["operator"] == "metricEventually":
        prefix = _METRIC_UNARY_PREFIX[formula["operator"]]
        return prefix + _format_timebound(formula["timebound"]) + "(" + body + ")"
    return _UNARY_WRAP[op] + body + ")"


def _format_binary(
    formula: _BinaryFormula,
    depth: int,
    *,
    parenthesize_binary: bool,
) -> str:
    """Render a binary operator (and/or/until/release/metric-*)."""
    left = _format_formula_inner(formula["left"], depth + 1, parenthesize_binary=True)
    right = _format_formula_inner(formula["right"], depth + 1, parenthesize_binary=True)
    op = formula["operator"]
    if formula["operator"] == "metricUntil" or formula["operator"] == "metricRelease":
        infix = _METRIC_BINARY_INFIX[formula["operator"]]
        s = left + infix + _format_timebound(formula["timebound"]) + right
    else:
        s = left + _BINARY_INFIX[op] + right
    return "(" + s + ")" if parenthesize_binary else s


def _format_formula_inner(
    formula: LTLFormula,
    depth: int,
    *,
    parenthesize_binary: bool,
) -> str:
    """Inner formatter with parenthesization for binary operators."""
    if depth > MAX_NESTING_DEPTH:
        msg = f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
        raise ValidationError(msg)
    if formula["operator"] == "atomic":
        return _format_predicate(formula["predicate"])
    if _is_unary(formula):
        return _format_unary(formula, depth)
    if _is_binary(formula):
        return _format_binary(formula, depth, parenthesize_binary=parenthesize_binary)
    return "<unknown>"


def collect_signals(formula: LTLFormula) -> list[str]:
    """Collect all signal names from a formula, deduplicated, in order.

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
    """
    signals: list[str] = []
    seen: set[str] = set()

    def on_atomic(pred: SignalPredicate) -> None:
        name = pred["signal"]
        if name and name not in seen:
            seen.add(name)
            signals.append(name)

    _walk_formula(formula, on_atomic)
    return signals


def build_diagnostic(formula: LTLFormula) -> PropertyDiagnostic:
    """Build a PropertyDiagnostic from a formula. Always succeeds."""
    return PropertyDiagnostic(
        signals=tuple(collect_signals(formula)),
        formula_desc=format_formula(formula),
    )


def format_enriched_reason(
    diag: PropertyDiagnostic,
    values: dict[str, Fraction | None],
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

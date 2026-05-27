"""Formula enrichment helpers — formatting, signal collection, diagnostics.

Module-level functions.  Rational rendering is delegated to the Agda
kernel via the FFI's ``aletheia_format_rational`` (R20 cluster Y stage 2);
the FFI library is registered eagerly by :class:`FFIBackend` and lazily
loaded otherwise so direct callers like ``format_formula(my_dict)`` keep
working without an explicit backend.
"""

from collections.abc import Callable
from fractions import Fraction
from typing import cast
import ctypes
import threading

from aletheia._time_units import MICROSECONDS_PER_MILLISECOND, MICROSECONDS_PER_SECOND
from aletheia.limits import MAX_NESTING_DEPTH
from aletheia.protocols import LTLFormula
from aletheia.client._types import PropertyDiagnostic, ValidationError

# Depth cap mirrors the kernel SSOT (`Aletheia.Limits.max-nesting-depth`,
# exposed as `aletheia.limits.MAX_NESTING_DEPTH`): a deeper formula would
# pass this local check, serialize to JSON, then get rejected on the wire
# as `bound_kind_nesting_depth`.  Mirroring the kernel cap surfaces the
# rejection immediately as `ValidationError` instead of as a wire round-trip
# error.  R21 PY-A-2.3 / AGDA-D-17.1 cross-binding SSOT fix.

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

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
    """
    if depth > MAX_NESTING_DEPTH:
        raise ValidationError(
            f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
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


# Module-level FFI library reference for the cross-binding-identical
# Rational renderer (R20 cluster Y stage 2).  Registered eagerly by
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
    # Thread-safe lazy-load (R23 PY-D-22.6).  Mirrors Go's sync.Once and
    # C++'s std::call_once — without the lock, two concurrent first-callers
    # both see _renderer_lib is None, both dlopen the .so, last-write wins.
    # GHC RTS init is idempotent per the renderer.cpp comment, so the race
    # is benign in practice; the lock is defensive thread-safety hygiene.
    with _RENDERER_LOCK:
        lib = _RENDERER_LIB[0]
        if lib is None:
            # Local import avoids a runtime circular dependency: ``_ffi``
            # has no upward dependencies, but importing at module load
            # would chain through ``configure_ffi_signatures`` which
            # references ctypes types that the renderer doesn't need
            # unless it actually has to lazy-load.
            from aletheia.client._ffi import (  # pylint: disable=import-outside-toplevel
                configure_ffi_signatures,
                find_ffi_library,
            )
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


def _format_rational(v: object) -> str:
    """Render a predicate value via the Agda kernel renderer.

    Delegates to :func:`Aletheia.DBC.RationalRenderer.formatRational`
    in the Agda kernel (see ``aletheia_format_rational`` FFI export
    in ``haskell-shim/src/AletheiaFFI.hs``).  Cross-binding parity is
    an architectural invariant: the same Agda function is called by
    Python, Go, and C++ enrichment paths, so the same Rational value
    renders to byte-identical output everywhere.

    Accepted input shapes (every shape coerces to ``Fraction`` then
    flows through the FFI — no local ``:g``-style fallback):

    * ``Fraction`` — passed straight through (DSL path via
      ``to_predicate_fraction``).
    * ``int`` / ``float`` — raw-JSON-dict callers (e.g. test fixtures
      constructing ``{"value": 0}`` directly without the DSL); coerced
      via ``Fraction(v)`` (exact for ``int``; IEEE-754-exact for
      ``float``).
    * ``dict`` with ``{"numerator", "denominator"}`` — wire-rational
      shape; coerced via ``Fraction(num, den)``.

    Any other shape is a contract violation and raises ``ValidationError``.
    """
    if isinstance(v, Fraction):
        frac = v
    elif isinstance(v, int) and not isinstance(v, bool):
        frac = Fraction(v, 1)
    elif isinstance(v, float):
        frac = Fraction(v)
    elif isinstance(v, dict):
        d = cast("dict[str, object]", v)
        num = d.get("numerator")
        den = d.get("denominator")
        if not (isinstance(num, int) and isinstance(den, int)
                and not isinstance(num, bool) and not isinstance(den, bool)):
            msg = (
                f"_format_rational rational dict requires int numerator/denominator; "
                f"got numerator={type(num).__name__} denominator={type(den).__name__}"
            )
            raise ValidationError(msg)
        if den == 0:
            raise ValidationError("_format_rational rational dict denominator must be non-zero")
        frac = Fraction(num, den)
    else:
        msg = (
            f"_format_rational expected Fraction / int / float / rational dict; "
            f"got {type(v).__name__}"
        )
        raise ValidationError(msg)
    lib = _get_or_load_renderer_lib()
    raw = lib.aletheia_format_rational(
        ctypes.c_int64(frac.numerator),
        ctypes.c_int64(frac.denominator),
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
    if us % MICROSECONDS_PER_SECOND == 0:
        return f"{us // MICROSECONDS_PER_SECOND}s "
    if us % MICROSECONDS_PER_MILLISECOND == 0:
        return f"{us // MICROSECONDS_PER_MILLISECOND}ms "
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

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
    """
    if depth > MAX_NESTING_DEPTH:
        raise ValidationError(
            f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
        )
    inner = _format_formula_inner(formula, depth, parenthesize_binary=_parenthesize_binary)
    return inner


def _format_formula_inner(  # pylint: disable=too-many-return-statements,too-many-branches
    formula: dict[str, object], depth: int,
    *, parenthesize_binary: bool,
) -> str:
    """Inner formatter with parenthesization for binary operators."""
    if depth > MAX_NESTING_DEPTH:
        raise ValidationError(
            f"Formula nesting depth exceeds {MAX_NESTING_DEPTH}"
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

    Raises ValidationError if nesting exceeds MAX_NESTING_DEPTH.
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

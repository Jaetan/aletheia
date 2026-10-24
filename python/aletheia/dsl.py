# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Python DSL for LTL properties over CAN signals.

Provides fluent interface for expressing temporal properties:
```python
Signal("VehicleSpeed").less_than(220).always()
# Every brake press is followed within 100 ms by a speed decrease
brake_pressed = Signal("BrakePressure").greater_than(0)
speed_decreases = Signal("VehicleSpeed").changed_by(-10)
brake_pressed.implies(speed_decreases.within(100)).always()
```

Usage with AletheiaClient:
```python
from aletheia import AletheiaClient, Signal

property = Signal("VehicleSpeed").less_than(220).always()
client.set_properties([property.to_dict()])
```

Output format matches the Agda JSON schema:
    - All formulas use "operator" key (not "type")
    - Predicates use {"operator": "atomic", "predicate": {...}} format
    - Time bounds use "timebound" key (not "time_ms")
    - "never" desugars to always(not(...))
    - "implies" desugars to or(not(antecedent), consequent)
"""

from __future__ import annotations

from fractions import Fraction

from aletheia._dsl_patterns import eventually_always, infinitely_often, never
from aletheia._dsl_property import Property, implies_formula, require_non_negative_time_ms
from aletheia._time_units import MICROSECONDS_PER_MILLISECOND
from aletheia.client._helpers.rational import to_exact_fraction
from aletheia.client._types import ValidationError
from aletheia.types import (
    AlwaysFormula,
    AndFormula,
    AtomicFormula,
    EventuallyFormula,
    LTLFormula,
    MetricAlwaysFormula,
    MetricEventuallyFormula,
    NextFormula,
    NotFormula,
    OrFormula,
    PredicateType,
    SignalPredicate,
    WeakNextFormula,
)

# Predicate value inputs are exact: an integer or a :class:`~fractions.Fraction`.
# The float principle — no float ever crosses the API: a decimal is an
# exact rational, so callers pass ``Fraction(n, d)`` (or :func:`aletheia.from_decimal`
# for a decimal string) rather than a lossy ``float``.  The Agda kernel and the
# Go / C++ / Rust bindings all accept the canonical rational dict on the wire.
type _RationalInput = int | Fraction


def to_predicate_fraction(value: _RationalInput) -> Fraction:
    """Convert an exact numeric predicate input to a :class:`~fractions.Fraction`.

    The DSL-facing entry to the float-principle validator
    :func:`~aletheia.client._helpers.rational.to_exact_fraction` — the single
    source of truth shared with the client's signal-value path. An ``int`` or a
    ``Fraction`` flows through exactly, while a ``float`` (lossy: ``Fraction(0.1)``
    is not ``1/10``) or a ``bool`` (``Fraction(True)`` would silently become
    ``1``) is rejected; pass a ``Fraction`` or :func:`aletheia.from_decimal` for
    an exact decimal.
    """
    return to_exact_fraction(value)


def _atomic(predicate: SignalPredicate) -> AtomicFormula:
    """Wrap a signal predicate in an atomic formula."""
    return {"operator": "atomic", "predicate": predicate}


class Signal:
    """Reference to a CAN signal for use in temporal properties.

    Adding a new signal predicate is a **three-point coupling**. The
    following sites must all change together, and the Agda layer is the
    source of truth:

      1. ``src/Aletheia/LTL/SignalPredicate/Types.agda`` — add the
         constructor to the ``SignalPredicate`` / ``ValuePredicate`` /
         ``DeltaPredicate`` ADTs.  Then extend
         ``src/Aletheia/LTL/JSON/Format.agda``'s
         ``formatSignalPredicateFields`` (and its parser counterpart) so
         the JSON wire format recognises the new tag.
      2. ``python/aletheia/types.py`` — add the matching member to
         ``PredicateType`` (Python mirror of the wire-format tag).
      3. This module — expose it as a method on ``Signal`` (or ``Predicate``)
         that emits ``{'predicate': PredicateType.NEW_KIND.value, ...}``.

    A registry / plugin design would decouple points (2) and (3) but would
    not help point (1) — CAN signal predicates are fixed by the Agda spec,
    so the closed-domain coupling is intentional. Don't refactor to a
    registry without first changing the Agda surface.
    """

    # DEFERRED: Public __init__ methods on Signal/Property/Predicate allow
    #   positional args (`Signal("Speed")`); kwargs-only (`Signal(name="Speed")`)
    #   would prevent positional-confusion bugs as the API grows.
    # Why: Migration breaks every doc-fence and test (`Signal("X")` →
    #   `Signal(name="X")`); cross-binding parity already strong-typed via
    #   Go/C++ struct construction.
    # Revisit when: A signature gains an optional positional that could collide
    #   with the existing arg (e.g. `Signal(name: str, unit: str = "")` —
    #   `Signal("Speed", "km/h")` would silently mis-interpret).
    def __init__(self, name: str) -> None:
        """Create a signal reference.

        Args:
            name: Signal name (must exist in DBC)

        """
        self.name: str = name

    def equals(self, value: _RationalInput) -> Predicate:
        """Signal equals a specific value.

        Args:
            value: Expected signal value (int or Fraction; coerced to exact Fraction)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        Signal("Gear").equals(0)  # Gear is in park
        ```

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.EQUALS.value,
                "signal": self.name,
                "value": to_predicate_fraction(value),
            }
        )
        return Predicate(formula)

    def less_than(self, value: _RationalInput) -> Predicate:
        """Signal is less than a value.

        Args:
            value: Upper bound (exclusive); int or Fraction (coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        Signal("Speed").less_than(220)  # Speed below 220 km/h
        ```

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.LESS_THAN.value,
                "signal": self.name,
                "value": to_predicate_fraction(value),
            }
        )
        return Predicate(formula)

    def greater_than(self, value: _RationalInput) -> Predicate:
        """Signal is greater than a value.

        Args:
            value: Lower bound (exclusive); int or Fraction (coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        Signal("Speed").greater_than(5)  # Vehicle moving
        ```

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.GREATER_THAN.value,
                "signal": self.name,
                "value": to_predicate_fraction(value),
            }
        )
        return Predicate(formula)

    def less_than_or_equal(self, value: _RationalInput) -> Predicate:
        """Signal is less than or equal to a value.

        Args:
            value: Upper bound (inclusive); int or Fraction (coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.LESS_THAN_OR_EQUAL.value,
                "signal": self.name,
                "value": to_predicate_fraction(value),
            }
        )
        return Predicate(formula)

    def greater_than_or_equal(self, value: _RationalInput) -> Predicate:
        """Signal is greater than or equal to a value.

        Args:
            value: Lower bound (inclusive); int or Fraction (coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.GREATER_THAN_OR_EQUAL.value,
                "signal": self.name,
                "value": to_predicate_fraction(value),
            }
        )
        return Predicate(formula)

    def between(self, min_val: _RationalInput, max_val: _RationalInput) -> Predicate:
        """Signal is within a range (inclusive).

        Args:
            min_val: Minimum value (inclusive)
            max_val: Maximum value (inclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        from aletheia import AletheiaClient, from_decimal

        # The kernel reads every decimal, so a client is open first
        with AletheiaClient():
            Signal("BatteryVoltage").between(from_decimal("11.5"), from_decimal("14.5"))
        ```

        """
        lo = to_predicate_fraction(min_val)
        hi = to_predicate_fraction(max_val)
        if lo > hi:
            msg = f"min_val ({min_val}) must be <= max_val ({max_val})"
            raise ValidationError(msg)
        formula: AtomicFormula = _atomic(
            {"predicate": PredicateType.BETWEEN.value, "signal": self.name, "min": lo, "max": hi}
        )
        return Predicate(formula)

    def changed_by(self, delta: _RationalInput) -> Predicate:
        """Signal changed in a specific direction.

        Positive delta: curr - prev >= delta (increased by at least delta)
        Negative delta: curr - prev <= delta (decreased by at least |delta|)

        Args:
            delta: Signed change threshold (int or Fraction; coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        Signal("Speed").changed_by(-10)  # Speed decreased by 10+
        ```

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.CHANGED_BY.value,
                "signal": self.name,
                "delta": to_predicate_fraction(delta),
            }
        )
        return Predicate(formula)

    def stable_within(self, tolerance: _RationalInput) -> Predicate:
        """Signal value stayed within tolerance of previous value.

        Checks |signal_now - signal_prev| <= tolerance

        Args:
            tolerance: Maximum allowed absolute change (int or Fraction; coerced to Fraction)

        Returns:
            Predicate that can be used in temporal operators

        Example:
        ```python
        Signal("Temp").stable_within(2)  # Temperature stable within +/-2
        ```

        """
        formula: AtomicFormula = _atomic(
            {
                "predicate": PredicateType.STABLE_WITHIN.value,
                "signal": self.name,
                "tolerance": to_predicate_fraction(tolerance),
            }
        )
        return Predicate(formula)


class Predicate:
    """Atomic predicate over CAN signals.

    Created by Signal comparison methods. Can be composed into
    temporal properties using temporal operators.

    **Recommended temporal operators** (robust on CAN networks):
        ``always``, ``eventually``, ``never``, ``within``, ``for_at_least``

    **Boolean / logical combinators**:
        ``and_``, ``or_``, ``not_``, ``implies``

    **Discouraged** (see the "Discouraged in CAN analysis" section at the
    bottom of this class): ``next`` — use ``within(time_ms)`` instead. Left
    in the API for completeness with standard LTLf; CAN timing jitter makes
    frame-exact semantics unreliable.
    """

    def __init__(self, formula: LTLFormula) -> None:
        """Construct a Predicate wrapping a finished LTLFormula dict.

        Not part of the public API — call ``Signal(name).equals(v)``
        (or any other comparison method) instead.  Direct callers must
        supply a fully-formed LTLFormula matching the Agda JSON schema;
        the stored ``_formula`` is assumed to be schema-valid and is
        passed verbatim to the kernel via ``to_formula()``.
        """
        self._formula: LTLFormula = formula

    def to_formula(self) -> LTLFormula:
        """Convert to LTL formula for use in composition.

        Returns:
            LTL formula representation

        """
        return self._formula

    def always(self) -> Property:
        """Property must always hold (globally).

        Returns:
            Temporal property (LTL formula)

        Example:
        ```python
        Signal("Speed").less_than(220).always()
        ```

        """
        formula: AlwaysFormula = {"operator": "always", "formula": self._formula}
        return Property(formula)

    def eventually(self) -> Property:
        """Property must eventually hold (sometime in future).

        Returns:
            Temporal property (LTL formula)

        Example:
        ```python
        Signal("DoorClosed").equals(1).eventually()
        ```

        """
        formula: EventuallyFormula = {"operator": "eventually", "formula": self._formula}
        return Property(formula)

    def never(self) -> Property:
        """Property must never hold (always negated).

        Desugars to always(not(formula)) for Agda compatibility.

        Returns:
            Temporal property (LTL formula)

        Example:
        ```python
        Signal("ErrorCode").equals(0xFF).never()
        ```

        """
        formula: AlwaysFormula = {
            "operator": "always",
            "formula": {"operator": "not", "formula": self._formula},
        }
        return Property(formula)

    def within(self, time_ms: int) -> Property:
        """Property must hold within time_ms milliseconds.

        Uses Metric Eventually (time-bounded eventually operator).
        More robust than Next for CAN networks with jitter.

        Args:
            time_ms: Time bound in milliseconds (must be >= 0)

        Returns:
            Bounded temporal property

        Raises:
            ValidationError: ``time_ms`` is negative.

        Example:
        ```python
        # Every brake press is followed within 100 ms by a speed decrease
        brake_pressed = Signal("BrakePressure").greater_than(0)
        speed_decreases = Signal("VehicleSpeed").changed_by(-10)
        brake_pressed.implies(speed_decreases.within(100)).always()
        ```

        """
        require_non_negative_time_ms(time_ms)
        formula: MetricEventuallyFormula = {
            "operator": "metricEventually",
            "timebound": time_ms * MICROSECONDS_PER_MILLISECOND,
            "formula": self._formula,
        }
        return Property(formula)

    def for_at_least(self, time_ms: int) -> Property:
        """Property must hold continuously for at least time_ms milliseconds.

        Uses Metric Always (time-bounded always operator).
        Useful for debouncing and stability checks.

        Args:
            time_ms: Duration in milliseconds (must be >= 0)

        Returns:
            Bounded temporal property

        Raises:
            ValidationError: ``time_ms`` is negative.

        Example:
        ```python
        Signal("DoorClosed").equals(1).for_at_least(50)  # Debounced
        ```

        """
        require_non_negative_time_ms(time_ms)
        formula: MetricAlwaysFormula = {
            "operator": "metricAlways",
            "timebound": time_ms * MICROSECONDS_PER_MILLISECOND,
            "formula": self._formula,
        }
        return Property(formula)

    def and_(self, other: Predicate) -> Predicate:
        """Logical AND of two predicates.

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
        ```python
        left_ok = Signal("LeftDoor").equals(0)
        right_ok = Signal("RightDoor").equals(0)
        left_ok.and_(right_ok)
        ```

        """
        formula: AndFormula = {
            "operator": "and",
            "left": self._formula,
            "right": other.to_formula(),
        }
        return Predicate(formula)

    def or_(self, other: Predicate) -> Predicate:
        """Logical OR of two predicates.

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
        ```python
        error1 = Signal("ErrorCode").equals(1)
        error2 = Signal("ErrorCode").equals(2)
        error1.or_(error2)
        ```

        """
        formula: OrFormula = {"operator": "or", "left": self._formula, "right": other.to_formula()}
        return Predicate(formula)

    def not_(self) -> Predicate:
        """Logical NOT of predicate.

        Returns:
            Negated predicate

        Example:
        ```python
        Signal("Enabled").equals(1).not_()
        ```

        """
        formula: NotFormula = {"operator": "not", "formula": self._formula}
        return Predicate(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other.

        Desugars to or(not(self), other) for Agda compatibility.

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
        ```python
        # Every brake press is followed within 100 ms by a speed decrease
        brake_pressed = Signal("BrakePressure").greater_than(0)
        speed_decreases = Signal("VehicleSpeed").changed_by(-10)
        brake_pressed.implies(speed_decreases.within(100)).always()
        ```

        """
        return Property(implies_formula(self._formula, other.to_formula()))

    def until(self, other: Property | Predicate) -> Property:
        """Temporal until: this predicate holds at every frame until other becomes true.

        Args:
            other: Property or Predicate that must eventually hold

        Returns:
            Until property

        Example:
        ```python
        # The start button stays released until the power mode reaches ACC, which it does
        Signal("StartButton").equals(1).not_().until(Signal("PowerMode").equals(2))
        ```

        """
        return Property(self._formula).until(other)

    def release(self, other: Property | Predicate) -> Property:
        """Temporal release: other holds until this predicate releases it (dual of until).

        Args:
            other: Property or Predicate that must hold until released

        Returns:
            Release property

        Example:
        ```python
        # The brake stays engaged up to the frame the ignition comes on, and forever
        # if it never does
        Signal("Ignition").equals(1).release(Signal("Brake").equals(1))
        ```

        """
        return Property(self._formula).release(other)

    def metric_until(self, time_ms: int, other: Property | Predicate) -> Property:
        """Temporal until with time bound: this predicate holds until other, within time_ms.

        Args:
            time_ms: Time bound in milliseconds (must be >= 0)
            other: Property or Predicate that must hold within time_ms

        Returns:
            Metric Until property

        Raises:
            ValidationError: ``time_ms`` is negative.

        Example:
        ```python
        # The speed stays above 50 until the brake is pressed, which happens within 1000 ms
        Signal("Speed").greater_than(50).metric_until(1000, Signal("Brake").equals(1))
        ```

        """
        return Property(self._formula).metric_until(time_ms, other)

    def metric_release(self, time_ms: int, other: Property | Predicate) -> Property:
        """Temporal release with time bound: other holds until this predicate releases it.

        Args:
            time_ms: Time bound in milliseconds (must be >= 0)
            other: Property or Predicate that must hold until released

        Returns:
            Metric Release property

        Raises:
            ValidationError: ``time_ms`` is negative.

        Example:
        ```python
        # The brake stays engaged through the first 5000 ms, released sooner when the
        # ignition comes on
        Signal("Ignition").equals(1).metric_release(5000, Signal("Brake").equals(1))
        ```

        """
        return Property(self._formula).metric_release(time_ms, other)

    # ------------------------------------------------------------------
    # Discouraged in CAN analysis — kept for standard-LTLf completeness.
    # Prefer ``within(time_ms)`` / ``for_at_least(time_ms)`` on real CAN
    # traces, where inter-frame timing is jittery and "the next frame"
    # is not a stable notion. See individual method docstrings.
    # ------------------------------------------------------------------

    def next(self) -> Property:
        """Property must hold in the next frame (X operator).

        **DISCOURAGED on CAN networks.** The Next operator is rarely useful
        in CAN analysis because:

        - Timing uncertainty: CAN frames don't arrive at fixed intervals
        - ECU jitter: Processing delays vary unpredictably (1–10 ms typical)
        - Network effects: Retransmissions, priority inversion, bus contention
        - Ambiguous semantics: "Next frame" from which ECU?

        Prefer ``within(time_ms)`` for time-bounded checks:
        - More robust: Tolerates jitter and timing variations
        - Explicit bounds: Clearly states the acceptable time window
        - Better semantics: "Within 100 ms" is clearer than "next frame"

        Kept in the API because Next is a standard LTLf operator and some
        deterministic replay workflows (fixed-rate simulators, recorded
        traces with known sample period) can use it safely.

        Returns:
            Temporal property (LTL Next formula)

        Example (discouraged on real traces):
        ```python
        # Anti-pattern: assumes next frame arrives immediately
        Signal("Brake").equals(1).next()
        ```

        Better alternatives:
        ```python
        state_a = Signal("Gear").equals(1)
        state_b = Signal("Gear").equals(2)
        Signal("Brake").equals(1).within(10)  # within 10 ms
        Signal("Brake").equals(1).eventually()  # if timing doesn't matter
        state_a.metric_until(100, state_b)  # gear 1 until gear 2, within 100 ms
        ```

        """
        formula: NextFormula = {"operator": "next", "formula": self._formula}
        return Property(formula)

    def weak_next(self) -> Property:
        """Property must hold in the next frame, or hold vacuously at end of stream (WX operator).

        Like ``next()``, but satisfied when no successor frame exists (end of
        trace). Use for "if X then next Y" patterns where X may be true on the
        final frame, where strong Next would report a violation the trace's
        end causes rather than the property.

        **DISCOURAGED on CAN networks** for the same timing-uncertainty
        reasons as ``next()``. Prefer ``within(time_ms)`` in practice.

        Returns:
            Temporal property (LTL Weak Next formula)

        Example:
        ```python
        Signal("Brake").equals(1).weak_next()
        ```

        """
        formula: WeakNextFormula = {"operator": "weakNext", "formula": self._formula}
        return Property(formula)


__all__ = [
    "Predicate",
    "Property",
    "Signal",
    "eventually_always",
    "infinitely_often",
    "never",
]

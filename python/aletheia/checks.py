"""Industry-vocabulary Check API for CAN signal verification

Provides fluent, domain-specific wrappers over the LTL DSL so that
automotive technicians can define signal checks without knowing
temporal logic.

Usage:
    from aletheia import Check

    # Simple signal bounds
    Check.signal("Speed").never_exceeds(220)
    Check.signal("Voltage").stays_between(11.5, 14.5)

    # Causal / response checks
    Check.when("Brake").exceeds(50).then("BrakeLight").equals(1).within(100)

Every check compiles to the same LTL Property used by the DSL layer.
"""

from __future__ import annotations

from .dsl import Signal, Predicate, Property
from .protocols import LTLFormula


class CheckResult:
    """Terminal object wrapping a Property with optional metadata.

    Returned by every check-building chain.  Metadata (name, severity)
    is carried alongside the formula but is *not* included in the LTL
    dict produced by ``to_dict()`` — it is for display / reporting only.
    """

    def __init__(self, prop: Property) -> None:
        self._property: Property = prop
        self.name: str | None = None
        self.check_severity: str | None = None

    # -- chainable setters ---------------------------------------------------

    def named(self, name: str) -> CheckResult:
        """Assign a human-readable name to this check."""
        self.name = name
        return self

    def severity(self, level: str) -> CheckResult:
        """Assign a severity level (e.g. "critical", "warning")."""
        self.check_severity = level
        return self

    # -- output --------------------------------------------------------------

    def to_dict(self) -> LTLFormula:
        """Return the LTL formula dict (same as ``Property.to_dict()``)."""
        return self._property.to_dict()

    def to_property(self) -> Property:
        """Unwrap to the raw ``Property`` for DSL-level composition."""
        return self._property


# ============================================================================
# Simple signal checks
# ============================================================================

class CheckSignalPredicate:  # pylint: disable=too-few-public-methods
    """Intermediate holding a predicate that needs a temporal quantifier."""

    def __init__(self, prop: Property) -> None:
        self._property = prop

    def always(self) -> CheckResult:
        """The predicate must hold at every time step."""
        return CheckResult(self._property)


class SettlesBuilder:  # pylint: disable=too-few-public-methods
    """Intermediate for ``settles_between(lo, hi).within(ms)``."""

    def __init__(self, signal_name: str, lo: float, hi: float) -> None:
        self._signal_name = signal_name
        self._lo = lo
        self._hi = hi

    def within(self, time_ms: int) -> CheckResult:
        """Signal must settle between *lo* and *hi* within *time_ms* ms.

        Compiles to ``Signal(s).between(lo, hi).for_at_least(time_ms)``.
        """
        prop = Signal(self._signal_name).between(self._lo, self._hi).for_at_least(time_ms)
        return CheckResult(prop)


class CheckSignal:
    """Builder for single-signal checks (returned by ``Check.signal()``)."""

    def __init__(self, signal_name: str) -> None:
        self._name = signal_name

    # -- one-shot convenience methods ----------------------------------------

    def never_exceeds(self, value: float) -> CheckResult:
        """``Signal(s).less_than(value).always()`` — G(s < v)"""
        prop = Signal(self._name).less_than(value).always()
        return CheckResult(prop)

    def never_below(self, value: float) -> CheckResult:
        """``Signal(s).greater_than_or_equal(value).always()`` — G(s >= v)"""
        prop = Signal(self._name).greater_than_or_equal(value).always()
        return CheckResult(prop)

    def stays_between(self, lo: float, hi: float) -> CheckResult:
        """``Signal(s).between(lo, hi).always()`` — G(lo <= s <= hi)"""
        prop = Signal(self._name).between(lo, hi).always()
        return CheckResult(prop)

    def never_equals(self, value: float) -> CheckResult:
        """``Signal(s).equals(value).never()`` — G(not(s == v))"""
        prop = Signal(self._name).equals(value).never()
        return CheckResult(prop)

    # -- two-step methods (need another call to finish) ----------------------

    def equals(self, value: float) -> CheckSignalPredicate:
        """Begin an ``equals(v).always()`` chain."""
        prop = Signal(self._name).equals(value).always()
        return CheckSignalPredicate(prop)

    def settles_between(self, lo: float, hi: float) -> SettlesBuilder:
        """Begin a ``settles_between(lo, hi).within(ms)`` chain."""
        return SettlesBuilder(self._name, lo, hi)


# ============================================================================
# When / Then causal checks
# ============================================================================

class ThenCondition:  # pylint: disable=too-few-public-methods
    """Holds trigger + then predicates; needs ``.within(ms)`` to finish."""

    def __init__(self, trigger: Predicate, then_pred: Predicate) -> None:
        self._trigger = trigger
        self._then_pred = then_pred

    def within(self, time_ms: int) -> CheckResult:
        """``G(trigger → F≤t(then_predicate))``"""
        prop = self._trigger.implies(
            self._then_pred.within(time_ms)
        ).always()
        return CheckResult(prop)


class ThenSignal:
    """Builder for the then-clause of a when/then check."""

    def __init__(self, trigger: Predicate, then_signal_name: str) -> None:
        self._trigger = trigger
        self._then_name = then_signal_name

    def equals(self, value: float) -> ThenCondition:
        """Then-signal equals *value*."""
        pred = Signal(self._then_name).equals(value)
        return ThenCondition(self._trigger, pred)

    def exceeds(self, value: float) -> ThenCondition:
        """Then-signal exceeds *value*."""
        pred = Signal(self._then_name).greater_than(value)
        return ThenCondition(self._trigger, pred)

    def stays_between(self, lo: float, hi: float) -> ThenCondition:
        """Then-signal stays between *lo* and *hi*."""
        pred = Signal(self._then_name).between(lo, hi)
        return ThenCondition(self._trigger, pred)


class WhenCondition:  # pylint: disable=too-few-public-methods
    """Holds the trigger predicate; needs ``.then(signal)`` to continue."""

    def __init__(self, trigger: Predicate) -> None:
        self._trigger = trigger

    def then(self, signal_name: str) -> ThenSignal:
        """Specify the signal that must respond to the trigger."""
        return ThenSignal(self._trigger, signal_name)


class WhenSignal:
    """Builder for the when-clause (returned by ``Check.when()``)."""

    def __init__(self, signal_name: str) -> None:
        self._name = signal_name

    def exceeds(self, value: float) -> WhenCondition:
        """Trigger fires when signal exceeds *value*."""
        pred = Signal(self._name).greater_than(value)
        return WhenCondition(pred)

    def equals(self, value: float) -> WhenCondition:
        """Trigger fires when signal equals *value*."""
        pred = Signal(self._name).equals(value)
        return WhenCondition(pred)

    def drops_below(self, value: float) -> WhenCondition:
        """Trigger fires when signal drops below *value*."""
        pred = Signal(self._name).less_than(value)
        return WhenCondition(pred)


# ============================================================================
# Top-level entry point
# ============================================================================

class Check:
    """Entry point for the Check API.

    Examples::

        Check.signal("Speed").never_exceeds(220)
        Check.when("Brake").exceeds(50).then("BrakeLight").equals(1).within(100)
    """

    @staticmethod
    def signal(name: str) -> CheckSignal:
        """Start a single-signal check."""
        return CheckSignal(name)

    @staticmethod
    def when(signal_name: str) -> WhenSignal:
        """Start a causal when/then check."""
        return WhenSignal(signal_name)

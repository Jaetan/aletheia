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

from dataclasses import dataclass, replace

from .dsl import Signal, Predicate, Property
from .protocols import LTLFormula


@dataclass(frozen=True, slots=True)
class CheckResult:
    """Terminal object wrapping a Property with optional metadata.

    Returned by every check-building chain.  Metadata (name, severity)
    is carried alongside the formula but is *not* included in the LTL
    dict produced by ``to_dict()`` — it is for display / reporting only.

    Immutable — ``named()`` / ``severity()`` return new instances rather
    than mutating in place, so a single check template can be shared
    across concurrent sessions without one rename bleeding into another.
    """

    _property: Property
    name: str = ""
    check_severity: str = ""
    signal_name: str = ""
    condition_desc: str = ""

    # -- chainable "setters" (return new instance) --------------------------

    def named(self, name: str) -> CheckResult:
        """Return a copy with the human-readable name set."""
        return replace(self, name=name)

    def severity(self, level: str) -> CheckResult:
        """Return a copy with the severity level set."""
        return replace(self, check_severity=level)

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

    def __init__(
        self, prop: Property,
        signal_name: str = "",
        condition_desc: str = "",
    ) -> None:
        self._property = prop
        self._signal_name = signal_name
        self._condition_desc = condition_desc

    def always(self) -> CheckResult:
        """The predicate must hold at every time step."""
        return CheckResult(
            _property=self._property,
            signal_name=self._signal_name,
            condition_desc=self._condition_desc,
        )


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
        if time_ms < 0:
            raise ValueError(f"time_ms must be non-negative, got {time_ms}")
        prop = Signal(self._signal_name).between(self._lo, self._hi).for_at_least(time_ms)
        return CheckResult(
            _property=prop,
            signal_name=self._signal_name,
            condition_desc=f"between {self._lo} and {self._hi} within {time_ms}ms",
        )


class CheckSignal:
    """Builder for single-signal checks (returned by ``Check.signal()``)."""

    def __init__(self, signal_name: str) -> None:
        self._name = signal_name

    # -- one-shot convenience methods ----------------------------------------

    def never_exceeds(self, value: float) -> CheckResult:
        """``Signal(s).less_than(value).always()`` — G(s < v)"""
        prop = Signal(self._name).less_than(value).always()
        return CheckResult(
            _property=prop,
            signal_name=self._name,
            condition_desc=f"< {value}",
        )

    def never_below(self, value: float) -> CheckResult:
        """``Signal(s).greater_than_or_equal(value).always()`` — G(s >= v)"""
        prop = Signal(self._name).greater_than_or_equal(value).always()
        return CheckResult(
            _property=prop,
            signal_name=self._name,
            condition_desc=f">= {value}",
        )

    def stays_between(self, lo: float, hi: float) -> CheckResult:
        """``Signal(s).between(lo, hi).always()`` — G(lo <= s <= hi)"""
        if lo > hi:
            raise ValueError("stays_between: lo must be <= hi")
        prop = Signal(self._name).between(lo, hi).always()
        return CheckResult(
            _property=prop,
            signal_name=self._name,
            condition_desc=f"between {lo} and {hi}",
        )

    def never_equals(self, value: float) -> CheckResult:
        """``Signal(s).equals(value).never()`` — G(not(s == v))"""
        prop = Signal(self._name).equals(value).never()
        return CheckResult(
            _property=prop,
            signal_name=self._name,
            condition_desc=f"!= {value}",
        )

    # -- two-step methods (need another call to finish) ----------------------

    def equals(self, value: float) -> CheckSignalPredicate:
        """Begin an ``equals(v).always()`` chain."""
        prop = Signal(self._name).equals(value).always()
        return CheckSignalPredicate(prop, self._name, f"= {value}")

    def settles_between(self, lo: float, hi: float) -> SettlesBuilder:
        """Begin a ``settles_between(lo, hi).within(ms)`` chain."""
        if lo > hi:
            raise ValueError("settles_between: lo must be <= hi")
        return SettlesBuilder(self._name, lo, hi)


# ============================================================================
# When / Then causal checks
# ============================================================================

class ThenCondition:  # pylint: disable=too-few-public-methods
    """Holds trigger + then predicates; needs ``.within(ms)`` to finish."""

    def __init__(
        self, trigger: Predicate, then_pred: Predicate,
        then_signal: str = "", then_desc: str = "",
    ) -> None:
        self._trigger = trigger
        self._then_pred = then_pred
        self._then_signal = then_signal
        self._then_desc = then_desc

    def within(self, time_ms: int) -> CheckResult:
        """``G(trigger → F≤t(then_predicate))``"""
        if time_ms < 0:
            raise ValueError(f"time_ms must be non-negative, got {time_ms}")
        prop = self._trigger.implies(
            self._then_pred.within(time_ms)
        ).always()
        desc = f"{self._then_desc} within {time_ms}ms" if self._then_desc else ""
        return CheckResult(
            _property=prop,
            signal_name=self._then_signal,
            condition_desc=desc,
        )


class ThenSignal:
    """Builder for the then-clause of a when/then check."""

    def __init__(self, trigger: Predicate, then_signal_name: str) -> None:
        self._trigger = trigger
        self._then_name = then_signal_name

    def equals(self, value: float) -> ThenCondition:
        """Then-signal equals *value*."""
        pred = Signal(self._then_name).equals(value)
        return ThenCondition(self._trigger, pred, self._then_name, f"= {value}")

    def exceeds(self, value: float) -> ThenCondition:
        """Then-signal exceeds *value*."""
        pred = Signal(self._then_name).greater_than(value)
        return ThenCondition(self._trigger, pred, self._then_name, f"> {value}")

    def stays_between(self, lo: float, hi: float) -> ThenCondition:
        """Then-signal stays between *lo* and *hi*."""
        if lo > hi:
            raise ValueError("stays_between: lo must be <= hi")
        pred = Signal(self._then_name).between(lo, hi)
        return ThenCondition(
            self._trigger, pred, self._then_name, f"between {lo} and {hi}",
        )


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

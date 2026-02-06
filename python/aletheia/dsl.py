"""Python DSL for LTL properties over CAN signals

Provides fluent interface for expressing temporal properties:
    Signal("Speed").less_than(220).always()
    brake_pressed.implies(speed_decreases.within(100))

Usage with AletheiaClient:
    from aletheia import AletheiaClient, Signal

    property = Signal("Speed").less_than(220).always()
    client.set_properties([property.to_dict()])

Output format matches the Agda JSON schema:
    - All formulas use "operator" key (not "type")
    - Predicates use {"operator": "atomic", "predicate": {...}} format
    - Time bounds use "timebound" key (not "time_ms")
    - "never" desugars to always(not(...))
    - "implies" desugars to or(not(antecedent), consequent)
"""

from __future__ import annotations

from .protocols import (
    LTLFormula,
    AtomicFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    AlwaysFormula,
    EventuallyFormula,
    MetricEventuallyFormula,
    MetricAlwaysFormula,
    UntilFormula,
    ReleaseFormula,
    MetricUntilFormula,
    MetricReleaseFormula,
    NextFormula,
    SignalPredicate,
)


def _atomic(predicate: SignalPredicate) -> AtomicFormula:
    """Wrap a signal predicate in an atomic formula"""
    return {'operator': 'atomic', 'predicate': predicate}


class Signal:
    """Reference to a CAN signal for use in temporal properties"""

    def __init__(self, name: str):
        """Create a signal reference

        Args:
            name: Signal name (must exist in DBC)
        """
        self.name: str = name

    def equals(self, value: float) -> 'Predicate':
        """Signal equals a specific value

        Args:
            value: Expected signal value

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Gear").equals(0)  # Gear is in park
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'equals',
            'signal': self.name,
            'value': value
        })
        return Predicate(formula)

    def less_than(self, value: float) -> 'Predicate':
        """Signal is less than a value

        Args:
            value: Upper bound (exclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").less_than(220)  # Speed below 220 km/h
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'lessThan',
            'signal': self.name,
            'value': value
        })
        return Predicate(formula)

    def greater_than(self, value: float) -> 'Predicate':
        """Signal is greater than a value

        Args:
            value: Lower bound (exclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").greater_than(5)  # Vehicle moving
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'greaterThan',
            'signal': self.name,
            'value': value
        })
        return Predicate(formula)

    def less_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is less than or equal to a value

        Args:
            value: Upper bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'lessThanOrEqual',
            'signal': self.name,
            'value': value
        })
        return Predicate(formula)

    def greater_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is greater than or equal to a value

        Args:
            value: Lower bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'greaterThanOrEqual',
            'signal': self.name,
            'value': value
        })
        return Predicate(formula)

    def between(self, min_val: float, max_val: float) -> 'Predicate':
        """Signal is within a range (inclusive)

        Args:
            min_val: Minimum value (inclusive)
            max_val: Maximum value (inclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("BatteryVoltage").between(11.5, 14.5)
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'between',
            'signal': self.name,
            'min': min_val,
            'max': max_val
        })
        return Predicate(formula)

    def changed_by(self, delta: float) -> 'Predicate':
        """Signal changed by at least delta (absolute value)

        Checks |signal_now - signal_prev| >= |delta|

        Args:
            delta: Minimum change magnitude (can be negative for decrease)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").changed_by(-10)  # Speed decreased by 10+
        """
        formula: AtomicFormula = _atomic({
            'predicate': 'changedBy',
            'signal': self.name,
            'delta': delta
        })
        return Predicate(formula)


class Predicate:
    """Atomic predicate over CAN signals

    Created by Signal comparison methods. Can be composed into
    temporal properties using temporal operators.
    """

    def __init__(self, formula: LTLFormula):
        """Internal constructor - use Signal methods instead"""
        self._data: LTLFormula = formula

    def to_formula(self) -> LTLFormula:
        """Convert to LTL formula for use in composition

        Returns:
            LTL formula representation
        """
        return self._data

    def always(self) -> 'Property':
        """Property must always hold (globally)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("Speed").less_than(220).always()
        """
        formula: AlwaysFormula = {
            'operator': 'always',
            'formula': self._data
        }
        return Property(formula)

    def eventually(self) -> 'Property':
        """Property must eventually hold (sometime in future)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("DoorClosed").equals(1).eventually()
        """
        formula: EventuallyFormula = {
            'operator': 'eventually',
            'formula': self._data
        }
        return Property(formula)

    def never(self) -> 'Property':
        """Property must never hold (always negated)

        Desugars to always(not(formula)) for Agda compatibility.

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("ErrorCode").equals(0xFF).never()
        """
        formula: AlwaysFormula = {
            'operator': 'always',
            'formula': {
                'operator': 'not',
                'formula': self._data
            }
        }
        return Property(formula)

    def next(self) -> 'Property':
        """Property must hold in the next frame (X operator)

        WARNING: The Next operator is rarely useful in CAN analysis due to:
        - Timing uncertainty: CAN frames don't arrive at fixed intervals
        - ECU jitter: Processing delays vary unpredictably (1-10ms typical)
        - Network effects: Retransmissions, priority inversion, bus contention
        - Ambiguous semantics: "Next frame" from which ECU?

        For time-bounded checks, use .within(time_ms) instead:
        - More robust: Tolerates jitter and timing variations
        - Explicit bounds: Clearly states acceptable time window
        - Better semantics: "Within 100ms" is clearer than "next frame"

        Returns:
            Temporal property (LTL Next formula)

        Example (discouraged):
            # Anti-pattern: Assumes next frame arrives immediately
            Signal("Brake").equals(1).next()

        Better alternatives:
            # Time-bounded check (recommended)
            Signal("Brake").equals(1).within(10)  # Within 10ms

            # Eventually (if timing doesn't matter)
            Signal("Brake").equals(1).eventually()

            # Metric until for state transitions
            state_a.metric_until(100, state_b)  # Transition within 100ms
        """
        formula: NextFormula = {
            'operator': 'next',
            'formula': self._data
        }
        return Property(formula)

    def within(self, time_ms: int) -> 'Property':
        """Property must hold within time_ms milliseconds

        Uses Metric Eventually (time-bounded eventually operator).
        More robust than Next for CAN networks with jitter.

        Args:
            time_ms: Time bound in milliseconds

        Returns:
            Bounded temporal property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        formula: MetricEventuallyFormula = {
            'operator': 'metricEventually',
            'timebound': time_ms,
            'formula': self._data
        }
        return Property(formula)

    def for_at_least(self, time_ms: int) -> 'Property':
        """Property must hold continuously for at least time_ms milliseconds

        Uses Metric Always (time-bounded always operator).
        Useful for debouncing and stability checks.

        Args:
            time_ms: Duration in milliseconds

        Returns:
            Bounded temporal property

        Example:
            Signal("DoorClosed").equals(1).for_at_least(50)  # Debounced
        """
        formula: MetricAlwaysFormula = {
            'operator': 'metricAlways',
            'timebound': time_ms,
            'formula': self._data
        }
        return Property(formula)

    def and_(self, other: 'Predicate') -> 'Predicate':
        """Logical AND of two predicates

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
            left_ok.and_(right_ok)
        """
        formula: AndFormula = {
            'operator': 'and',
            'left': self._data,
            'right': other.to_formula()
        }
        return Predicate(formula)

    def or_(self, other: 'Predicate') -> 'Predicate':
        """Logical OR of two predicates

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
            error1.or_(error2)
        """
        formula: OrFormula = {
            'operator': 'or',
            'left': self._data,
            'right': other.to_formula()
        }
        return Predicate(formula)

    def not_(self) -> 'Predicate':
        """Logical NOT of predicate

        Returns:
            Negated predicate

        Example:
            Signal("Enabled").equals(1).not_()
        """
        formula: NotFormula = {
            'operator': 'not',
            'formula': self._data
        }
        return Predicate(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other

        Desugars to or(not(self), other) for Agda compatibility.

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        if isinstance(other, Predicate):
            other_formula = other.to_formula()
        else:
            other_formula = other.to_formula()

        formula: OrFormula = {
            'operator': 'or',
            'left': {
                'operator': 'not',
                'formula': self._data
            },
            'right': other_formula
        }
        return Property(formula)


class Property:
    """Temporal property (LTL formula)

    Created by Predicate temporal methods. Can be composed with
    other properties using logical operators.
    """

    def __init__(self, formula: LTLFormula):
        """Internal constructor - use Predicate methods instead"""
        self._data: LTLFormula = formula

    def to_formula(self) -> LTLFormula:
        """Convert to LTL formula for use in composition

        Returns:
            LTL formula representation
        """
        return self._data

    def and_(self, other: 'Property') -> 'Property':
        """Logical AND of two properties

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
            speed_ok.and_(voltage_ok)
        """
        formula: AndFormula = {
            'operator': 'and',
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def or_(self, other: 'Property') -> 'Property':
        """Logical OR of two properties

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
            charging.or_(engine_running)
        """
        formula: OrFormula = {
            'operator': 'or',
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other

        Desugars to or(not(self), other) for Agda compatibility.

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        if isinstance(other, Predicate):
            other_formula = other.to_formula()
        else:
            other_formula = other.to_formula()

        formula: OrFormula = {
            'operator': 'or',
            'left': {
                'operator': 'not',
                'formula': self._data
            },
            'right': other_formula
        }
        return Property(formula)

    def until(self, other: 'Property') -> 'Property':
        """Temporal until: self holds until other becomes true

        Args:
            other: Property that must eventually hold

        Returns:
            Until property

        Example:
            power_off.implies(power_start.never().until(power_acc))
        """
        formula: UntilFormula = {
            'operator': 'until',
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def release(self, other: 'Property') -> 'Property':
        """Temporal release: other holds until self releases it (dual of until)

        Args:
            other: Property that must hold until released

        Returns:
            Release property

        Example:
            # Safety interlock: brake must be engaged until ignition releases it
            ignition_on.release(brake_engaged)
        """
        formula: ReleaseFormula = {
            'operator': 'release',
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def metric_until(self, time_ms: int, other: 'Property') -> 'Property':
        """Temporal until with time bound: self holds until other, within time_ms

        More robust than Next for checking "next frame" conditions.
        Tolerates CAN jitter and ECU timing uncertainty.

        Args:
            time_ms: Time bound in milliseconds
            other: Property that must eventually hold

        Returns:
            Metric Until property

        Example:
            # Speed must stay above 50 until brake within 1000ms
            speed_ok.metric_until(1000, brake_pressed)
        """
        formula: MetricUntilFormula = {
            'operator': 'metricUntil',
            'timebound': time_ms,
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def metric_release(self, time_ms: int, other: 'Property') -> 'Property':
        """Temporal release with time bound: other holds until self releases it, within time_ms

        Args:
            time_ms: Time bound in milliseconds
            other: Property that must hold until released

        Returns:
            Metric Release property

        Example:
            # Brake must be engaged until ignition releases it, within 5000ms
            ignition_on.metric_release(5000, brake_engaged)
        """
        formula: MetricReleaseFormula = {
            'operator': 'metricRelease',
            'timebound': time_ms,
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def always(self) -> 'Property':
        """Property must always hold (globally) - applies to nested formulas

        Returns:
            Nested temporal property

        Example:
            # G(F(p)) - infinitely often pattern
            Signal("Speed").greater_than(100).eventually().always()
        """
        formula: AlwaysFormula = {
            'operator': 'always',
            'formula': self._data
        }
        return Property(formula)

    def eventually(self) -> 'Property':
        """Property must eventually hold - applies to nested formulas

        Returns:
            Nested temporal property

        Example:
            # F(G(p)) - eventually always (stability) pattern
            Signal("Temperature").less_than(70).always().eventually()
        """
        formula: EventuallyFormula = {
            'operator': 'eventually',
            'formula': self._data
        }
        return Property(formula)

    def not_(self) -> 'Property':
        """Logical negation of property - applies to nested formulas

        Returns:
            Negated property

        Example:
            # G(not F(p)) - never occurs pattern
            fault_eventually = Signal("Fault").equals(1).eventually()
            fault_eventually.not_().always()
        """
        formula: NotFormula = {
            'operator': 'not',
            'formula': self._data
        }
        return Property(formula)

    def next(self) -> 'Property':
        """Apply Next operator to nested formula

        WARNING: Next is rarely useful for CAN analysis.
        See Predicate.next() docstring for warnings and better alternatives.

        Use this for nested temporal operators like X(G(phi)) - "next, then always".

        Returns:
            Nested temporal property (X(nested))

        Example:
            # X(G(p)) - next frame, then always
            Signal("State").equals(1).always().next()
        """
        formula: NextFormula = {
            'operator': 'next',
            'formula': self._data
        }
        return Property(formula)

    def to_dict(self) -> LTLFormula:
        """Convert to dictionary for use with AletheiaClient

        Returns:
            Dictionary representation suitable for JSON serialization

        Example:
            property = Signal("Speed").less_than(220).always()
            client.set_properties([property.to_dict()])
        """
        return self._data


# ============================================================================
# NESTED TEMPORAL OPERATOR HELPERS
# ============================================================================

def infinitely_often(formula: Property | Predicate) -> Property:
    """G(F phi) - Property holds infinitely many times (liveness pattern)

    Standard LTL pattern for liveness properties that must occur repeatedly.
    This is NOT a primitive operator, but a composition of Always and Eventually.

    Use this when: You need to verify recurring behaviors (e.g., periodic signals,
    repeated state transitions, cyclic patterns).

    Args:
        formula: Property or Predicate that must hold infinitely often

    Returns:
        Always(Eventually(formula)) property

    Example:
        # Speed exceeds 100 infinitely often (repeated acceleration)
        infinitely_often(Signal("Speed").greater_than(100))

        # Equivalent fluent form:
        Signal("Speed").greater_than(100).eventually().always()

    Note: Helper exists for clarity when expressing this common LTL pattern.
    """
    if isinstance(formula, Predicate):
        inner = formula.eventually()
    else:
        inner = formula.eventually()
    return inner.always()


def eventually_always(formula: Property | Predicate) -> Property:
    """F(G phi) - Property eventually holds forever (stability pattern)

    Standard LTL pattern for stability/convergence properties.
    This is NOT a primitive operator, but a composition of Eventually and Always.

    Use this when: You need to verify that a system reaches a stable state
    (e.g., temperature stabilization, mode transitions, initialization complete).

    Args:
        formula: Property or Predicate that must eventually stabilize

    Returns:
        Eventually(Always(formula)) property

    Example:
        # Temperature eventually stabilizes below 70 degrees
        eventually_always(Signal("Temperature").less_than(70))

        # Equivalent fluent form:
        Signal("Temperature").less_than(70).always().eventually()

    Note: Helper exists for clarity when expressing this common LTL pattern.
    """
    if isinstance(formula, Predicate):
        inner = formula.always()
    else:
        inner = formula.always()
    return inner.eventually()


def never(formula: Property | Predicate) -> Property:
    """G(not phi) - Property never holds (strongest safety property)

    Equivalent to always(not(formula)) but more readable.

    Args:
        formula: Property or Predicate that must never hold

    Returns:
        Always(Not(formula)) property

    Example:
        # Critical fault never occurs
        never(Signal("CriticalFault").equals(1))

        # Equivalent to:
        Signal("CriticalFault").equals(1).not_().always()
    """
    if isinstance(formula, Predicate):
        inner = formula.not_()
    else:
        inner = formula.not_()
    return inner.always()

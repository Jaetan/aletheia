"""Python DSL for LTL properties over CAN signals

Provides fluent interface for expressing temporal properties:
    Signal("Speed").less_than(220).always()
    brake_pressed.implies(speed_decreases.within(100))

Usage with StreamingClient:
    from aletheia import StreamingClient, Signal

    property = Signal("Speed").less_than(220).always()
    client.set_properties([property.to_dict()])
"""

from __future__ import annotations

from .protocols import (
    LTLFormula,
    CompareFormula,
    BetweenFormula,
    ChangedByFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    AlwaysFormula,
    EventuallyFormula,
    NeverFormula,
    EventuallyWithinFormula,
    AlwaysWithinFormula,
    ImpliesFormula,
    UntilFormula,
)


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
        formula: CompareFormula = {
            'type': 'compare',
            'signal': self.name,
            'op': 'EQ',
            'value': value
        }
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
        formula: CompareFormula = {
            'type': 'compare',
            'signal': self.name,
            'op': 'LT',
            'value': value
        }
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
        formula: CompareFormula = {
            'type': 'compare',
            'signal': self.name,
            'op': 'GT',
            'value': value
        }
        return Predicate(formula)

    def less_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is less than or equal to a value

        Args:
            value: Upper bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        formula: CompareFormula = {
            'type': 'compare',
            'signal': self.name,
            'op': 'LE',
            'value': value
        }
        return Predicate(formula)

    def greater_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is greater than or equal to a value

        Args:
            value: Lower bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        formula: CompareFormula = {
            'type': 'compare',
            'signal': self.name,
            'op': 'GE',
            'value': value
        }
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
        formula: BetweenFormula = {
            'type': 'between',
            'signal': self.name,
            'min': min_val,
            'max': max_val
        }
        return Predicate(formula)

    def changed_by(self, delta: float) -> 'Predicate':
        """Signal changed by at least delta (absolute value)

        Checks |signal_now - signal_prev| ≥ |delta|

        Args:
            delta: Minimum change magnitude (can be negative for decrease)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").changed_by(-10)  # Speed decreased by 10+
        """
        formula: ChangedByFormula = {
            'type': 'changed_by',
            'signal': self.name,
            'delta': delta
        }
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
            'type': 'always',
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
            'type': 'eventually',
            'formula': self._data
        }
        return Property(formula)

    def never(self) -> 'Property':
        """Property must never hold (always negated)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("ErrorCode").equals(0xFF).never()
        """
        formula: NeverFormula = {
            'type': 'never',
            'formula': self._data
        }
        return Property(formula)

    def within(self, time_ms: int) -> 'Property':
        """Property must hold within time_ms milliseconds

        Args:
            time_ms: Time bound in milliseconds

        Returns:
            Bounded temporal property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        formula: EventuallyWithinFormula = {
            'type': 'eventually_within',
            'time_ms': time_ms,
            'formula': self._data
        }
        return Property(formula)

    def for_at_least(self, time_ms: int) -> 'Property':
        """Property must hold continuously for at least time_ms milliseconds

        Args:
            time_ms: Duration in milliseconds

        Returns:
            Bounded temporal property

        Example:
            Signal("DoorClosed").equals(1).for_at_least(50)  # Debounced
        """
        formula: AlwaysWithinFormula = {
            'type': 'always_within',
            'time_ms': time_ms,
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
            'type': 'and',
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
            'type': 'or',
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
            'type': 'not',
            'formula': self._data
        }
        return Predicate(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        # Get the formula from the other operand
        if isinstance(other, Predicate):
            other_formula = other.to_formula()
        else:
            other_formula = other.to_formula()

        formula: ImpliesFormula = {
            'type': 'implies',
            'antecedent': self._data,
            'consequent': other_formula
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
            'type': 'and',
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
            'type': 'or',
            'left': self._data,
            'right': other.to_formula()
        }
        return Property(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        # Get the formula from the other operand
        if isinstance(other, Predicate):
            other_formula = other.to_formula()
        else:
            other_formula = other.to_formula()

        formula: ImpliesFormula = {
            'type': 'implies',
            'antecedent': self._data,
            'consequent': other_formula
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
            'type': 'until',
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
            'type': 'always',
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
            'type': 'eventually',
            'formula': self._data
        }
        return Property(formula)

    def not_(self) -> 'Property':
        """Logical negation of property - applies to nested formulas

        Returns:
            Negated property

        Example:
            # G(¬F(p)) - never occurs pattern
            fault_eventually = Signal("Fault").equals(1).eventually()
            fault_eventually.not_().always()
        """
        formula: NotFormula = {
            'type': 'not',
            'formula': self._data
        }
        return Property(formula)

    def to_dict(self) -> LTLFormula:
        """Convert to dictionary for use with StreamingClient

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
    """G(F φ) - Property holds infinitely many times

    Standard LTL pattern for liveness properties that must occur repeatedly.

    Args:
        formula: Property or Predicate that must hold infinitely often

    Returns:
        Always(Eventually(formula)) property

    Example:
        # Speed exceeds 100 infinitely often (repeated acceleration)
        infinitely_often(Signal("Speed").greater_than(100))

        # Equivalent to:
        Signal("Speed").greater_than(100).eventually().always()
    """
    if isinstance(formula, Predicate):
        inner = formula.eventually()
    else:
        inner = formula.eventually()
    return inner.always()


def eventually_always(formula: Property | Predicate) -> Property:
    """F(G φ) - Property eventually holds forever

    Standard LTL pattern for stability/convergence properties.

    Args:
        formula: Property or Predicate that must eventually stabilize

    Returns:
        Eventually(Always(formula)) property

    Example:
        # Temperature eventually stabilizes below 70 degrees
        eventually_always(Signal("Temperature").less_than(70))

        # Equivalent to:
        Signal("Temperature").less_than(70).always().eventually()
    """
    if isinstance(formula, Predicate):
        inner = formula.always()
    else:
        inner = formula.always()
    return inner.eventually()


def never(formula: Property | Predicate) -> Property:
    """G(¬φ) - Property never holds (strongest safety property)

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

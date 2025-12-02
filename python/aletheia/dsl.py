"""Python DSL for LTL properties over CAN signals

Provides fluent interface for expressing temporal properties:
    Signal("Speed").less_than(220).always()
    brake_pressed.implies(speed_decreases.within(100))

Usage with StreamingClient:
    from aletheia import StreamingClient, Signal

    property = Signal("Speed").less_than(220).always()
    client.set_properties([property.to_dict()])
"""

from typing import Any, Dict, Union


class Signal:
    """Reference to a CAN signal for use in temporal properties"""

    def __init__(self, name: str):
        """Create a signal reference

        Args:
            name: Signal name (must exist in DBC)
        """
        self.name = name

    def equals(self, value: float) -> 'Predicate':
        """Signal equals a specific value

        Args:
            value: Expected signal value

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Gear").equals(0)  # Gear is in park
        """
        return Predicate({
            'type': 'compare',
            'signal': self.name,
            'op': 'EQ',
            'value': value
        })

    def less_than(self, value: float) -> 'Predicate':
        """Signal is less than a value

        Args:
            value: Upper bound (exclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").less_than(220)  # Speed below 220 km/h
        """
        return Predicate({
            'type': 'compare',
            'signal': self.name,
            'op': 'LT',
            'value': value
        })

    def greater_than(self, value: float) -> 'Predicate':
        """Signal is greater than a value

        Args:
            value: Lower bound (exclusive)

        Returns:
            Predicate that can be used in temporal operators

        Example:
            Signal("Speed").greater_than(5)  # Vehicle moving
        """
        return Predicate({
            'type': 'compare',
            'signal': self.name,
            'op': 'GT',
            'value': value
        })

    def less_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is less than or equal to a value

        Args:
            value: Upper bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        return Predicate({
            'type': 'compare',
            'signal': self.name,
            'op': 'LE',
            'value': value
        })

    def greater_than_or_equal(self, value: float) -> 'Predicate':
        """Signal is greater than or equal to a value

        Args:
            value: Lower bound (inclusive)

        Returns:
            Predicate that can be used in temporal operators
        """
        return Predicate({
            'type': 'compare',
            'signal': self.name,
            'op': 'GE',
            'value': value
        })

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
        return Predicate({
            'type': 'between',
            'signal': self.name,
            'min': min_val,
            'max': max_val
        })

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
        return Predicate({
            'type': 'changed_by',
            'signal': self.name,
            'delta': delta
        })


class Predicate:
    """Atomic predicate over CAN signals

    Created by Signal comparison methods. Can be composed into
    temporal properties using temporal operators.
    """

    def __init__(self, data: Dict[str, Any]):
        """Internal constructor - use Signal methods instead"""
        self._data = data

    def always(self) -> 'Property':
        """Property must always hold (globally)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("Speed").less_than(220).always()
        """
        return Property({
            'type': 'always',
            'formula': self._data
        })

    def eventually(self) -> 'Property':
        """Property must eventually hold (sometime in future)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("DoorClosed").equals(1).eventually()
        """
        return Property({
            'type': 'eventually',
            'formula': self._data
        })

    def never(self) -> 'Property':
        """Property must never hold (always negated)

        Returns:
            Temporal property (LTL formula)

        Example:
            Signal("ErrorCode").equals(0xFF).never()
        """
        return Property({
            'type': 'never',
            'formula': self._data
        })

    def within(self, time_ms: int) -> 'Property':
        """Property must hold within time_ms milliseconds

        Args:
            time_ms: Time bound in milliseconds

        Returns:
            Bounded temporal property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        return Property({
            'type': 'eventually_within',
            'time_ms': time_ms,
            'formula': self._data
        })

    def for_at_least(self, time_ms: int) -> 'Property':
        """Property must hold continuously for at least time_ms milliseconds

        Args:
            time_ms: Duration in milliseconds

        Returns:
            Bounded temporal property

        Example:
            Signal("DoorClosed").equals(1).for_at_least(50)  # Debounced
        """
        return Property({
            'type': 'always_within',
            'time_ms': time_ms,
            'formula': self._data
        })

    def and_(self, other: 'Predicate') -> 'Predicate':
        """Logical AND of two predicates

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
            left_ok.and_(right_ok)
        """
        return Predicate({
            'type': 'and',
            'left': self._data,
            'right': other._data
        })

    def or_(self, other: 'Predicate') -> 'Predicate':
        """Logical OR of two predicates

        Args:
            other: Another predicate

        Returns:
            Combined predicate

        Example:
            error1.or_(error2)
        """
        return Predicate({
            'type': 'or',
            'left': self._data,
            'right': other._data
        })

    def not_(self) -> 'Predicate':
        """Logical NOT of predicate

        Returns:
            Negated predicate

        Example:
            Signal("Enabled").equals(1).not_()
        """
        return Predicate({
            'type': 'not',
            'formula': self._data
        })

    def implies(self, other: Union['Property', 'Predicate']) -> 'Property':
        """Logical implication: if self then other

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        # Convert Predicate to Property if needed
        if isinstance(other, Predicate):
            other_data = other._data
        else:
            other_data = other._data

        return Property({
            'type': 'implies',
            'antecedent': self._data,
            'consequent': other_data
        })


class Property:
    """Temporal property (LTL formula)

    Created by Predicate temporal methods. Can be composed with
    other properties using logical operators.
    """

    def __init__(self, data: Dict[str, Any]):
        """Internal constructor - use Predicate methods instead"""
        self._data = data

    def and_(self, other: 'Property') -> 'Property':
        """Logical AND of two properties

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
            speed_ok.and_(voltage_ok)
        """
        return Property({
            'type': 'and',
            'left': self._data,
            'right': other._data
        })

    def or_(self, other: 'Property') -> 'Property':
        """Logical OR of two properties

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
            charging.or_(engine_running)
        """
        return Property({
            'type': 'or',
            'left': self._data,
            'right': other._data
        })

    def implies(self, other: Union['Property', 'Predicate']) -> 'Property':
        """Logical implication: if self then other

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
            brake_pressed.implies(speed_decreases.within(100))
        """
        # Convert Predicate to Property if needed
        if isinstance(other, Predicate):
            other_data = other._data
        else:
            other_data = other._data

        return Property({
            'type': 'implies',
            'antecedent': self._data,
            'consequent': other_data
        })

    def until(self, other: 'Property') -> 'Property':
        """Temporal until: self holds until other becomes true

        Args:
            other: Property that must eventually hold

        Returns:
            Until property

        Example:
            power_off.implies(power_start.never().until(power_acc))
        """
        return Property({
            'type': 'until',
            'left': self._data,
            'right': other._data
        })

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for use with StreamingClient

        Returns:
            Dictionary representation suitable for JSON serialization

        Example:
            property = Signal("Speed").less_than(220).always()
            client.set_properties([property.to_dict()])
        """
        return self._data

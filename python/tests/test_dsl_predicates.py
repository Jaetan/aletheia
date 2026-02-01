"""Unit tests for the Python DSL - Signal and Predicate

Tests cover:
- Signal comparison operators (equals, less_than, greater_than, etc.)
- Predicate logical operators (and_, or_, not_, implies)
"""

from typing import cast
from aletheia.dsl import Signal, Predicate, Property
from aletheia.protocols import (
    AtomicFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    MetricEventuallyFormula,
    EqualsPredicate,
    LessThanPredicate,
    GreaterThanPredicate,
    BetweenPredicate,
)


# ============================================================================
# SIGNAL COMPARISON OPERATORS
# ============================================================================

class TestSignalComparison:
    """Test Signal comparison methods"""

    def test_signal_creation(self) -> None:
        """Signal can be created with a name"""
        sig = Signal("Speed")
        assert sig.name == "Speed"

    def test_signal_empty_name(self) -> None:
        """Signal accepts empty string (validation happens in Agda)"""
        sig = Signal("")
        assert sig.name == ""

    def test_equals(self) -> None:
        """Signal.equals() creates correct predicate"""
        pred = Signal("Gear").equals(0)
        assert isinstance(pred, Predicate)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'equals',
                'signal': 'Gear',
                'value': 0
            }
        }

    def test_less_than(self) -> None:
        """Signal.less_than() creates correct predicate"""
        pred = Signal("Speed").less_than(220)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'lessThan',
                'signal': 'Speed',
                'value': 220
            }
        }

    def test_greater_than(self) -> None:
        """Signal.greater_than() creates correct predicate"""
        pred = Signal("Speed").greater_than(5)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'greaterThan',
                'signal': 'Speed',
                'value': 5
            }
        }

    def test_less_than_or_equal(self) -> None:
        """Signal.less_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").less_than_or_equal(14.5)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'lessThanOrEqual',
                'signal': 'Voltage',
                'value': 14.5
            }
        }

    def test_greater_than_or_equal(self) -> None:
        """Signal.greater_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").greater_than_or_equal(11.5)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'greaterThanOrEqual',
                'signal': 'Voltage',
                'value': 11.5
            }
        }

    def test_between(self) -> None:
        """Signal.between() creates correct predicate"""
        pred = Signal("Voltage").between(11.5, 14.5)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'between',
                'signal': 'Voltage',
                'min': 11.5,
                'max': 14.5
            }
        }

    def test_changed_by(self) -> None:
        """Signal.changed_by() creates correct predicate"""
        pred = Signal("Speed").changed_by(-10)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula == {
            'operator': 'atomic',
            'predicate': {
                'predicate': 'changedBy',
                'signal': 'Speed',
                'delta': -10
            }
        }

    # Edge cases
    def test_comparison_with_zero(self) -> None:
        """Comparison with zero works"""
        pred = Signal("Speed").equals(0)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(EqualsPredicate, formula['predicate'])
        assert inner_pred['value'] == 0

    def test_comparison_with_negative(self) -> None:
        """Comparison with negative values works"""
        pred = Signal("Temp").greater_than(-40)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(GreaterThanPredicate, formula['predicate'])
        assert inner_pred['value'] == -40

    def test_comparison_with_float(self) -> None:
        """Comparison with float values works"""
        pred = Signal("Voltage").equals(12.6)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(EqualsPredicate, formula['predicate'])
        assert inner_pred['value'] == 12.6

    def test_comparison_with_large_number(self) -> None:
        """Comparison with large numbers works"""
        pred = Signal("Counter").less_than(1000000)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(LessThanPredicate, formula['predicate'])
        assert inner_pred['value'] == 1000000

    def test_between_min_equals_max(self) -> None:
        """between() works when min equals max (single value range)"""
        pred = Signal("Mode").between(5, 5)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(BetweenPredicate, formula['predicate'])
        assert inner_pred['min'] == 5
        assert inner_pred['max'] == 5

    def test_between_reversed_bounds(self) -> None:
        """between() accepts reversed bounds (validation in Agda)"""
        pred = Signal("X").between(10, 5)
        formula = cast(AtomicFormula, pred.to_formula())
        inner_pred = cast(BetweenPredicate, formula['predicate'])
        assert inner_pred['min'] == 10
        assert inner_pred['max'] == 5


# ============================================================================
# LOGICAL OPERATORS - PREDICATE LEVEL
# ============================================================================

class TestPredicateLogicalOperators:
    """Test Predicate logical operators (and_, or_, not_, implies)"""

    def test_and(self) -> None:
        """Predicate.and_() combines two predicates"""
        left = Signal("LeftDoor").equals(1)
        right = Signal("RightDoor").equals(1)
        combined = left.and_(right)

        assert isinstance(combined, Predicate)
        formula = cast(AndFormula, combined.to_formula())
        assert formula['operator'] == 'and'
        left_formula = cast(AtomicFormula, formula['left'])
        right_formula = cast(AtomicFormula, formula['right'])
        assert left_formula['predicate']['signal'] == 'LeftDoor'
        assert right_formula['predicate']['signal'] == 'RightDoor'

    def test_or(self) -> None:
        """Predicate.or_() combines two predicates"""
        error1 = Signal("Error1").equals(1)
        error2 = Signal("Error2").equals(1)
        combined = error1.or_(error2)

        formula = cast(OrFormula, combined.to_formula())
        assert formula['operator'] == 'or'

    def test_not(self) -> None:
        """Predicate.not_() negates predicate"""
        pred = Signal("Enabled").equals(1)
        negated = pred.not_()

        formula = cast(NotFormula, negated.to_formula())
        assert formula['operator'] == 'not'
        inner_formula = cast(AtomicFormula, formula['formula'])
        assert inner_formula['predicate']['signal'] == 'Enabled'

    def test_implies_predicate_to_predicate(self) -> None:
        """Predicate.implies() desugars to or(not(...), ...)"""
        brake = Signal("Brake").equals(1)
        throttle = Signal("Throttle").equals(0)
        implication = brake.implies(throttle)

        assert isinstance(implication, Property)
        data = cast(OrFormula, implication.to_dict())
        assert data['operator'] == 'or'
        # left is not(antecedent)
        not_ant = cast(NotFormula, data['left'])
        assert not_ant['operator'] == 'not'
        ant = cast(AtomicFormula, not_ant['formula'])
        assert ant['predicate']['signal'] == 'Brake'
        # right is consequent
        cons = cast(AtomicFormula, data['right'])
        assert cons['predicate']['signal'] == 'Throttle'

    def test_implies_predicate_to_property(self) -> None:
        """Predicate.implies() with a Property desugars correctly"""
        brake = Signal("Brake").equals(1)
        speed_decrease = Signal("Speed").changed_by(-10).within(100)
        implication = brake.implies(speed_decrease)

        data = cast(OrFormula, implication.to_dict())
        assert data['operator'] == 'or'
        consequent = cast(MetricEventuallyFormula, data['right'])
        assert consequent['operator'] == 'metricEventually'

    def test_chained_logical_operators(self) -> None:
        """Multiple logical operators can be chained"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        combined = a.and_(b).and_(c)
        formula = cast(AndFormula, combined.to_formula())
        assert formula['operator'] == 'and'
        left_formula = cast(AndFormula, formula['left'])
        assert left_formula['operator'] == 'and'  # Nested

    def test_not_of_compound(self) -> None:
        """not_() works on compound predicates"""
        compound = Signal("A").equals(1).and_(Signal("B").equals(1))
        negated = compound.not_()

        formula = cast(NotFormula, negated.to_formula())
        assert formula['operator'] == 'not'
        inner_formula = cast(AndFormula, formula['formula'])
        assert inner_formula['operator'] == 'and'

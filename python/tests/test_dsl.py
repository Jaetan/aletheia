"""Unit tests for the Python DSL (Signal/Predicate/Property)

Tests cover:
- Signal comparison operators
- Temporal operators (always, eventually, never, within, for_at_least)
- Logical operators (and, or, not, implies)
- Composition and chaining
- Edge cases (empty strings, special values, negative numbers)
- JSON serialization
"""

import pytest
import math
from aletheia.dsl import Signal, Predicate, Property


# ============================================================================
# SIGNAL COMPARISON OPERATORS
# ============================================================================

class TestSignalComparison:
    """Test Signal comparison methods"""

    def test_signal_creation(self):
        """Signal can be created with a name"""
        sig = Signal("Speed")
        assert sig.name == "Speed"

    def test_signal_empty_name(self):
        """Signal accepts empty string (validation happens in Agda)"""
        sig = Signal("")
        assert sig.name == ""

    def test_equals(self):
        """Signal.equals() creates correct predicate"""
        pred = Signal("Gear").equals(0)
        assert isinstance(pred, Predicate)
        assert pred._data == {
            'type': 'compare',
            'signal': 'Gear',
            'op': 'EQ',
            'value': 0
        }

    def test_less_than(self):
        """Signal.less_than() creates correct predicate"""
        pred = Signal("Speed").less_than(220)
        assert pred._data == {
            'type': 'compare',
            'signal': 'Speed',
            'op': 'LT',
            'value': 220
        }

    def test_greater_than(self):
        """Signal.greater_than() creates correct predicate"""
        pred = Signal("Speed").greater_than(5)
        assert pred._data == {
            'type': 'compare',
            'signal': 'Speed',
            'op': 'GT',
            'value': 5
        }

    def test_less_than_or_equal(self):
        """Signal.less_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").less_than_or_equal(14.5)
        assert pred._data == {
            'type': 'compare',
            'signal': 'Voltage',
            'op': 'LE',
            'value': 14.5
        }

    def test_greater_than_or_equal(self):
        """Signal.greater_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").greater_than_or_equal(11.5)
        assert pred._data == {
            'type': 'compare',
            'signal': 'Voltage',
            'op': 'GE',
            'value': 11.5
        }

    def test_between(self):
        """Signal.between() creates correct predicate"""
        pred = Signal("Voltage").between(11.5, 14.5)
        assert pred._data == {
            'type': 'between',
            'signal': 'Voltage',
            'min': 11.5,
            'max': 14.5
        }

    def test_changed_by(self):
        """Signal.changed_by() creates correct predicate"""
        pred = Signal("Speed").changed_by(-10)
        assert pred._data == {
            'type': 'changed_by',
            'signal': 'Speed',
            'delta': -10
        }

    # Edge cases
    def test_comparison_with_zero(self):
        """Comparison with zero works"""
        pred = Signal("Speed").equals(0)
        assert pred._data['value'] == 0

    def test_comparison_with_negative(self):
        """Comparison with negative values works"""
        pred = Signal("Temp").greater_than(-40)
        assert pred._data['value'] == -40

    def test_comparison_with_float(self):
        """Comparison with float values works"""
        pred = Signal("Voltage").equals(12.6)
        assert pred._data['value'] == 12.6

    def test_comparison_with_large_number(self):
        """Comparison with large numbers works"""
        pred = Signal("Counter").less_than(1000000)
        assert pred._data['value'] == 1000000

    def test_between_min_equals_max(self):
        """between() works when min equals max (single value range)"""
        pred = Signal("Mode").between(5, 5)
        assert pred._data['min'] == 5
        assert pred._data['max'] == 5

    def test_between_reversed_bounds(self):
        """between() accepts reversed bounds (validation in Agda)"""
        pred = Signal("X").between(10, 5)
        assert pred._data['min'] == 10
        assert pred._data['max'] == 5


# ============================================================================
# TEMPORAL OPERATORS
# ============================================================================

class TestTemporalOperators:
    """Test Predicate temporal operators"""

    def test_always(self):
        """Predicate.always() creates correct property"""
        prop = Signal("Speed").less_than(220).always()
        assert isinstance(prop, Property)
        assert prop._data['type'] == 'always'
        assert prop._data['formula']['op'] == 'LT'

    def test_eventually(self):
        """Predicate.eventually() creates correct property"""
        prop = Signal("DoorClosed").equals(1).eventually()
        assert prop._data['type'] == 'eventually'

    def test_never(self):
        """Predicate.never() creates correct property"""
        prop = Signal("ErrorCode").equals(0xFF).never()
        assert prop._data['type'] == 'never'

    def test_within(self):
        """Predicate.within() creates bounded temporal property"""
        prop = Signal("BrakePressed").equals(1).within(100)
        assert prop._data['type'] == 'eventually_within'
        assert prop._data['time_ms'] == 100

    def test_for_at_least(self):
        """Predicate.for_at_least() creates bounded temporal property"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        assert prop._data['type'] == 'always_within'
        assert prop._data['time_ms'] == 50

    def test_within_zero_ms(self):
        """within(0) is valid (immediate)"""
        prop = Signal("X").equals(1).within(0)
        assert prop._data['time_ms'] == 0

    def test_for_at_least_zero_ms(self):
        """for_at_least(0) is valid"""
        prop = Signal("X").equals(1).for_at_least(0)
        assert prop._data['time_ms'] == 0

    def test_large_time_bounds(self):
        """Large time bounds work (hours)"""
        prop = Signal("EngineOn").equals(1).for_at_least(3600000)  # 1 hour
        assert prop._data['time_ms'] == 3600000


# ============================================================================
# LOGICAL OPERATORS - PREDICATE LEVEL
# ============================================================================

class TestPredicateLogicalOperators:
    """Test Predicate logical operators (and_, or_, not_, implies)"""

    def test_and(self):
        """Predicate.and_() combines two predicates"""
        left = Signal("LeftDoor").equals(1)
        right = Signal("RightDoor").equals(1)
        combined = left.and_(right)

        assert isinstance(combined, Predicate)
        assert combined._data['type'] == 'and'
        assert combined._data['left']['signal'] == 'LeftDoor'
        assert combined._data['right']['signal'] == 'RightDoor'

    def test_or(self):
        """Predicate.or_() combines two predicates"""
        error1 = Signal("Error1").equals(1)
        error2 = Signal("Error2").equals(1)
        combined = error1.or_(error2)

        assert combined._data['type'] == 'or'

    def test_not(self):
        """Predicate.not_() negates predicate"""
        pred = Signal("Enabled").equals(1)
        negated = pred.not_()

        assert negated._data['type'] == 'not'
        assert negated._data['formula']['signal'] == 'Enabled'

    def test_implies_predicate_to_predicate(self):
        """Predicate.implies() with another Predicate"""
        brake = Signal("Brake").equals(1)
        throttle = Signal("Throttle").equals(0)
        implication = brake.implies(throttle)

        assert isinstance(implication, Property)
        assert implication._data['type'] == 'implies'
        assert implication._data['antecedent']['signal'] == 'Brake'
        assert implication._data['consequent']['signal'] == 'Throttle'

    def test_implies_predicate_to_property(self):
        """Predicate.implies() with a Property"""
        brake = Signal("Brake").equals(1)
        speed_decrease = Signal("Speed").changed_by(-10).within(100)
        implication = brake.implies(speed_decrease)

        assert implication._data['type'] == 'implies'
        assert implication._data['consequent']['type'] == 'eventually_within'

    def test_chained_logical_operators(self):
        """Multiple logical operators can be chained"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        combined = a.and_(b).and_(c)
        assert combined._data['type'] == 'and'
        assert combined._data['left']['type'] == 'and'  # Nested

    def test_not_of_compound(self):
        """not_() works on compound predicates"""
        compound = Signal("A").equals(1).and_(Signal("B").equals(1))
        negated = compound.not_()

        assert negated._data['type'] == 'not'
        assert negated._data['formula']['type'] == 'and'


# ============================================================================
# LOGICAL OPERATORS - PROPERTY LEVEL
# ============================================================================

class TestPropertyLogicalOperators:
    """Test Property logical operators"""

    def test_property_and(self):
        """Property.and_() combines two properties"""
        speed_ok = Signal("Speed").less_than(220).always()
        voltage_ok = Signal("Voltage").between(11.5, 14.5).always()
        combined = speed_ok.and_(voltage_ok)

        assert isinstance(combined, Property)
        assert combined._data['type'] == 'and'

    def test_property_or(self):
        """Property.or_() combines two properties"""
        charging = Signal("Charging").equals(1).eventually()
        engine = Signal("Engine").equals(1).eventually()
        combined = charging.or_(engine)

        assert combined._data['type'] == 'or'

    def test_property_implies(self):
        """Property.implies() creates implication"""
        brake = Signal("Brake").equals(1).eventually()
        stopped = Signal("Speed").equals(0).eventually()
        implication = brake.implies(stopped)

        assert implication._data['type'] == 'implies'

    def test_until(self):
        """Property.until() creates until temporal formula"""
        power_low = Signal("PowerMode").equals(0).always()
        power_acc = Signal("PowerMode").equals(1).eventually()
        until_prop = power_low.until(power_acc)

        assert until_prop._data['type'] == 'until'
        assert until_prop._data['left']['type'] == 'always'
        assert until_prop._data['right']['type'] == 'eventually'


# ============================================================================
# COMPOSITION AND CHAINING
# ============================================================================

class TestComposition:
    """Test complex compositions and method chaining"""

    def test_fluent_chaining(self):
        """Methods can be chained fluently"""
        prop = Signal("Speed").less_than(220).always()
        assert prop._data['type'] == 'always'
        assert prop._data['formula']['op'] == 'LT'

    def test_complex_composition(self):
        """Complex property compositions work"""
        # (Speed < 220 ∧ Voltage ∈ [11.5, 14.5]) always
        speed_ok = Signal("Speed").less_than(220)
        voltage_ok = Signal("Voltage").between(11.5, 14.5)
        combined = speed_ok.and_(voltage_ok).always()

        assert combined._data['type'] == 'always'
        assert combined._data['formula']['type'] == 'and'

    def test_implication_with_temporal(self):
        """Implication with temporal operators"""
        # Brake pressed → Speed decreases within 100ms
        brake = Signal("Brake").equals(1)
        speed_dec = Signal("Speed").changed_by(-10).within(100)
        prop = brake.implies(speed_dec)

        assert prop._data['type'] == 'implies'
        assert prop._data['consequent']['type'] == 'eventually_within'

    def test_nested_implications(self):
        """Nested implications work"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        # A → (B → C)
        inner = b.implies(c.eventually())
        outer = a.implies(inner)

        assert outer._data['type'] == 'implies'
        assert outer._data['consequent']['type'] == 'implies'

    def test_until_with_complex_formulas(self):
        """until() works with complex properties"""
        left = Signal("State").equals(0).always()
        right = Signal("State").equals(1).and_(Signal("Ready").equals(1)).eventually()
        prop = left.until(right)

        assert prop._data['type'] == 'until'

    def test_mixed_temporal_and_logical(self):
        """Mixing temporal and logical operators"""
        # (A always) ∧ (B eventually)
        always_a = Signal("A").equals(1).always()
        eventually_b = Signal("B").equals(1).eventually()
        combined = always_a.and_(eventually_b)

        assert combined._data['type'] == 'and'
        assert combined._data['left']['type'] == 'always'
        assert combined._data['right']['type'] == 'eventually'


# ============================================================================
# JSON SERIALIZATION
# ============================================================================

class TestJSONSerialization:
    """Test to_dict() and JSON serialization"""

    def test_simple_property_to_dict(self):
        """Simple property serializes correctly"""
        prop = Signal("Speed").less_than(220).always()
        data = prop.to_dict()

        assert isinstance(data, dict)
        assert data['type'] == 'always'
        assert data['formula']['signal'] == 'Speed'

    def test_complex_property_to_dict(self):
        """Complex property serializes correctly"""
        left = Signal("A").equals(1)
        right = Signal("B").equals(1)
        prop = left.and_(right).always()
        data = prop.to_dict()

        assert data['type'] == 'always'
        assert data['formula']['type'] == 'and'

    def test_nested_structure(self):
        """Deeply nested structures serialize"""
        prop = Signal("A").equals(1).and_(
            Signal("B").equals(1).and_(
                Signal("C").equals(1)
            )
        ).always()

        data = prop.to_dict()
        assert data['formula']['left']['type'] == 'compare'
        assert data['formula']['right']['type'] == 'and'

    def test_serialization_preserves_values(self):
        """Serialization preserves all values correctly"""
        prop = Signal("Voltage").between(11.5, 14.5).for_at_least(1000)
        data = prop.to_dict()

        assert data['time_ms'] == 1000
        assert data['formula']['min'] == 11.5
        assert data['formula']['max'] == 14.5


# ============================================================================
# EDGE CASES AND ERROR CONDITIONS
# ============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""

    def test_signal_with_unicode_name(self):
        """Signal names can contain unicode (validation in Agda)"""
        sig = Signal("Tür_Öffnen")
        pred = sig.equals(1)
        assert pred._data['signal'] == "Tür_Öffnen"

    def test_signal_with_special_chars(self):
        """Signal names can contain special characters"""
        sig = Signal("CAN_Bus$Status#1")
        assert sig.name == "CAN_Bus$Status#1"

    def test_zero_comparison(self):
        """Zero is a valid comparison value"""
        pred = Signal("Speed").equals(0)
        assert pred._data['value'] == 0

    def test_negative_delta(self):
        """Negative delta for changed_by works"""
        pred = Signal("Speed").changed_by(-10)
        assert pred._data['delta'] == -10

    def test_fractional_values(self):
        """Fractional values work in comparisons"""
        pred = Signal("Voltage").equals(12.65)
        assert pred._data['value'] == 12.65

    def test_very_large_time_bound(self):
        """Very large time bounds work"""
        prop = Signal("X").equals(1).within(999999999)
        assert prop._data['time_ms'] == 999999999

    def test_chaining_same_operators(self):
        """Chaining same operator multiple times"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)
        d = Signal("D").equals(1)

        result = a.and_(b).and_(c).and_(d)
        assert result._data['type'] == 'and'

    def test_property_methods_return_new_objects(self):
        """Property methods return new objects (immutable)"""
        base = Signal("Speed").less_than(100)
        prop1 = base.always()
        prop2 = base.eventually()

        assert prop1 is not prop2
        assert prop1._data['type'] != prop2._data['type']


# ============================================================================
# REAL-WORLD EXAMPLES
# ============================================================================

class TestRealWorldExamples:
    """Test real-world automotive property examples"""

    def test_speed_limit(self):
        """Speed must always be under limit"""
        prop = Signal("Speed").less_than(220).always()
        data = prop.to_dict()

        assert data['type'] == 'always'
        assert data['formula']['value'] == 220

    def test_brake_safety(self):
        """Brake pressed implies throttle zero"""
        brake = Signal("BrakePressed").equals(1)
        throttle = Signal("ThrottlePosition").equals(0)
        prop = brake.implies(throttle)

        assert prop._data['type'] == 'implies'

    def test_voltage_range(self):
        """Battery voltage stays in safe range"""
        prop = Signal("BatteryVoltage").between(11.5, 14.5).always()
        data = prop.to_dict()

        assert data['formula']['min'] == 11.5
        assert data['formula']['max'] == 14.5

    def test_door_debounce(self):
        """Door closed signal must be stable (debounced)"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        assert prop._data['time_ms'] == 50

    def test_emergency_brake(self):
        """Emergency brake → Speed decreases quickly"""
        emergency = Signal("EmergencyBrake").equals(1)
        speed_dec = Signal("Speed").changed_by(-20).within(200)
        prop = emergency.implies(speed_dec)

        data = prop.to_dict()
        assert data['consequent']['time_ms'] == 200

    def test_gear_sequence(self):
        """Gear in park until ignition on"""
        park = Signal("Gear").equals(0).always()
        ignition = Signal("Ignition").equals(1).eventually()
        prop = park.until(ignition)

        assert prop._data['type'] == 'until'

    def test_multi_error_detection(self):
        """Multiple error codes can never occur"""
        err1 = Signal("ErrorCode1").equals(0xFF).never()
        err2 = Signal("ErrorCode2").equals(0xFF).never()
        prop = err1.and_(err2)

        assert prop._data['left']['type'] == 'never'
        assert prop._data['right']['type'] == 'never'

    def test_turn_signal_pattern(self):
        """Turn signal blinks regularly (simplified)"""
        on = Signal("LeftTurnSignal").equals(1)
        off = Signal("LeftTurnSignal").equals(0)
        # Simplified: on implies off within 500ms
        prop = on.implies(off.within(500))

        assert prop._data['consequent']['time_ms'] == 500

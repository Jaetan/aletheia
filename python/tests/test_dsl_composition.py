"""Unit tests for the Python DSL - Composition and Serialization

Tests cover:
- Property logical operators
- Complex compositions and method chaining
- JSON serialization
- Edge cases and boundary conditions
- Real-world automotive examples
"""

from typing import cast
from aletheia.dsl import Signal, Property
from aletheia.protocols import (
    AtomicFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    AlwaysFormula,
    EventuallyFormula,
    MetricEventuallyFormula,
    MetricAlwaysFormula,
    UntilFormula,
)


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
        data = cast(AndFormula, combined.to_dict())
        assert data['operator'] == 'and'

    def test_property_or(self):
        """Property.or_() combines two properties"""
        charging = Signal("Charging").equals(1).eventually()
        engine = Signal("Engine").equals(1).eventually()
        combined = charging.or_(engine)

        data = cast(OrFormula, combined.to_dict())
        assert data['operator'] == 'or'

    def test_property_implies(self):
        """Property.implies() desugars to or(not(...), ...)"""
        brake = Signal("Brake").equals(1).eventually()
        stopped = Signal("Speed").equals(0).eventually()
        implication = brake.implies(stopped)

        data = cast(OrFormula, implication.to_dict())
        assert data['operator'] == 'or'
        not_ant = cast(NotFormula, data['left'])
        assert not_ant['operator'] == 'not'

    def test_until(self):
        """Property.until() creates until temporal formula"""
        power_low = Signal("PowerMode").equals(0).always()
        power_acc = Signal("PowerMode").equals(1).eventually()
        until_prop = power_low.until(power_acc)

        data = cast(UntilFormula, until_prop.to_dict())
        assert data['operator'] == 'until'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['operator'] == 'always'
        assert right_data['operator'] == 'eventually'


# ============================================================================
# COMPOSITION AND CHAINING
# ============================================================================

class TestComposition:
    """Test complex compositions and method chaining"""

    def test_fluent_chaining(self):
        """Methods can be chained fluently"""
        prop = Signal("Speed").less_than(220).always()
        data = cast(AlwaysFormula, prop.to_dict())
        assert data['operator'] == 'always'
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['predicate'] == 'lessThan'

    def test_complex_composition(self):
        """Complex property compositions work"""
        # (Speed < 220 AND Voltage in [11.5, 14.5]) always
        speed_ok = Signal("Speed").less_than(220)
        voltage_ok = Signal("Voltage").between(11.5, 14.5)
        combined = speed_ok.and_(voltage_ok).always()

        data = cast(AlwaysFormula, combined.to_dict())
        assert data['operator'] == 'always'
        formula = cast(AndFormula, data['formula'])
        assert formula['operator'] == 'and'

    def test_implication_with_temporal(self):
        """Implication with temporal operators desugars correctly"""
        # Brake pressed -> Speed decreases within 100ms
        brake = Signal("Brake").equals(1)
        speed_dec = Signal("Speed").changed_by(-10).within(100)
        prop = brake.implies(speed_dec)

        data = cast(OrFormula, prop.to_dict())
        assert data['operator'] == 'or'
        consequent = cast(MetricEventuallyFormula, data['right'])
        assert consequent['operator'] == 'metricEventually'

    def test_nested_implications(self):
        """Nested implications desugar correctly"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        # A -> (B -> C)
        inner = b.implies(c.eventually())
        outer = a.implies(inner)

        data = cast(OrFormula, outer.to_dict())
        assert data['operator'] == 'or'
        # consequent is inner implication (also desugared to or)
        consequent = cast(OrFormula, data['right'])
        assert consequent['operator'] == 'or'

    def test_until_with_complex_formulas(self):
        """until() works with complex properties"""
        left = Signal("State").equals(0).always()
        right = Signal("State").equals(1).and_(Signal("Ready").equals(1)).eventually()
        prop = left.until(right)

        data = cast(UntilFormula, prop.to_dict())
        assert data['operator'] == 'until'

    def test_mixed_temporal_and_logical(self):
        """Mixing temporal and logical operators"""
        # (A always) AND (B eventually)
        always_a = Signal("A").equals(1).always()
        eventually_b = Signal("B").equals(1).eventually()
        combined = always_a.and_(eventually_b)

        data = cast(AndFormula, combined.to_dict())
        assert data['operator'] == 'and'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['operator'] == 'always'
        assert right_data['operator'] == 'eventually'


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
        assert data['operator'] == 'always'
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['signal'] == 'Speed'

    def test_complex_property_to_dict(self):
        """Complex property serializes correctly"""
        left = Signal("A").equals(1)
        right = Signal("B").equals(1)
        prop = left.and_(right).always()
        data = prop.to_dict()

        assert data['operator'] == 'always'
        formula = cast(AndFormula, data['formula'])
        assert formula['operator'] == 'and'

    def test_nested_structure(self):
        """Deeply nested structures serialize"""
        prop = Signal("A").equals(1).and_(
            Signal("B").equals(1).and_(
                Signal("C").equals(1)
            )
        ).always()

        data = cast(AlwaysFormula, prop.to_dict())
        formula = cast(AndFormula, data['formula'])
        left_formula = cast(AtomicFormula, formula['left'])
        right_formula = cast(AndFormula, formula['right'])
        assert left_formula['operator'] == 'atomic'
        assert right_formula['operator'] == 'and'

    def test_serialization_preserves_values(self):
        """Serialization preserves all values correctly"""
        prop = Signal("Voltage").between(11.5, 14.5).for_at_least(1000)
        data = cast(MetricAlwaysFormula, prop.to_dict())

        assert data['timebound'] == 1000
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['min'] == 11.5
        assert formula['predicate']['max'] == 14.5


# ============================================================================
# EDGE CASES AND ERROR CONDITIONS
# ============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""

    def test_signal_with_unicode_name(self):
        """Signal names can contain unicode (validation in Agda)"""
        sig = Signal("Tür_Öffnen")
        pred = sig.equals(1)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula['predicate']['signal'] == "Tür_Öffnen"

    def test_signal_with_special_chars(self):
        """Signal names can contain special characters"""
        sig = Signal("CAN_Bus$Status#1")
        assert sig.name == "CAN_Bus$Status#1"

    def test_zero_comparison(self):
        """Zero is a valid comparison value"""
        pred = Signal("Speed").equals(0)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula['predicate']['value'] == 0

    def test_negative_delta(self):
        """Negative delta for changed_by works"""
        pred = Signal("Speed").changed_by(-10)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula['predicate']['delta'] == -10

    def test_fractional_values(self):
        """Fractional values work in comparisons"""
        pred = Signal("Voltage").equals(12.65)
        formula = cast(AtomicFormula, pred.to_formula())
        assert formula['predicate']['value'] == 12.65

    def test_very_large_time_bound(self):
        """Very large time bounds work"""
        prop = Signal("X").equals(1).within(999999999)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['timebound'] == 999999999

    def test_chaining_same_operators(self):
        """Chaining same operator multiple times"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)
        d = Signal("D").equals(1)

        result = a.and_(b).and_(c).and_(d)
        formula = cast(AndFormula, result.to_formula())
        assert formula['operator'] == 'and'

    def test_property_methods_return_new_objects(self):
        """Property methods return new objects (immutable)"""
        base = Signal("Speed").less_than(100)
        prop1 = base.always()
        prop2 = base.eventually()

        assert prop1 is not prop2
        data1 = prop1.to_dict()
        data2 = prop2.to_dict()
        assert data1['operator'] != data2['operator']


# ============================================================================
# REAL-WORLD EXAMPLES
# ============================================================================

class TestRealWorldExamples:
    """Test real-world automotive property examples"""

    def test_speed_limit(self):
        """Speed must always be under limit"""
        prop = Signal("Speed").less_than(220).always()
        data = cast(AlwaysFormula, prop.to_dict())

        assert data['operator'] == 'always'
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['value'] == 220

    def test_brake_safety(self):
        """Brake pressed implies throttle zero (desugars to or(not, ...))"""
        brake = Signal("BrakePressed").equals(1)
        throttle = Signal("ThrottlePosition").equals(0)
        prop = brake.implies(throttle)

        data = cast(OrFormula, prop.to_dict())
        assert data['operator'] == 'or'

    def test_voltage_range(self):
        """Battery voltage stays in safe range"""
        prop = Signal("BatteryVoltage").between(11.5, 14.5).always()
        data = cast(AlwaysFormula, prop.to_dict())

        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['min'] == 11.5
        assert formula['predicate']['max'] == 14.5

    def test_door_debounce(self):
        """Door closed signal must be stable (debounced)"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['timebound'] == 50

    def test_emergency_brake(self):
        """Emergency brake -> Speed decreases quickly (desugars to or)"""
        emergency = Signal("EmergencyBrake").equals(1)
        speed_dec = Signal("Speed").changed_by(-20).within(200)
        prop = emergency.implies(speed_dec)

        data = cast(OrFormula, prop.to_dict())
        consequent = cast(MetricEventuallyFormula, data['right'])
        assert consequent['timebound'] == 200

    def test_gear_sequence(self):
        """Gear in park until ignition on"""
        park = Signal("Gear").equals(0).always()
        ignition = Signal("Ignition").equals(1).eventually()
        prop = park.until(ignition)

        data = cast(UntilFormula, prop.to_dict())
        assert data['operator'] == 'until'

    def test_multi_error_detection(self):
        """Multiple error codes can never occur (desugars to always(not(...)))"""
        err1 = Signal("ErrorCode1").equals(0xFF).never()
        err2 = Signal("ErrorCode2").equals(0xFF).never()
        prop = err1.and_(err2)

        data = cast(AndFormula, prop.to_dict())
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(AlwaysFormula, data['right'])
        # never desugars to always(not(...))
        assert left_data['operator'] == 'always'
        assert right_data['operator'] == 'always'
        left_not = cast(NotFormula, left_data['formula'])
        right_not = cast(NotFormula, right_data['formula'])
        assert left_not['operator'] == 'not'
        assert right_not['operator'] == 'not'

    def test_turn_signal_pattern(self):
        """Turn signal blinks regularly (simplified)"""
        on = Signal("LeftTurnSignal").equals(1)
        off = Signal("LeftTurnSignal").equals(0)
        # Simplified: on implies off within 500ms (desugars to or)
        prop = on.implies(off.within(500))

        data = cast(OrFormula, prop.to_dict())
        consequent = cast(MetricEventuallyFormula, data['right'])
        assert consequent['timebound'] == 500

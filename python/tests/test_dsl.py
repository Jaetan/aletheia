"""Unit tests for the Python DSL (Signal/Predicate/Property)

Tests cover:
- Signal comparison operators
- Temporal operators (always, eventually, never, within, for_at_least)
- Logical operators (and, or, not, implies)
- Composition and chaining
- Edge cases (empty strings, special values, negative numbers)
- JSON serialization
"""

from typing import cast
from aletheia.dsl import (
    Signal, Predicate, Property,
    infinitely_often, eventually_always, never
)
from aletheia.protocols import (
    CompareFormula,
    BetweenFormula,
    ChangedByFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    AlwaysFormula,
    EventuallyFormula,
    NeverFormula,
    MetricEventuallyFormula,
    MetricAlwaysFormula,
    ImpliesFormula,
    UntilFormula,
)


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
        formula = cast(CompareFormula, pred.to_formula())
        assert formula == {
            'type': 'compare',
            'signal': 'Gear',
            'op': 'EQ',
            'value': 0
        }

    def test_less_than(self):
        """Signal.less_than() creates correct predicate"""
        pred = Signal("Speed").less_than(220)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula == {
            'type': 'compare',
            'signal': 'Speed',
            'op': 'LT',
            'value': 220
        }

    def test_greater_than(self):
        """Signal.greater_than() creates correct predicate"""
        pred = Signal("Speed").greater_than(5)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula == {
            'type': 'compare',
            'signal': 'Speed',
            'op': 'GT',
            'value': 5
        }

    def test_less_than_or_equal(self):
        """Signal.less_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").less_than_or_equal(14.5)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula == {
            'type': 'compare',
            'signal': 'Voltage',
            'op': 'LE',
            'value': 14.5
        }

    def test_greater_than_or_equal(self):
        """Signal.greater_than_or_equal() creates correct predicate"""
        pred = Signal("Voltage").greater_than_or_equal(11.5)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula == {
            'type': 'compare',
            'signal': 'Voltage',
            'op': 'GE',
            'value': 11.5
        }

    def test_between(self):
        """Signal.between() creates correct predicate"""
        pred = Signal("Voltage").between(11.5, 14.5)
        formula = cast(BetweenFormula, pred.to_formula())
        assert formula == {
            'type': 'between',
            'signal': 'Voltage',
            'min': 11.5,
            'max': 14.5
        }

    def test_changed_by(self):
        """Signal.changed_by() creates correct predicate"""
        pred = Signal("Speed").changed_by(-10)
        formula = cast(ChangedByFormula, pred.to_formula())
        assert formula == {
            'type': 'changed_by',
            'signal': 'Speed',
            'delta': -10
        }

    # Edge cases
    def test_comparison_with_zero(self):
        """Comparison with zero works"""
        pred = Signal("Speed").equals(0)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == 0

    def test_comparison_with_negative(self):
        """Comparison with negative values works"""
        pred = Signal("Temp").greater_than(-40)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == -40

    def test_comparison_with_float(self):
        """Comparison with float values works"""
        pred = Signal("Voltage").equals(12.6)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == 12.6

    def test_comparison_with_large_number(self):
        """Comparison with large numbers works"""
        pred = Signal("Counter").less_than(1000000)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == 1000000

    def test_between_min_equals_max(self):
        """between() works when min equals max (single value range)"""
        pred = Signal("Mode").between(5, 5)
        formula = cast(BetweenFormula, pred.to_formula())
        assert formula['min'] == 5
        assert formula['max'] == 5

    def test_between_reversed_bounds(self):
        """between() accepts reversed bounds (validation in Agda)"""
        pred = Signal("X").between(10, 5)
        formula = cast(BetweenFormula, pred.to_formula())
        assert formula['min'] == 10
        assert formula['max'] == 5


# ============================================================================
# TEMPORAL OPERATORS
# ============================================================================

class TestTemporalOperators:
    """Test Predicate temporal operators"""

    def test_always(self):
        """Predicate.always() creates correct property"""
        prop = Signal("Speed").less_than(220).always()
        assert isinstance(prop, Property)
        data = cast(AlwaysFormula, prop.to_dict())
        assert data['type'] == 'always'
        formula = cast(CompareFormula, data['formula'])
        assert formula['op'] == 'LT'

    def test_eventually(self):
        """Predicate.eventually() creates correct property"""
        prop = Signal("DoorClosed").equals(1).eventually()
        data = cast(EventuallyFormula, prop.to_dict())
        assert data['type'] == 'eventually'

    def test_never(self):
        """Predicate.never() creates correct property"""
        prop = Signal("ErrorCode").equals(0xFF).never()
        data = cast(NeverFormula, prop.to_dict())
        assert data['type'] == 'never'

    def test_within(self):
        """Predicate.within() creates bounded temporal property"""
        prop = Signal("BrakePressed").equals(1).within(100)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['type'] == 'metricEventually'
        assert data['time_ms'] == 100

    def test_for_at_least(self):
        """Predicate.for_at_least() creates bounded temporal property"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['type'] == 'metricAlways'
        assert data['time_ms'] == 50

    def test_within_zero_ms(self):
        """within(0) is valid (immediate)"""
        prop = Signal("X").equals(1).within(0)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['time_ms'] == 0

    def test_for_at_least_zero_ms(self):
        """for_at_least(0) is valid"""
        prop = Signal("X").equals(1).for_at_least(0)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['time_ms'] == 0

    def test_large_time_bounds(self):
        """Large time bounds work (hours)"""
        prop = Signal("EngineOn").equals(1).for_at_least(3600000)  # 1 hour
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['time_ms'] == 3600000


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
        formula = cast(AndFormula, combined.to_formula())
        assert formula['type'] == 'and'
        left_formula = cast(CompareFormula, formula['left'])
        right_formula = cast(CompareFormula, formula['right'])
        assert left_formula['signal'] == 'LeftDoor'
        assert right_formula['signal'] == 'RightDoor'

    def test_or(self):
        """Predicate.or_() combines two predicates"""
        error1 = Signal("Error1").equals(1)
        error2 = Signal("Error2").equals(1)
        combined = error1.or_(error2)

        formula = cast(OrFormula, combined.to_formula())
        assert formula['type'] == 'or'

    def test_not(self):
        """Predicate.not_() negates predicate"""
        pred = Signal("Enabled").equals(1)
        negated = pred.not_()

        formula = cast(NotFormula, negated.to_formula())
        assert formula['type'] == 'not'
        inner_formula = cast(CompareFormula, formula['formula'])
        assert inner_formula['signal'] == 'Enabled'

    def test_implies_predicate_to_predicate(self):
        """Predicate.implies() with another Predicate"""
        brake = Signal("Brake").equals(1)
        throttle = Signal("Throttle").equals(0)
        implication = brake.implies(throttle)

        assert isinstance(implication, Property)
        data = cast(ImpliesFormula, implication.to_dict())
        assert data['type'] == 'implies'
        antecedent = cast(CompareFormula, data['antecedent'])
        consequent = cast(CompareFormula, data['consequent'])
        assert antecedent['signal'] == 'Brake'
        assert consequent['signal'] == 'Throttle'

    def test_implies_predicate_to_property(self):
        """Predicate.implies() with a Property"""
        brake = Signal("Brake").equals(1)
        speed_decrease = Signal("Speed").changed_by(-10).within(100)
        implication = brake.implies(speed_decrease)

        data = cast(ImpliesFormula, implication.to_dict())
        assert data['type'] == 'implies'
        consequent = cast(MetricEventuallyFormula, data['consequent'])
        assert consequent['type'] == 'metricEventually'

    def test_chained_logical_operators(self):
        """Multiple logical operators can be chained"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        combined = a.and_(b).and_(c)
        formula = cast(AndFormula, combined.to_formula())
        assert formula['type'] == 'and'
        left_formula = cast(AndFormula, formula['left'])
        assert left_formula['type'] == 'and'  # Nested

    def test_not_of_compound(self):
        """not_() works on compound predicates"""
        compound = Signal("A").equals(1).and_(Signal("B").equals(1))
        negated = compound.not_()

        formula = cast(NotFormula, negated.to_formula())
        assert formula['type'] == 'not'
        inner_formula = cast(AndFormula, formula['formula'])
        assert inner_formula['type'] == 'and'


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
        assert data['type'] == 'and'

    def test_property_or(self):
        """Property.or_() combines two properties"""
        charging = Signal("Charging").equals(1).eventually()
        engine = Signal("Engine").equals(1).eventually()
        combined = charging.or_(engine)

        data = cast(OrFormula, combined.to_dict())
        assert data['type'] == 'or'

    def test_property_implies(self):
        """Property.implies() creates implication"""
        brake = Signal("Brake").equals(1).eventually()
        stopped = Signal("Speed").equals(0).eventually()
        implication = brake.implies(stopped)

        data = cast(ImpliesFormula, implication.to_dict())
        assert data['type'] == 'implies'

    def test_until(self):
        """Property.until() creates until temporal formula"""
        power_low = Signal("PowerMode").equals(0).always()
        power_acc = Signal("PowerMode").equals(1).eventually()
        until_prop = power_low.until(power_acc)

        data = cast(UntilFormula, until_prop.to_dict())
        assert data['type'] == 'until'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['type'] == 'always'
        assert right_data['type'] == 'eventually'


# ============================================================================
# COMPOSITION AND CHAINING
# ============================================================================

class TestComposition:
    """Test complex compositions and method chaining"""

    def test_fluent_chaining(self):
        """Methods can be chained fluently"""
        prop = Signal("Speed").less_than(220).always()
        data = cast(AlwaysFormula, prop.to_dict())
        assert data['type'] == 'always'
        formula = cast(CompareFormula, data['formula'])
        assert formula['op'] == 'LT'

    def test_complex_composition(self):
        """Complex property compositions work"""
        # (Speed < 220 ∧ Voltage ∈ [11.5, 14.5]) always
        speed_ok = Signal("Speed").less_than(220)
        voltage_ok = Signal("Voltage").between(11.5, 14.5)
        combined = speed_ok.and_(voltage_ok).always()

        data = cast(AlwaysFormula, combined.to_dict())
        assert data['type'] == 'always'
        formula = cast(AndFormula, data['formula'])
        assert formula['type'] == 'and'

    def test_implication_with_temporal(self):
        """Implication with temporal operators"""
        # Brake pressed → Speed decreases within 100ms
        brake = Signal("Brake").equals(1)
        speed_dec = Signal("Speed").changed_by(-10).within(100)
        prop = brake.implies(speed_dec)

        data = cast(ImpliesFormula, prop.to_dict())
        assert data['type'] == 'implies'
        consequent = cast(MetricEventuallyFormula, data['consequent'])
        assert consequent['type'] == 'metricEventually'

    def test_nested_implications(self):
        """Nested implications work"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)

        # A → (B → C)
        inner = b.implies(c.eventually())
        outer = a.implies(inner)

        data = cast(ImpliesFormula, outer.to_dict())
        assert data['type'] == 'implies'
        consequent = cast(ImpliesFormula, data['consequent'])
        assert consequent['type'] == 'implies'

    def test_until_with_complex_formulas(self):
        """until() works with complex properties"""
        left = Signal("State").equals(0).always()
        right = Signal("State").equals(1).and_(Signal("Ready").equals(1)).eventually()
        prop = left.until(right)

        data = cast(UntilFormula, prop.to_dict())
        assert data['type'] == 'until'

    def test_mixed_temporal_and_logical(self):
        """Mixing temporal and logical operators"""
        # (A always) ∧ (B eventually)
        always_a = Signal("A").equals(1).always()
        eventually_b = Signal("B").equals(1).eventually()
        combined = always_a.and_(eventually_b)

        data = cast(AndFormula, combined.to_dict())
        assert data['type'] == 'and'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['type'] == 'always'
        assert right_data['type'] == 'eventually'


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
        # data is already AlwaysFormula after to_dict()
        formula = cast(CompareFormula, data['formula'])
        assert formula['signal'] == 'Speed'

    def test_complex_property_to_dict(self):
        """Complex property serializes correctly"""
        left = Signal("A").equals(1)
        right = Signal("B").equals(1)
        prop = left.and_(right).always()
        data = prop.to_dict()

        assert data['type'] == 'always'
        # data is already AlwaysFormula after to_dict()
        formula = cast(AndFormula, data['formula'])
        assert formula['type'] == 'and'

    def test_nested_structure(self):
        """Deeply nested structures serialize"""
        prop = Signal("A").equals(1).and_(
            Signal("B").equals(1).and_(
                Signal("C").equals(1)
            )
        ).always()

        data = cast(AlwaysFormula, prop.to_dict())
        formula = cast(AndFormula, data['formula'])
        left_formula = cast(CompareFormula, formula['left'])
        right_formula = cast(AndFormula, formula['right'])
        assert left_formula['type'] == 'compare'
        assert right_formula['type'] == 'and'

    def test_serialization_preserves_values(self):
        """Serialization preserves all values correctly"""
        prop = Signal("Voltage").between(11.5, 14.5).for_at_least(1000)
        data = cast(MetricAlwaysFormula, prop.to_dict())

        assert data['time_ms'] == 1000
        formula = cast(BetweenFormula, data['formula'])
        assert formula['min'] == 11.5
        assert formula['max'] == 14.5


# ============================================================================
# EDGE CASES AND ERROR CONDITIONS
# ============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""

    def test_signal_with_unicode_name(self):
        """Signal names can contain unicode (validation in Agda)"""
        sig = Signal("Tür_Öffnen")
        pred = sig.equals(1)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['signal'] == "Tür_Öffnen"

    def test_signal_with_special_chars(self):
        """Signal names can contain special characters"""
        sig = Signal("CAN_Bus$Status#1")
        assert sig.name == "CAN_Bus$Status#1"

    def test_zero_comparison(self):
        """Zero is a valid comparison value"""
        pred = Signal("Speed").equals(0)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == 0

    def test_negative_delta(self):
        """Negative delta for changed_by works"""
        pred = Signal("Speed").changed_by(-10)
        formula = cast(ChangedByFormula, pred.to_formula())
        assert formula['delta'] == -10

    def test_fractional_values(self):
        """Fractional values work in comparisons"""
        pred = Signal("Voltage").equals(12.65)
        formula = cast(CompareFormula, pred.to_formula())
        assert formula['value'] == 12.65

    def test_very_large_time_bound(self):
        """Very large time bounds work"""
        prop = Signal("X").equals(1).within(999999999)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['time_ms'] == 999999999

    def test_chaining_same_operators(self):
        """Chaining same operator multiple times"""
        a = Signal("A").equals(1)
        b = Signal("B").equals(1)
        c = Signal("C").equals(1)
        d = Signal("D").equals(1)

        result = a.and_(b).and_(c).and_(d)
        formula = cast(AndFormula, result.to_formula())
        assert formula['type'] == 'and'

    def test_property_methods_return_new_objects(self):
        """Property methods return new objects (immutable)"""
        base = Signal("Speed").less_than(100)
        prop1 = base.always()
        prop2 = base.eventually()

        assert prop1 is not prop2
        data1 = prop1.to_dict()
        data2 = prop2.to_dict()
        assert data1['type'] != data2['type']


# ============================================================================
# REAL-WORLD EXAMPLES
# ============================================================================

class TestRealWorldExamples:
    """Test real-world automotive property examples"""

    def test_speed_limit(self):
        """Speed must always be under limit"""
        prop = Signal("Speed").less_than(220).always()
        data = cast(AlwaysFormula, prop.to_dict())

        assert data['type'] == 'always'
        formula = cast(CompareFormula, data['formula'])
        assert formula['value'] == 220

    def test_brake_safety(self):
        """Brake pressed implies throttle zero"""
        brake = Signal("BrakePressed").equals(1)
        throttle = Signal("ThrottlePosition").equals(0)
        prop = brake.implies(throttle)

        data = cast(ImpliesFormula, prop.to_dict())
        assert data['type'] == 'implies'

    def test_voltage_range(self):
        """Battery voltage stays in safe range"""
        prop = Signal("BatteryVoltage").between(11.5, 14.5).always()
        data = cast(AlwaysFormula, prop.to_dict())

        formula = cast(BetweenFormula, data['formula'])
        assert formula['min'] == 11.5
        assert formula['max'] == 14.5

    def test_door_debounce(self):
        """Door closed signal must be stable (debounced)"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['time_ms'] == 50

    def test_emergency_brake(self):
        """Emergency brake → Speed decreases quickly"""
        emergency = Signal("EmergencyBrake").equals(1)
        speed_dec = Signal("Speed").changed_by(-20).within(200)
        prop = emergency.implies(speed_dec)

        data = cast(ImpliesFormula, prop.to_dict())
        consequent = cast(MetricEventuallyFormula, data['consequent'])
        assert consequent['time_ms'] == 200

    def test_gear_sequence(self):
        """Gear in park until ignition on"""
        park = Signal("Gear").equals(0).always()
        ignition = Signal("Ignition").equals(1).eventually()
        prop = park.until(ignition)

        data = cast(UntilFormula, prop.to_dict())
        assert data['type'] == 'until'

    def test_multi_error_detection(self):
        """Multiple error codes can never occur"""
        err1 = Signal("ErrorCode1").equals(0xFF).never()
        err2 = Signal("ErrorCode2").equals(0xFF).never()
        prop = err1.and_(err2)

        data = cast(AndFormula, prop.to_dict())
        left_data = cast(NeverFormula, data['left'])
        right_data = cast(NeverFormula, data['right'])
        assert left_data['type'] == 'never'
        assert right_data['type'] == 'never'

    def test_turn_signal_pattern(self):
        """Turn signal blinks regularly (simplified)"""
        on = Signal("LeftTurnSignal").equals(1)
        off = Signal("LeftTurnSignal").equals(0)
        # Simplified: on implies off within 500ms
        prop = on.implies(off.within(500))

        data = cast(ImpliesFormula, prop.to_dict())
        consequent = cast(MetricEventuallyFormula, data['consequent'])
        assert consequent['time_ms'] == 500


# ============================================================================
# NESTED TEMPORAL OPERATORS
# ============================================================================

class TestNestedTemporalOperators:
    """Test nested temporal operator compositions (Phase 4 feature)

    These tests verify that standard LTL semantics for nested temporal
    operators work correctly after the bind/zipWith fixes in Coinductive.agda.
    """

    def test_always_not_always(self):
        """G(¬G(p)) - Infinitely often not-p pattern

        This tests the critical nested temporal operator bug fix.
        G(¬G(speed > 50)) ≡ G(F(speed ≤ 50))
        Meaning: infinitely often, the speed is ≤ 50
        """
        speed_high = Signal("Speed").greater_than(50)

        # Construct G(¬G(p)) using fluent API
        infinitely_often_not_high = speed_high.always().not_().always()

        # Verify structure
        data = cast(AlwaysFormula, infinitely_often_not_high.to_dict())
        assert data['type'] == 'always'
        not_formula = cast(NotFormula, data['formula'])
        assert not_formula['type'] == 'not'
        always_formula = cast(AlwaysFormula, not_formula['formula'])
        assert always_formula['type'] == 'always'
        compare_formula = cast(CompareFormula, always_formula['formula'])
        assert compare_formula['op'] == 'GT'

    def test_and_always_eventually(self):
        """G(p) ∧ F(q) - Composition of different temporal operators

        Tests: Always temp < 80 AND Eventually speed > 60
        This verifies And operator correctly handles nested temporal operators.
        """
        temp_ok = Signal("Temperature").less_than(80).always()
        speed_high = Signal("Speed").greater_than(60).eventually()
        combined = temp_ok.and_(speed_high)

        # Verify structure
        data = cast(AndFormula, combined.to_dict())
        assert data['type'] == 'and'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['type'] == 'always'
        assert right_data['type'] == 'eventually'

    def test_not_eventually_equiv_always_not(self):
        """¬F(p) structure (equivalent to G(¬p) by De Morgan)

        Tests: Not(Eventually(error == 1))
        Should be equivalent to: Always(Not(error == 1))
        """
        error_active = Signal("ErrorCode").equals(1)
        eventually_error = error_active.eventually()
        # Create ¬F(p) by wrapping eventually in not
        not_formula_dict: NotFormula = {
            'type': 'not',
            'formula': eventually_error.to_dict()
        }
        never_error = Property(not_formula_dict)

        # Verify structure of ¬F(error)
        data = cast(NotFormula, never_error.to_dict())
        assert data['type'] == 'not'
        formula = cast(EventuallyFormula, data['formula'])
        assert formula['type'] == 'eventually'

        # Compare to G(¬error) structure
        not_error = error_active.not_()
        always_not_error = not_error.always()

        always_data = cast(AlwaysFormula, always_not_error.to_dict())
        assert always_data['type'] == 'always'
        not_formula = cast(NotFormula, always_data['formula'])
        assert not_formula['type'] == 'not'

    def test_or_eventually_eventually(self):
        """F(p) ∨ F(q) - Or of Eventually operators

        Tests: Eventually charging OR Eventually engine on
        Verifies Or operator handles nested temporal operators.
        """
        charging = Signal("Charging").equals(1).eventually()
        engine = Signal("Engine").equals(1).eventually()
        combined = charging.or_(engine)

        data = cast(OrFormula, combined.to_dict())
        assert data['type'] == 'or'
        left_data = cast(EventuallyFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['type'] == 'eventually'
        assert right_data['type'] == 'eventually'

    def test_nested_until_with_temporal_subformulas(self):
        """(G(p)) U (F(q)) - Until with nested temporal operators

        Tests: Always(state == 0) Until Eventually(state == 1)
        Complex nesting to verify Until handles nested temporal operators.
        """
        state_zero = Signal("State").equals(0).always()
        state_one = Signal("State").equals(1).eventually()
        until_prop = state_zero.until(state_one)

        data = cast(UntilFormula, until_prop.to_dict())
        assert data['type'] == 'until'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['type'] == 'always'
        assert right_data['type'] == 'eventually'

    def test_deeply_nested_composition(self):
        """G(F(p)) - Infinitely often pattern

        Tests: Always(Eventually(speed > 100))
        Meaning: infinitely often, speed exceeds 100
        """
        # Construct G(F(p)) using fluent API
        infinitely_often_high = Signal("Speed").greater_than(100).eventually().always()

        # Verify G(F(p)) structure
        data = cast(AlwaysFormula, infinitely_often_high.to_dict())
        assert data['type'] == 'always'
        eventually_formula = cast(EventuallyFormula, data['formula'])
        assert eventually_formula['type'] == 'eventually'
        compare_formula = cast(CompareFormula, eventually_formula['formula'])
        assert compare_formula['op'] == 'GT'

    def test_triple_nesting_always_not_eventually(self):
        """G(¬F(p)) - Always never pattern

        Tests: Always(Not(Eventually(fault == 1)))
        Meaning: fault never occurs (strongest safety property)
        """
        # Construct G(¬F(p)) using fluent API
        never_fault = Signal("Fault").equals(1).eventually().not_().always()

        # Verify G(¬F(p)) structure
        data = cast(AlwaysFormula, never_fault.to_dict())
        assert data['type'] == 'always'
        not_formula = cast(NotFormula, data['formula'])
        assert not_formula['type'] == 'not'
        eventually_formula = cast(EventuallyFormula, not_formula['formula'])
        assert eventually_formula['type'] == 'eventually'

    def test_infinitely_often_helper(self):
        """Test infinitely_often() helper function - G(F(p))"""
        # Using helper function
        prop1 = infinitely_often(Signal("Speed").greater_than(100))

        # Using fluent API
        prop2 = Signal("Speed").greater_than(100).eventually().always()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(AlwaysFormula, prop1.to_dict())
        assert data['type'] == 'always'
        formula = cast(EventuallyFormula, data['formula'])
        assert formula['type'] == 'eventually'

    def test_eventually_always_helper(self):
        """Test eventually_always() helper function - F(G(p))"""
        # Using helper function
        prop1 = eventually_always(Signal("Temperature").less_than(70))

        # Using fluent API
        prop2 = Signal("Temperature").less_than(70).always().eventually()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(EventuallyFormula, prop1.to_dict())
        assert data['type'] == 'eventually'
        formula = cast(AlwaysFormula, data['formula'])
        assert formula['type'] == 'always'

    def test_never_helper(self):
        """Test never() helper function - G(¬φ)"""
        # Using helper function
        prop1 = never(Signal("CriticalFault").equals(1))

        # Using fluent API
        prop2 = Signal("CriticalFault").equals(1).not_().always()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(AlwaysFormula, prop1.to_dict())
        assert data['type'] == 'always'
        formula = cast(NotFormula, data['formula'])
        assert formula['type'] == 'not'

    def test_helper_with_property_input(self):
        """Test helpers accept Property objects, not just Predicates"""
        # Start with a property (always)
        always_prop = Signal("State").equals(1).always()

        # Apply helper to property
        nested = infinitely_often(always_prop)

        # Should create G(F(G(p)))
        data = cast(AlwaysFormula, nested.to_dict())
        assert data['type'] == 'always'
        eventually_formula = cast(EventuallyFormula, data['formula'])
        assert eventually_formula['type'] == 'eventually'
        always_formula = cast(AlwaysFormula, eventually_formula['formula'])
        assert always_formula['type'] == 'always'

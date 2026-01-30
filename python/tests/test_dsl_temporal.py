"""Unit tests for the Python DSL - Temporal Operators

Tests cover:
- Basic temporal operators (always, eventually, never, within, for_at_least)
- Next operator
- Release operator
- Metric Until and Metric Release operators
- Nested temporal operator compositions
"""

from typing import cast
from aletheia.dsl import (
    Signal, Property,
    infinitely_often, eventually_always, never
)
from aletheia.protocols import (
    AtomicFormula,
    AlwaysFormula,
    EventuallyFormula,
    NextFormula,
    NotFormula,
    MetricEventuallyFormula,
    MetricAlwaysFormula,
    UntilFormula,
    ReleaseFormula,
    MetricUntilFormula,
    MetricReleaseFormula,
    AndFormula,
    OrFormula,
)


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
        assert data['operator'] == 'always'
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['predicate'] == 'lessThan'

    def test_eventually(self):
        """Predicate.eventually() creates correct property"""
        prop = Signal("DoorClosed").equals(1).eventually()
        data = cast(EventuallyFormula, prop.to_dict())
        assert data['operator'] == 'eventually'

    def test_never(self):
        """Predicate.never() desugars to always(not(...))"""
        prop = Signal("ErrorCode").equals(0xFF).never()
        data = cast(AlwaysFormula, prop.to_dict())
        assert data['operator'] == 'always'
        not_formula = cast(NotFormula, data['formula'])
        assert not_formula['operator'] == 'not'
        inner = cast(AtomicFormula, not_formula['formula'])
        assert inner['operator'] == 'atomic'

    def test_within(self):
        """Predicate.within() creates bounded temporal property"""
        prop = Signal("BrakePressed").equals(1).within(100)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['operator'] == 'metricEventually'
        assert data['timebound'] == 100

    def test_for_at_least(self):
        """Predicate.for_at_least() creates bounded temporal property"""
        prop = Signal("DoorClosed").equals(1).for_at_least(50)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['operator'] == 'metricAlways'
        assert data['timebound'] == 50

    def test_within_zero_ms(self):
        """within(0) is valid (immediate)"""
        prop = Signal("X").equals(1).within(0)
        data = cast(MetricEventuallyFormula, prop.to_dict())
        assert data['timebound'] == 0

    def test_for_at_least_zero_ms(self):
        """for_at_least(0) is valid"""
        prop = Signal("X").equals(1).for_at_least(0)
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['timebound'] == 0

    def test_large_time_bounds(self):
        """Large time bounds work (hours)"""
        prop = Signal("EngineOn").equals(1).for_at_least(3600000)  # 1 hour
        data = cast(MetricAlwaysFormula, prop.to_dict())
        assert data['timebound'] == 3600000


# ============================================================================
# NEXT OPERATOR
# ============================================================================

class TestNextOperator:
    """Test Next operator (with warnings about brittleness)"""

    def test_predicate_next(self):
        """Predicate.next() creates NextFormula"""
        prop = Signal("Speed").less_than(100).next()
        assert isinstance(prop, Property)
        data = cast(NextFormula, prop.to_dict())
        assert data['operator'] == 'next'
        formula = cast(AtomicFormula, data['formula'])
        assert formula['predicate']['signal'] == 'Speed'
        assert formula['predicate']['predicate'] == 'lessThan'
        assert formula['predicate']['value'] == 100

    def test_property_next(self):
        """Property.next() creates nested Next formula"""
        prop = Signal("State").equals(1).always().next()
        data = cast(NextFormula, prop.to_dict())
        assert data['operator'] == 'next'
        always_formula = cast(AlwaysFormula, data['formula'])
        assert always_formula['operator'] == 'always'

    def test_next_chaining(self):
        """Multiple Next operators chain correctly"""
        prop = Signal("X").equals(1).next().next()
        data = cast(NextFormula, prop.to_dict())
        assert data['operator'] == 'next'
        inner = cast(NextFormula, data['formula'])
        assert inner['operator'] == 'next'
        innermost = cast(AtomicFormula, inner['formula'])
        assert innermost['predicate']['signal'] == 'X'


# ============================================================================
# RELEASE OPERATOR
# ============================================================================

class TestReleaseOperator:
    """Test Release operator (dual of Until)"""

    def test_release_basic(self):
        """Property.release() creates ReleaseFormula"""
        left = Signal("Brake").equals(1).always()
        right = Signal("Ignition").equals(0).always()
        prop = left.release(right)

        data = cast(ReleaseFormula, prop.to_dict())
        assert data['operator'] == 'release'
        assert 'left' in data
        assert 'right' in data

    def test_release_semantics(self):
        """Release operator: right holds until left releases it"""
        ignition_on = Signal("Ignition").equals(1).eventually()
        brake_engaged = Signal("Brake").equals(1).always()
        prop = ignition_on.release(brake_engaged)

        data = cast(ReleaseFormula, prop.to_dict())
        assert data['operator'] == 'release'
        left_formula = cast(EventuallyFormula, data['left'])
        assert left_formula['operator'] == 'eventually'
        right_formula = cast(AlwaysFormula, data['right'])
        assert right_formula['operator'] == 'always'


# ============================================================================
# METRIC UNTIL OPERATOR
# ============================================================================

class TestMetricUntilOperator:
    """Test Metric Until operator (time-bounded until)"""

    def test_metric_until_basic(self):
        """Property.metric_until() creates MetricUntilFormula"""
        speed_ok = Signal("Speed").greater_than(50).always()
        brake = Signal("Brake").equals(1).eventually()
        prop = speed_ok.metric_until(1000, brake)

        data = cast(MetricUntilFormula, prop.to_dict())
        assert data['operator'] == 'metricUntil'
        assert data['timebound'] == 1000
        assert 'left' in data
        assert 'right' in data

    def test_metric_until_zero_time(self):
        """metric_until with 0ms is valid"""
        left = Signal("A").equals(1).always()
        right = Signal("B").equals(1).eventually()
        prop = left.metric_until(0, right)

        data = cast(MetricUntilFormula, prop.to_dict())
        assert data['timebound'] == 0

    def test_metric_until_large_time(self):
        """metric_until with large time bound (1 hour)"""
        left = Signal("X").equals(1).always()
        right = Signal("Y").equals(1).eventually()
        prop = left.metric_until(3600000, right)

        data = cast(MetricUntilFormula, prop.to_dict())
        assert data['timebound'] == 3600000


# ============================================================================
# METRIC RELEASE OPERATOR
# ============================================================================

class TestMetricReleaseOperator:
    """Test Metric Release operator (time-bounded release)"""

    def test_metric_release_basic(self):
        """Property.metric_release() creates MetricReleaseFormula"""
        ignition = Signal("Ignition").equals(1).eventually()
        brake = Signal("Brake").equals(1).always()
        prop = ignition.metric_release(5000, brake)

        data = cast(MetricReleaseFormula, prop.to_dict())
        assert data['operator'] == 'metricRelease'
        assert data['timebound'] == 5000
        assert 'left' in data
        assert 'right' in data

    def test_metric_release_edge_cases(self):
        """Metric release with edge case time bounds"""
        left = Signal("A").equals(1).eventually()
        right = Signal("B").equals(1).always()

        # Zero time
        prop_zero = left.metric_release(0, right)
        data_zero = cast(MetricReleaseFormula, prop_zero.to_dict())
        assert data_zero['timebound'] == 0

        # Large time (24 hours)
        prop_large = left.metric_release(86400000, right)
        data_large = cast(MetricReleaseFormula, prop_large.to_dict())
        assert data_large['timebound'] == 86400000


# ============================================================================
# NESTED TEMPORAL OPERATORS
# ============================================================================

class TestNestedTemporalOperators:
    """Test nested temporal operator compositions (Phase 4 feature)

    These tests verify that standard LTL semantics for nested temporal
    operators work correctly after the bind/zipWith fixes in Coinductive.agda.
    """

    def test_always_not_always(self):
        """G(not G(p)) - Infinitely often not-p pattern

        This tests the critical nested temporal operator bug fix.
        G(not G(speed > 50)) equiv G(F(speed <= 50))
        Meaning: infinitely often, the speed is <= 50
        """
        speed_high = Signal("Speed").greater_than(50)

        # Construct G(not G(p)) using fluent API
        infinitely_often_not_high = speed_high.always().not_().always()

        # Verify structure
        data = cast(AlwaysFormula, infinitely_often_not_high.to_dict())
        assert data['operator'] == 'always'
        not_formula = cast(NotFormula, data['formula'])
        assert not_formula['operator'] == 'not'
        always_formula = cast(AlwaysFormula, not_formula['formula'])
        assert always_formula['operator'] == 'always'
        compare_formula = cast(AtomicFormula, always_formula['formula'])
        assert compare_formula['predicate']['predicate'] == 'greaterThan'

    def test_and_always_eventually(self):
        """G(p) AND F(q) - Composition of different temporal operators

        Tests: Always temp < 80 AND Eventually speed > 60
        This verifies And operator correctly handles nested temporal operators.
        """
        temp_ok = Signal("Temperature").less_than(80).always()
        speed_high = Signal("Speed").greater_than(60).eventually()
        combined = temp_ok.and_(speed_high)

        # Verify structure
        data = cast(AndFormula, combined.to_dict())
        assert data['operator'] == 'and'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['operator'] == 'always'
        assert right_data['operator'] == 'eventually'

    def test_not_eventually_equiv_always_not(self):
        """not F(p) structure (equivalent to G(not p) by De Morgan)

        Tests: Not(Eventually(error == 1))
        Should be equivalent to: Always(Not(error == 1))
        """
        error_active = Signal("ErrorCode").equals(1)
        eventually_error = error_active.eventually()
        # Create not F(p) by wrapping eventually in not
        not_formula_dict: NotFormula = {
            'operator': 'not',
            'formula': eventually_error.to_dict()
        }
        never_error = Property(not_formula_dict)

        # Verify structure of not F(error)
        data = cast(NotFormula, never_error.to_dict())
        assert data['operator'] == 'not'
        formula = cast(EventuallyFormula, data['formula'])
        assert formula['operator'] == 'eventually'

        # Compare to G(not error) structure
        not_error = error_active.not_()
        always_not_error = not_error.always()

        always_data = cast(AlwaysFormula, always_not_error.to_dict())
        assert always_data['operator'] == 'always'
        not_formula = cast(NotFormula, always_data['formula'])
        assert not_formula['operator'] == 'not'

    def test_or_eventually_eventually(self):
        """F(p) OR F(q) - Or of Eventually operators

        Tests: Eventually charging OR Eventually engine on
        Verifies Or operator handles nested temporal operators.
        """
        charging = Signal("Charging").equals(1).eventually()
        engine = Signal("Engine").equals(1).eventually()
        combined = charging.or_(engine)

        data = cast(OrFormula, combined.to_dict())
        assert data['operator'] == 'or'
        left_data = cast(EventuallyFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['operator'] == 'eventually'
        assert right_data['operator'] == 'eventually'

    def test_nested_until_with_temporal_subformulas(self):
        """(G(p)) U (F(q)) - Until with nested temporal operators

        Tests: Always(state == 0) Until Eventually(state == 1)
        Complex nesting to verify Until handles nested temporal operators.
        """
        state_zero = Signal("State").equals(0).always()
        state_one = Signal("State").equals(1).eventually()
        until_prop = state_zero.until(state_one)

        data = cast(UntilFormula, until_prop.to_dict())
        assert data['operator'] == 'until'
        left_data = cast(AlwaysFormula, data['left'])
        right_data = cast(EventuallyFormula, data['right'])
        assert left_data['operator'] == 'always'
        assert right_data['operator'] == 'eventually'

    def test_deeply_nested_composition(self):
        """G(F(p)) - Infinitely often pattern

        Tests: Always(Eventually(speed > 100))
        Meaning: infinitely often, speed exceeds 100
        """
        # Construct G(F(p)) using fluent API
        infinitely_often_high = Signal("Speed").greater_than(100).eventually().always()

        # Verify G(F(p)) structure
        data = cast(AlwaysFormula, infinitely_often_high.to_dict())
        assert data['operator'] == 'always'
        eventually_formula = cast(EventuallyFormula, data['formula'])
        assert eventually_formula['operator'] == 'eventually'
        compare_formula = cast(AtomicFormula, eventually_formula['formula'])
        assert compare_formula['predicate']['predicate'] == 'greaterThan'

    def test_triple_nesting_always_not_eventually(self):
        """G(not F(p)) - Always never pattern

        Tests: Always(Not(Eventually(fault == 1)))
        Meaning: fault never occurs (strongest safety property)
        """
        # Construct G(not F(p)) using fluent API
        never_fault = Signal("Fault").equals(1).eventually().not_().always()

        # Verify G(not F(p)) structure
        data = cast(AlwaysFormula, never_fault.to_dict())
        assert data['operator'] == 'always'
        not_formula = cast(NotFormula, data['formula'])
        assert not_formula['operator'] == 'not'
        eventually_formula = cast(EventuallyFormula, not_formula['formula'])
        assert eventually_formula['operator'] == 'eventually'

    def test_infinitely_often_helper(self):
        """Test infinitely_often() helper function - G(F(p))"""
        # Using helper function
        prop1 = infinitely_often(Signal("Speed").greater_than(100))

        # Using fluent API
        prop2 = Signal("Speed").greater_than(100).eventually().always()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(AlwaysFormula, prop1.to_dict())
        assert data['operator'] == 'always'
        formula = cast(EventuallyFormula, data['formula'])
        assert formula['operator'] == 'eventually'

    def test_eventually_always_helper(self):
        """Test eventually_always() helper function - F(G(p))"""
        # Using helper function
        prop1 = eventually_always(Signal("Temperature").less_than(70))

        # Using fluent API
        prop2 = Signal("Temperature").less_than(70).always().eventually()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(EventuallyFormula, prop1.to_dict())
        assert data['operator'] == 'eventually'
        formula = cast(AlwaysFormula, data['formula'])
        assert formula['operator'] == 'always'

    def test_never_helper(self):
        """Test never() helper function - G(not phi)"""
        # Using helper function
        prop1 = never(Signal("CriticalFault").equals(1))

        # Using fluent API
        prop2 = Signal("CriticalFault").equals(1).not_().always()

        # Should produce identical structure
        assert prop1.to_dict() == prop2.to_dict()
        data = cast(AlwaysFormula, prop1.to_dict())
        assert data['operator'] == 'always'
        formula = cast(NotFormula, data['formula'])
        assert formula['operator'] == 'not'

    def test_helper_with_property_input(self):
        """Test helpers accept Property objects, not just Predicates"""
        # Start with a property (always)
        always_prop = Signal("State").equals(1).always()

        # Apply helper to property
        nested = infinitely_often(always_prop)

        # Should create G(F(G(p)))
        data = cast(AlwaysFormula, nested.to_dict())
        assert data['operator'] == 'always'
        eventually_formula = cast(EventuallyFormula, data['formula'])
        assert eventually_formula['operator'] == 'eventually'
        always_formula = cast(AlwaysFormula, eventually_formula['formula'])
        assert always_formula['operator'] == 'always'

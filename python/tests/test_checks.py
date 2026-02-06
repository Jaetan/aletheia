"""Unit tests for the Check API (industry-vocabulary wrappers over the DSL)

Tests cover:
- CheckSignal one-shot methods (never_exceeds, never_below, stays_between, never_equals)
- CheckSignal two-step methods (equals().always(), settles_between().within())
- When/Then causal checks with all trigger/response combinations
- Metadata (name, severity) — present on CheckResult, absent from to_dict()
- Equivalence: every Check produces the same formula as the equivalent DSL chain
"""

from aletheia.checks import Check, CheckResult
from aletheia.dsl import Signal, Property


# ============================================================================
# CheckSignal — one-shot methods
# ============================================================================

class TestCheckSignal:
    """Test Check.signal() one-shot convenience methods."""

    def test_never_exceeds(self) -> None:
        """never_exceeds() produces G(s < v)"""
        result = Check.signal("Speed").never_exceeds(220)
        assert isinstance(result, CheckResult)
        assert result.to_dict() == {
            'operator': 'always',
            'formula': {
                'operator': 'atomic',
                'predicate': {'predicate': 'lessThan', 'signal': 'Speed', 'value': 220}
            }
        }

    def test_never_below(self) -> None:
        """never_below() produces G(s >= v)"""
        result = Check.signal("Voltage").never_below(11.5)
        assert result.to_dict() == {
            'operator': 'always',
            'formula': {
                'operator': 'atomic',
                'predicate': {
                    'predicate': 'greaterThanOrEqual',
                    'signal': 'Voltage',
                    'value': 11.5,
                }
            }
        }

    def test_stays_between(self) -> None:
        """stays_between() produces G(lo <= s <= hi)"""
        result = Check.signal("Voltage").stays_between(11.5, 14.5)
        assert result.to_dict() == {
            'operator': 'always',
            'formula': {
                'operator': 'atomic',
                'predicate': {
                    'predicate': 'between',
                    'signal': 'Voltage',
                    'min': 11.5,
                    'max': 14.5,
                }
            }
        }

    def test_never_equals(self) -> None:
        """never_equals() produces G(not(s == v))"""
        result = Check.signal("ErrorCode").never_equals(0xFF)
        assert result.to_dict() == {
            'operator': 'always',
            'formula': {
                'operator': 'not',
                'formula': {
                    'operator': 'atomic',
                    'predicate': {
                        'predicate': 'equals',
                        'signal': 'ErrorCode',
                        'value': 0xFF,
                    }
                }
            }
        }

    def test_equals_always(self) -> None:
        """equals().always() produces G(s == v)"""
        result = Check.signal("Gear").equals(0).always()
        assert isinstance(result, CheckResult)
        assert result.to_dict() == {
            'operator': 'always',
            'formula': {
                'operator': 'atomic',
                'predicate': {'predicate': 'equals', 'signal': 'Gear', 'value': 0}
            }
        }

    def test_settles_between_within(self) -> None:
        """settles_between().within() produces G_t(lo <= s <= hi)"""
        result = Check.signal("Temp").settles_between(60, 80).within(500)
        assert isinstance(result, CheckResult)
        assert result.to_dict() == {
            'operator': 'metricAlways',
            'timebound': 500,
            'formula': {
                'operator': 'atomic',
                'predicate': {
                    'predicate': 'between',
                    'signal': 'Temp',
                    'min': 60,
                    'max': 80,
                }
            }
        }


# ============================================================================
# When / Then causal checks
# ============================================================================

class TestCheckWhenThen:
    """Test Check.when().then() causal chains."""

    def test_when_exceeds_then_equals(self) -> None:
        """when().exceeds().then().equals().within() produces G(p -> F_t(q))"""
        result = (
            Check.when("Brake").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
        )
        assert isinstance(result, CheckResult)
        # G( Brake > 50 → F≤100(BrakeLight == 1) )
        expected = (
            Signal("Brake").greater_than(50)
            .implies(Signal("BrakeLight").equals(1).within(100))
            .always()
            .to_dict()
        )
        assert result.to_dict() == expected

    def test_when_equals_then_exceeds(self) -> None:
        """when().equals() trigger with then().exceeds() response"""
        result = (
            Check.when("Ignition").equals(1)
            .then("RPM").exceeds(500)
            .within(2000)
        )
        expected = (
            Signal("Ignition").equals(1)
            .implies(Signal("RPM").greater_than(500).within(2000))
            .always()
            .to_dict()
        )
        assert result.to_dict() == expected

    def test_when_drops_below_then_stays_between(self) -> None:
        """when().drops_below() trigger with then().stays_between() response"""
        result = (
            Check.when("FuelLevel").drops_below(10)
            .then("FuelWarning").stays_between(1, 1)
            .within(50)
        )
        expected = (
            Signal("FuelLevel").less_than(10)
            .implies(Signal("FuelWarning").between(1, 1).within(50))
            .always()
            .to_dict()
        )
        assert result.to_dict() == expected


# ============================================================================
# Metadata
# ============================================================================

class TestCheckMetadata:
    """Test CheckResult metadata (name, severity) and chaining."""

    def test_named(self) -> None:
        """named() sets the name attribute"""
        result = Check.signal("Speed").never_exceeds(220).named("Speed limit")
        assert result.name == "Speed limit"

    def test_severity(self) -> None:
        """severity() sets the check_severity attribute"""
        result = Check.signal("Speed").never_exceeds(220).severity("critical")
        assert result.check_severity == "critical"

    def test_chaining_named_then_severity(self) -> None:
        """named() then severity() both stick"""
        result = (
            Check.signal("Speed").never_exceeds(220)
            .named("Speed limit")
            .severity("critical")
        )
        assert result.name == "Speed limit"
        assert result.check_severity == "critical"

    def test_chaining_severity_then_named(self) -> None:
        """severity() then named() both stick"""
        result = (
            Check.signal("Speed").never_exceeds(220)
            .severity("warning")
            .named("Soft limit")
        )
        assert result.name == "Soft limit"
        assert result.check_severity == "warning"

    def test_metadata_absent_from_to_dict(self) -> None:
        """Metadata is NOT included in the LTL formula dict."""
        result = (
            Check.signal("Speed").never_exceeds(220)
            .named("Speed limit")
            .severity("critical")
        )
        d = result.to_dict()
        assert "name" not in d  # type: ignore[operator]
        assert "severity" not in d  # type: ignore[operator]
        assert "check_severity" not in d  # type: ignore[operator]

    def test_defaults_none(self) -> None:
        """name and check_severity default to None"""
        result = Check.signal("Speed").never_exceeds(220)
        assert result.name is None
        assert result.check_severity is None

    def test_to_property_returns_property(self) -> None:
        """to_property() unwraps to a Property with matching dict"""
        result = Check.signal("Speed").never_exceeds(220)
        prop = result.to_property()
        assert isinstance(prop, Property)
        assert prop.to_dict() == result.to_dict()


# ============================================================================
# Equivalence: Check API == DSL
# ============================================================================

class TestCheckEquivalence:
    """Every Check method must produce the same formula as its DSL equivalent."""

    def test_never_exceeds_eq_dsl(self) -> None:
        """never_exceeds matches Signal.less_than.always"""
        check = Check.signal("Speed").never_exceeds(220).to_dict()
        dsl = Signal("Speed").less_than(220).always().to_dict()
        assert check == dsl

    def test_never_below_eq_dsl(self) -> None:
        """never_below matches Signal.greater_than_or_equal.always"""
        check = Check.signal("Voltage").never_below(11.5).to_dict()
        dsl = Signal("Voltage").greater_than_or_equal(11.5).always().to_dict()
        assert check == dsl

    def test_stays_between_eq_dsl(self) -> None:
        """stays_between matches Signal.between.always"""
        check = Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        dsl = Signal("Voltage").between(11.5, 14.5).always().to_dict()
        assert check == dsl

    def test_never_equals_eq_dsl(self) -> None:
        """never_equals matches Signal.equals.never"""
        check = Check.signal("ErrorCode").never_equals(0xFF).to_dict()
        dsl = Signal("ErrorCode").equals(0xFF).never().to_dict()
        assert check == dsl

    def test_equals_always_eq_dsl(self) -> None:
        """equals.always matches Signal.equals.always"""
        check = Check.signal("Gear").equals(0).always().to_dict()
        dsl = Signal("Gear").equals(0).always().to_dict()
        assert check == dsl

    def test_settles_between_eq_dsl(self) -> None:
        """settles_between.within matches Signal.between.for_at_least"""
        check = Check.signal("Temp").settles_between(60, 80).within(500).to_dict()
        dsl = Signal("Temp").between(60, 80).for_at_least(500).to_dict()
        assert check == dsl

    def test_when_then_eq_dsl(self) -> None:
        """when/then matches implies.within.always"""
        check = (
            Check.when("Brake").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
            .to_dict()
        )
        dsl = (
            Signal("Brake").greater_than(50)
            .implies(Signal("BrakeLight").equals(1).within(100))
            .always()
            .to_dict()
        )
        assert check == dsl

    def test_when_equals_then_exceeds_eq_dsl(self) -> None:
        """when(equals)/then(exceeds) matches DSL equivalent"""
        check = (
            Check.when("Ignition").equals(1)
            .then("RPM").exceeds(500)
            .within(2000)
            .to_dict()
        )
        dsl = (
            Signal("Ignition").equals(1)
            .implies(Signal("RPM").greater_than(500).within(2000))
            .always()
            .to_dict()
        )
        assert check == dsl

    def test_when_drops_below_then_stays_between_eq_dsl(self) -> None:
        """when(drops_below)/then(stays_between) matches DSL equivalent"""
        check = (
            Check.when("Fuel").drops_below(10)
            .then("Warning").stays_between(1, 1)
            .within(50)
            .to_dict()
        )
        dsl = (
            Signal("Fuel").less_than(10)
            .implies(Signal("Warning").between(1, 1).within(50))
            .always()
            .to_dict()
        )
        assert check == dsl

"""Unit tests for the YAML loader

Tests cover:
- Simple checks: each condition type loaded from YAML string
- When/Then checks: all trigger/response combinations
- Metadata: name and severity carried on CheckResult
- File loading: write temp YAML file, load it, verify
- Error handling: all validation error cases raise ValueError
- Equivalence: YAML-loaded checks produce same formula as Check API
"""

import textwrap
from pathlib import Path

import pytest

from aletheia.checks import Check, CheckResult
from aletheia.yaml_loader import load_checks


# ============================================================================
# Simple checks — each condition type
# ============================================================================

class TestLoadSimpleChecks:
    """Load each simple condition from a YAML string and verify formula."""

    def test_never_exceeds(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()

    def test_never_below(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Voltage
                condition: never_below
                value: 11.5
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Voltage").never_below(11.5).to_dict()

    def test_stays_between(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Voltage
                condition: stays_between
                min: 11.5
                max: 14.5
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )

    def test_never_equals(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: ErrorCode
                condition: never_equals
                value: 255
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("ErrorCode").never_equals(255).to_dict()

    def test_equals_always(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Gear
                condition: equals
                value: 0
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Gear").equals(0).always().to_dict()

    def test_settles_between(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: CoolantTemp
                condition: settles_between
                min: 80
                max: 100
                within_ms: 5000
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            Check.signal("CoolantTemp").settles_between(80, 100).within(5000).to_dict()
        )

    def test_multiple_checks(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
              - signal: Voltage
                condition: stays_between
                min: 11.5
                max: 14.5
        """))
        assert len(checks) == 2
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()
        assert checks[1].to_dict() == (
            Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )


# ============================================================================
# When/Then checks
# ============================================================================

class TestLoadWhenThenChecks:
    """Load when/then causal checks from YAML strings."""

    def test_when_exceeds_then_equals(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - name: "Brake response"
                when:
                  signal: BrakePedal
                  condition: exceeds
                  value: 50
                then:
                  signal: BrakeLight
                  condition: equals
                  value: 1
                within_ms: 100
        """))
        assert len(checks) == 1
        expected = (
            Check.when("BrakePedal").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_equals_then_exceeds(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - when:
                  signal: Ignition
                  condition: equals
                  value: 1
                then:
                  signal: RPM
                  condition: exceeds
                  value: 500
                within_ms: 2000
        """))
        expected = (
            Check.when("Ignition").equals(1)
            .then("RPM").exceeds(500)
            .within(2000)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_drops_below_then_stays_between(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - when:
                  signal: FuelLevel
                  condition: drops_below
                  value: 10
                then:
                  signal: FuelWarning
                  condition: stays_between
                  min: 1
                  max: 1
                within_ms: 50
        """))
        expected = (
            Check.when("FuelLevel").drops_below(10)
            .then("FuelWarning").stays_between(1, 1)
            .within(50)
            .to_dict()
        )
        assert checks[0].to_dict() == expected


# ============================================================================
# Metadata
# ============================================================================

class TestLoadMetadata:
    """Verify name and severity are set on CheckResult from YAML."""

    def test_name_set(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - name: "Speed limit"
                signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert checks[0].name == "Speed limit"

    def test_severity_set(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
                severity: critical
        """))
        assert checks[0].check_severity == "critical"

    def test_name_and_severity(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - name: "Speed limit"
                signal: Speed
                condition: never_exceeds
                value: 220
                severity: warning
        """))
        assert checks[0].name == "Speed limit"
        assert checks[0].check_severity == "warning"

    def test_defaults_none(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert checks[0].name is None
        assert checks[0].check_severity is None

    def test_when_then_metadata(self) -> None:
        checks = load_checks(textwrap.dedent("""\
            checks:
              - name: "Brake response"
                when:
                  signal: BrakePedal
                  condition: exceeds
                  value: 50
                then:
                  signal: BrakeLight
                  condition: equals
                  value: 1
                within_ms: 100
                severity: safety
        """))
        assert checks[0].name == "Brake response"
        assert checks[0].check_severity == "safety"


# ============================================================================
# File loading
# ============================================================================

class TestLoadFromFile:
    """Load checks from a temporary YAML file."""

    def test_load_from_path_object(self, tmp_path: Path) -> None:
        yaml_file = tmp_path / "checks.yaml"
        yaml_file.write_text(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """))
        checks = load_checks(yaml_file)
        assert len(checks) == 1
        assert checks[0].to_dict() == Check.signal("Speed").never_exceeds(220).to_dict()

    def test_load_from_path_string(self, tmp_path: Path) -> None:
        yaml_file = tmp_path / "checks.yml"
        yaml_file.write_text(textwrap.dedent("""\
            checks:
              - signal: Voltage
                condition: stays_between
                min: 11.5
                max: 14.5
        """))
        checks = load_checks(str(yaml_file))
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            Check.signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )

    def test_file_not_found(self) -> None:
        with pytest.raises(FileNotFoundError, match="YAML file not found"):
            load_checks("/nonexistent/path/checks.yaml")


# ============================================================================
# Error handling
# ============================================================================

class TestLoadErrors:
    """All validation error cases raise ValueError with useful messages."""

    def test_missing_checks_key(self) -> None:
        with pytest.raises(ValueError, match="YAML must contain a 'checks' list"):
            load_checks("signals:\n  - foo\n")

    def test_checks_not_a_list(self) -> None:
        with pytest.raises(ValueError, match="YAML must contain a 'checks' list"):
            load_checks("checks: not_a_list\n")

    def test_no_signal_or_when(self) -> None:
        with pytest.raises(ValueError, match="must have 'signal' or 'when'/'then'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - name: "Bad check"
                    condition: never_exceeds
                    value: 100
            """))

    def test_unknown_simple_condition(self) -> None:
        with pytest.raises(ValueError, match="unknown condition 'bogus'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: bogus
                    value: 100
            """))

    def test_never_exceeds_missing_value(self) -> None:
        with pytest.raises(ValueError, match="requires 'value'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: never_exceeds
            """))

    def test_stays_between_missing_min(self) -> None:
        with pytest.raises(ValueError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Voltage
                    condition: stays_between
                    max: 14.5
            """))

    def test_stays_between_missing_max(self) -> None:
        with pytest.raises(ValueError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Voltage
                    condition: stays_between
                    min: 11.5
            """))

    def test_settles_between_missing_within_ms(self) -> None:
        with pytest.raises(ValueError, match="requires 'within_ms'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Temp
                    condition: settles_between
                    min: 80
                    max: 100
            """))

    def test_settles_between_missing_range(self) -> None:
        with pytest.raises(ValueError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Temp
                    condition: settles_between
                    within_ms: 5000
            """))

    def test_equals_missing_value(self) -> None:
        with pytest.raises(ValueError, match="requires 'value'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Gear
                    condition: equals
            """))

    def test_when_then_missing_then(self) -> None:
        with pytest.raises(ValueError, match="must have 'signal' or 'when'/'then'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - name: "Incomplete"
                    when:
                      signal: Brake
                      condition: exceeds
                      value: 50
                    within_ms: 100
            """))

    def test_when_then_missing_within_ms(self) -> None:
        with pytest.raises(ValueError, match="require 'within_ms'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - when:
                      signal: Brake
                      condition: exceeds
                      value: 50
                    then:
                      signal: BrakeLight
                      condition: equals
                      value: 1
            """))

    def test_unknown_when_condition(self) -> None:
        with pytest.raises(ValueError, match="unknown when condition 'bogus'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - when:
                      signal: Brake
                      condition: bogus
                      value: 50
                    then:
                      signal: BrakeLight
                      condition: equals
                      value: 1
                    within_ms: 100
            """))

    def test_unknown_then_condition(self) -> None:
        with pytest.raises(ValueError, match="unknown then condition 'bogus'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - when:
                      signal: Brake
                      condition: exceeds
                      value: 50
                    then:
                      signal: BrakeLight
                      condition: bogus
                      value: 1
                    within_ms: 100
            """))

    def test_named_check_in_error_message(self) -> None:
        """Error messages include the check name when present."""
        with pytest.raises(ValueError, match="Check 'My Check'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - name: "My Check"
                    signal: Speed
                    condition: bogus
                    value: 100
            """))

    def test_unnamed_check_in_error_message(self) -> None:
        """Error messages use <unnamed> when no name is present."""
        with pytest.raises(ValueError, match="Check '<unnamed>'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: bogus
                    value: 100
            """))

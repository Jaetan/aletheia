"""Unit tests for the YAML loader

Tests cover:
- Simple checks: each condition type loaded from YAML string
- When/Then checks: all trigger/response combinations
- Metadata: name and severity carried on CheckResult
- File loading: write temp YAML file, load it, verify
- Error handling: all validation error cases raise ValidationError
- Equivalence: YAML-loaded checks produce same formula as Check API
"""

import textwrap
from pathlib import Path

import pytest

from aletheia import ValidationError
from aletheia.checks import signal, when
from aletheia.yaml_loader import load_checks


# ============================================================================
# Simple checks — each condition type
# ============================================================================

class TestLoadSimpleChecks:
    """Load each simple condition from a YAML string and verify formula."""

    def test_never_exceeds(self) -> None:
        """Verify never exceeds."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == signal("Speed").never_exceeds(220).to_dict()

    def test_never_below(self) -> None:
        """Verify never below."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Voltage
                condition: never_below
                value: 11.5
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == signal("Voltage").never_below(11.5).to_dict()

    def test_stays_between(self) -> None:
        """Verify stays between."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Voltage
                condition: stays_between
                min: 11.5
                max: 14.5
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == (
            signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )

    def test_never_equals(self) -> None:
        """Verify never equals."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: ErrorCode
                condition: never_equals
                value: 255
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == signal("ErrorCode").never_equals(255).to_dict()

    def test_equals_always(self) -> None:
        """Verify equals always."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Gear
                condition: equals
                value: 0
        """))
        assert len(checks) == 1
        assert checks[0].to_dict() == signal("Gear").equals(0).always().to_dict()

    def test_settles_between(self) -> None:
        """Verify settles between."""
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
            signal("CoolantTemp").settles_between(80, 100).within(5000).to_dict()
        )

    def test_multiple_checks(self) -> None:
        """Verify multiple checks."""
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
        assert checks[0].to_dict() == signal("Speed").never_exceeds(220).to_dict()
        assert checks[1].to_dict() == (
            signal("Voltage").stays_between(11.5, 14.5).to_dict()
        )


# ============================================================================
# When/Then checks
# ============================================================================

class TestLoadWhenThenChecks:
    """Load when/then causal checks from YAML strings."""

    def test_when_exceeds_then_equals(self) -> None:
        """Verify when exceeds then equals."""
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
            when("BrakePedal").exceeds(50)
            .then("BrakeLight").equals(1)
            .within(100)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_equals_then_exceeds(self) -> None:
        """Verify when equals then exceeds."""
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
            when("Ignition").equals(1)
            .then("RPM").exceeds(500)
            .within(2000)
            .to_dict()
        )
        assert checks[0].to_dict() == expected

    def test_when_drops_below_then_stays_between(self) -> None:
        """Verify when drops below then stays between."""
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
            when("FuelLevel").drops_below(10)
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
        """Verify name set."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - name: "Speed limit"
                signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert checks[0].name == "Speed limit"

    def test_severity_set(self) -> None:
        """Verify severity set."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
                severity: critical
        """))
        assert checks[0].check_severity == "critical"

    def test_name_and_severity(self) -> None:
        """Verify name and severity."""
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
        """Verify defaults none."""
        checks = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """))
        assert checks[0].name == ""
        assert checks[0].check_severity == ""

    def test_when_then_metadata(self) -> None:
        """Verify when then metadata."""
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
        """Verify load from path object."""
        yaml_file = tmp_path / "checks.yaml"
        yaml_file.write_text(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 220
        """), encoding="utf-8")
        checks = load_checks(yaml_file)
        assert len(checks) == 1
        assert checks[0].to_dict() == signal("Speed").never_exceeds(220).to_dict()

    def test_string_path_now_treated_as_inline_yaml(self, tmp_path: Path) -> None:
        """A bare string is parsed as inline YAML — never auto-promoted to a file path.

        R19 cluster B / PY-B-26.12 closes the path-confusion vector: dispatch
        is now strict by parameter type (``Path`` → file, ``str`` → inline
        YAML).  A string that happens to name an existing file is no longer
        opened; it is fed to ``yaml.safe_load`` as a YAML scalar.  Callers
        who want file behaviour wrap in ``pathlib.Path``.
        """
        yaml_file = tmp_path / "checks.yml"
        yaml_file.write_text("dummy", encoding="utf-8")
        # Passing the path as a bare str now parses the string itself as YAML
        # (a scalar) rather than opening the file — fails the structural check.
        with pytest.raises(ValidationError, match="YAML must contain a 'checks' list"):
            load_checks(str(yaml_file))

    def test_file_not_found(self, tmp_path: Path) -> None:
        """Verify file not found via Path argument."""
        missing = tmp_path / "does_not_exist.yaml"
        with pytest.raises(FileNotFoundError):
            load_checks(missing)



# ============================================================================
# Error handling
# ============================================================================

class TestLoadErrors:
    """All validation error cases raise ValidationError with useful messages."""

    def test_missing_checks_key(self) -> None:
        """Verify missing checks key."""
        with pytest.raises(ValidationError, match="YAML must contain a 'checks' list"):
            load_checks("signals:\n  - foo\n")

    def test_checks_not_a_list(self) -> None:
        """Verify checks not a list."""
        with pytest.raises(ValidationError, match="YAML must contain a 'checks' list"):
            load_checks("checks: not_a_list\n")

    def test_no_signal_or_when(self) -> None:
        """Verify no signal or when."""
        with pytest.raises(ValidationError, match="must have 'signal' or 'when'/'then'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - name: "Bad check"
                    condition: never_exceeds
                    value: 100
            """))

    def test_unknown_simple_condition(self) -> None:
        """Verify unknown simple condition."""
        with pytest.raises(ValidationError, match="unknown condition 'bogus'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: bogus
                    value: 100
            """))

    def test_never_exceeds_missing_value(self) -> None:
        """Verify never exceeds missing value."""
        with pytest.raises(ValidationError, match="requires 'value'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: never_exceeds
            """))

    def test_stays_between_missing_min(self) -> None:
        """Verify stays between missing min."""
        with pytest.raises(ValidationError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Voltage
                    condition: stays_between
                    max: 14.5
            """))

    def test_stays_between_missing_max(self) -> None:
        """Verify stays between missing max."""
        with pytest.raises(ValidationError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Voltage
                    condition: stays_between
                    min: 11.5
            """))

    def test_settles_between_missing_within_ms(self) -> None:
        """Verify settles between missing within ms."""
        with pytest.raises(ValidationError, match="requires 'within_ms'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Temp
                    condition: settles_between
                    min: 80
                    max: 100
            """))

    def test_settles_between_missing_range(self) -> None:
        """Verify settles between missing range."""
        with pytest.raises(ValidationError, match="requires 'min' and 'max'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Temp
                    condition: settles_between
                    within_ms: 5000
            """))

    def test_equals_missing_value(self) -> None:
        """Verify equals missing value."""
        with pytest.raises(ValidationError, match="requires 'value'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Gear
                    condition: equals
            """))

    def test_when_then_missing_then(self) -> None:
        """Verify when then missing then."""
        with pytest.raises(ValidationError, match="must have 'signal' or 'when'/'then'"):
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
        """Verify when then missing within ms."""
        with pytest.raises(ValidationError, match="require 'within_ms'"):
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
        """Verify unknown when condition."""
        with pytest.raises(ValidationError, match="unknown when condition 'bogus'"):
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
        """Verify unknown then condition."""
        with pytest.raises(ValidationError, match="unknown then condition 'bogus'"):
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
        with pytest.raises(ValidationError, match="Check 'My Check'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - name: "My Check"
                    signal: Speed
                    condition: bogus
                    value: 100
            """))

    def test_unnamed_check_in_error_message(self) -> None:
        """Error messages use <unnamed> when no name is present."""
        with pytest.raises(ValidationError, match="Check '<unnamed>'"):
            load_checks(textwrap.dedent("""\
                checks:
                  - signal: Speed
                    condition: bogus
                    value: 100
            """))


# ============================================================================
# R20 cluster N — adversarial-input hardening (cross-binding mirror)
# ============================================================================

class TestLoaderHardening:
    """Symlinked YAML refused outright, mirroring
    ``aletheia::detail::validate_loader_path`` in C++.  Inline YAML
    strings are unaffected — the symlink check only applies to ``Path``
    inputs.
    """

    def test_symlink_path_rejected(self, tmp_path: Path) -> None:
        """Symlinked .yaml is refused outright per cluster N hardening."""
        real = tmp_path / "real.yaml"
        real.write_text(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 200
        """))
        link = tmp_path / "link.yaml"
        try:
            link.symlink_to(real)
        except (OSError, NotImplementedError):
            pytest.skip("symlink creation not permitted on this filesystem")
        with pytest.raises(ValidationError, match="symbolic link"):
            load_checks(link)

    def test_inline_string_unaffected(self) -> None:
        """Inline YAML strings bypass the symlink check (no path involved)."""
        result = load_checks(textwrap.dedent("""\
            checks:
              - signal: Speed
                condition: never_exceeds
                value: 200
        """))
        assert len(result) == 1

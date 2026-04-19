"""YAML loader for declarative CAN signal checks

Loads check definitions from YAML files or strings and compiles them
through the Check API into LTL properties.

Usage:
    from aletheia import load_checks

    # From a file
    checks = load_checks("my_checks.yaml")

    # From a YAML string
    checks = load_checks('''
    checks:
      - name: "Speed limit"
        signal: VehicleSpeed
        condition: never_exceeds
        value: 220
        severity: critical
    ''')

    # Use with AletheiaClient
    client.set_properties([c.to_dict() for c in checks])

YAML Schema
============

Simple checks (single signal)::

    checks:
      - name: "Speed limit"          # optional
        signal: VehicleSpeed
        condition: never_exceeds      # never_exceeds|never_below|stays_between|
                                      # never_equals|equals|settles_between
        value: 220                    # for value-based conditions
        min: 11.5                     # for range-based conditions
        max: 14.5
        within_ms: 5000              # required for settles_between
        severity: critical           # optional

When/Then checks (causal)::

    checks:
      - name: "Brake response"
        when:
          signal: BrakePedal
          condition: exceeds          # exceeds|equals|drops_below
          value: 50
        then:
          signal: BrakeLight
          condition: equals           # equals|exceeds|stays_between
          value: 1
        within_ms: 100
        severity: safety
"""

from pathlib import Path

import yaml

from .checks import Check, CheckResult
from .protocols import is_object_list, is_str_dict
from ._check_conditions import (
    ALL_SIMPLE_CONDITIONS,
    SIMPLE_VALUE_CONDITIONS,
    SIMPLE_RANGE_CONDITIONS,
    SIMPLE_SETTLES_CONDITIONS,
    SIMPLE_EQUALS_CONDITIONS,
    WHEN_CONDITIONS,
    ALL_THEN_CONDITIONS,
    dispatch_simple,
    dispatch_when,
)
from ._loader_utils import get_str, get_number, get_int, get_dict


def _ctx(name: str) -> str:
    """Format a check name as an error context string."""
    return f"Check '{name}'"


def _check_name(entry: dict[str, object]) -> str:
    """Extract the check name for error messages."""
    name = entry.get("name")
    if isinstance(name, str):
        return name
    return "<unnamed>"


# ============================================================================
# Public API
# ============================================================================

def load_checks(source: str | Path) -> list[CheckResult]:
    """Load checks from a YAML file or YAML string.

    Args:
        source: Path to .yaml/.yml file, or a YAML string

    Returns:
        List of CheckResult objects ready for use with AletheiaClient

    Raises:
        ValueError: Invalid check definition (missing fields, unknown condition)
        FileNotFoundError: File path doesn't exist
    """
    raw = _load_yaml(source)

    if not is_str_dict(raw) or "checks" not in raw:
        raise ValueError("YAML must contain a 'checks' list")

    checks_raw = raw["checks"]
    if not is_object_list(checks_raw):
        raise ValueError("YAML must contain a 'checks' list")

    results: list[CheckResult] = []
    for entry in checks_raw:
        if not is_str_dict(entry):
            raise ValueError("Each check must be a YAML mapping")
        results.append(_parse_check(entry))
    return results


# ============================================================================
# Internal helpers
# ============================================================================

def _load_yaml(source: str | Path) -> object:
    """Load YAML from a file path or string.

    Returns the raw parsed object — caller must validate structure.
    """
    if isinstance(source, Path):
        with open(source, encoding="utf-8") as f:
            return yaml.safe_load(f)
    # String: existing file takes priority over inline detection
    path = Path(source)
    if path.exists():
        with open(path, encoding="utf-8") as f:
            return yaml.safe_load(f)
    # Multi-line or YAML-structured strings are inline YAML
    if "\n" in source or source.lstrip().startswith(("checks:", "-", "{", "[")):
        return yaml.safe_load(source)
    # Doesn't exist and doesn't look like inline YAML
    raise FileNotFoundError(f"YAML file not found: {source}")


def _parse_check(entry: dict[str, object]) -> CheckResult:
    """Parse a single check entry from the YAML."""
    if "when" in entry:
        result = _parse_when_then_check(entry)
    elif "signal" in entry:
        result = _parse_simple_check(entry)
    else:
        name = _check_name(entry)
        raise ValueError(
            f"Check '{name}': must have 'signal' or 'when'/'then'"
        )

    # Apply metadata — CheckResult is immutable so re-bind on each call.
    raw_name = entry.get("name")
    if isinstance(raw_name, str):
        result = result.named(raw_name)
    raw_sev = entry.get("severity")
    if isinstance(raw_sev, str):
        result = result.severity(raw_sev)

    return result


def _parse_simple_check(entry: dict[str, object]) -> CheckResult:
    """Parse a simple single-signal check."""
    name = _check_name(entry)
    condition = entry.get("condition", "")
    if not isinstance(condition, str):
        raise ValueError(f"Check '{name}': 'condition' must be a string")
    signal = get_str(entry, "signal", _ctx(name))

    if condition not in ALL_SIMPLE_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown condition '{condition}'")

    if condition in SIMPLE_VALUE_CONDITIONS:
        if "value" not in entry:
            raise ValueError(
                f"Check '{name}': condition '{condition}' requires 'value'"
            )
        return dispatch_simple(signal, condition, get_number(entry, "value", _ctx(name)))

    if condition in SIMPLE_RANGE_CONDITIONS:
        if "min" not in entry or "max" not in entry:
            raise ValueError(
                f"Check '{name}': condition '{condition}' requires 'min' and 'max'"
            )
        return Check.signal(signal).stays_between(
            get_number(entry, "min", _ctx(name)),
            get_number(entry, "max", _ctx(name)),
        )

    if condition in SIMPLE_SETTLES_CONDITIONS:
        if "min" not in entry or "max" not in entry:
            raise ValueError(
                f"Check '{name}': condition 'settles_between' requires 'min' and 'max'"
            )
        if "within_ms" not in entry:
            raise ValueError(
                f"Check '{name}': condition 'settles_between' requires 'within_ms'"
            )
        return Check.signal(signal).settles_between(
            get_number(entry, "min", _ctx(name)),
            get_number(entry, "max", _ctx(name)),
        ).within(get_int(entry, "within_ms", _ctx(name)))

    if condition in SIMPLE_EQUALS_CONDITIONS:
        if "value" not in entry:
            raise ValueError(
                f"Check '{name}': condition 'equals' requires 'value'"
            )
        return Check.signal(signal).equals(get_number(entry, "value", _ctx(name))).always()

    raise ValueError(f"Check '{name}': unknown condition '{condition}'")


def _parse_when_then_check(entry: dict[str, object]) -> CheckResult:
    """Parse a when/then causal check."""
    name = _check_name(entry)

    if "then" not in entry:
        raise ValueError(
            f"Check '{name}': must have 'signal' or 'when'/'then'"
        )
    if "within_ms" not in entry:
        raise ValueError(
            f"Check '{name}': when/then checks require 'within_ms'"
        )

    when = get_dict(entry, "when", _ctx(name))
    then = get_dict(entry, "then", _ctx(name))
    within_ms = get_int(entry, "within_ms", _ctx(name))

    # Validate when clause
    when_cond = get_str(when, "condition", _ctx(name))
    if when_cond not in WHEN_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown when condition '{when_cond}'")

    when_signal = get_str(when, "signal", _ctx(name))
    when_value = get_number(when, "value", _ctx(name))

    when_result = dispatch_when(Check.when(when_signal), when_cond, when_value)

    # Validate then clause
    then_cond = get_str(then, "condition", _ctx(name))
    if then_cond not in ALL_THEN_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown then condition '{then_cond}'")

    then_signal = get_str(then, "signal", _ctx(name))
    then_builder = when_result.then(then_signal)

    if then_cond == "equals":
        then_result = then_builder.equals(get_number(then, "value", _ctx(name)))
    elif then_cond == "exceeds":
        then_result = then_builder.exceeds(get_number(then, "value", _ctx(name)))
    else:  # stays_between
        if "min" not in then or "max" not in then:
            raise ValueError(
                f"Check '{name}': then condition 'stays_between' requires 'min' and 'max'"
            )
        then_result = then_builder.stays_between(
            get_number(then, "min", _ctx(name)),
            get_number(then, "max", _ctx(name)),
        )

    return then_result.within(within_ms)

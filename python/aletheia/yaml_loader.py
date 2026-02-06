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

from __future__ import annotations

from pathlib import Path
from typing import TypeGuard

import yaml  # type: ignore[import-untyped]

from .checks import Check, CheckResult


# ============================================================================
# Condition constants
# ============================================================================

_SIMPLE_VALUE_CONDITIONS = frozenset({
    "never_exceeds", "never_below", "never_equals",
})
_SIMPLE_RANGE_CONDITIONS = frozenset({
    "stays_between",
})
_SIMPLE_SETTLES_CONDITIONS = frozenset({
    "settles_between",
})
_SIMPLE_EQUALS_CONDITIONS = frozenset({
    "equals",
})
_ALL_SIMPLE_CONDITIONS = (
    _SIMPLE_VALUE_CONDITIONS
    | _SIMPLE_RANGE_CONDITIONS
    | _SIMPLE_SETTLES_CONDITIONS
    | _SIMPLE_EQUALS_CONDITIONS
)

_WHEN_CONDITIONS = frozenset({"exceeds", "equals", "drops_below"})
_THEN_VALUE_CONDITIONS = frozenset({"equals", "exceeds"})
_THEN_RANGE_CONDITIONS = frozenset({"stays_between"})
_ALL_THEN_CONDITIONS = _THEN_VALUE_CONDITIONS | _THEN_RANGE_CONDITIONS


# ============================================================================
# Type guards — runtime narrowing for YAML-parsed data
# ============================================================================

def _is_str_dict(val: object) -> TypeGuard[dict[str, object]]:
    """Narrow an unknown value to ``dict[str, object]``.

    YAML ``safe_load`` always produces dicts with string keys, so an
    ``isinstance(val, dict)`` check is sufficient at runtime.
    """
    return isinstance(val, dict)


def _is_object_list(val: object) -> TypeGuard[list[object]]:
    """Narrow an unknown value to ``list[object]``."""
    return isinstance(val, list)


# ============================================================================
# Field accessors with runtime type checking
# ============================================================================

def _get_str(d: dict[str, object], key: str, check_name: str) -> str:
    """Extract a required string field from a dict."""
    val = d.get(key)
    if not isinstance(val, str):
        raise ValueError(f"Check '{check_name}': missing or invalid '{key}' (expected string)")
    return val


def _get_number(d: dict[str, object], key: str, check_name: str) -> float:
    """Extract a required numeric field from a dict."""
    val = d.get(key)
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return float(val)
    raise ValueError(f"Check '{check_name}': missing or invalid '{key}' (expected number)")


def _get_int(d: dict[str, object], key: str, check_name: str) -> int:
    """Extract a required integer field from a dict."""
    val = d.get(key)
    if isinstance(val, int) and not isinstance(val, bool):
        return val
    raise ValueError(f"Check '{check_name}': missing or invalid '{key}' (expected integer)")


def _get_dict(d: dict[str, object], key: str, check_name: str) -> dict[str, object]:
    """Extract a required dict field from a dict."""
    val = d.get(key)
    if not _is_str_dict(val):
        raise ValueError(f"Check '{check_name}': missing or invalid '{key}' (expected mapping)")
    return val


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

    if not _is_str_dict(raw) or "checks" not in raw:
        raise ValueError("YAML must contain a 'checks' list")

    checks_raw = raw["checks"]
    if not _is_object_list(checks_raw):
        raise ValueError("YAML must contain a 'checks' list")

    results: list[CheckResult] = []
    for entry in checks_raw:
        if not _is_str_dict(entry):
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
            return yaml.safe_load(f)  # type: ignore[no-any-return]

    # String: detect whether it's a file path or inline YAML
    if "\n" in source or source.lstrip().startswith("checks:"):
        return yaml.safe_load(source)  # type: ignore[no-any-return]

    # Treat as file path
    path = Path(source)
    if not path.exists():
        raise FileNotFoundError(f"YAML file not found: {source}")
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)  # type: ignore[no-any-return]


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

    # Apply metadata
    raw_name = entry.get("name")
    if isinstance(raw_name, str):
        result.named(raw_name)
    raw_sev = entry.get("severity")
    if isinstance(raw_sev, str):
        result.severity(raw_sev)

    return result


def _parse_simple_check(entry: dict[str, object]) -> CheckResult:
    """Parse a simple single-signal check."""
    name = _check_name(entry)
    condition = entry.get("condition", "")
    if not isinstance(condition, str):
        raise ValueError(f"Check '{name}': 'condition' must be a string")
    signal = _get_str(entry, "signal", name)

    if condition not in _ALL_SIMPLE_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown condition '{condition}'")

    builder = Check.signal(signal)

    if condition in _SIMPLE_VALUE_CONDITIONS:
        if "value" not in entry:
            raise ValueError(
                f"Check '{name}': condition '{condition}' requires 'value'"
            )
        value = _get_number(entry, "value", name)
        if condition == "never_exceeds":
            return builder.never_exceeds(value)
        if condition == "never_below":
            return builder.never_below(value)
        # never_equals
        return builder.never_equals(value)

    if condition in _SIMPLE_RANGE_CONDITIONS:
        if "min" not in entry or "max" not in entry:
            raise ValueError(
                f"Check '{name}': condition '{condition}' requires 'min' and 'max'"
            )
        return builder.stays_between(
            _get_number(entry, "min", name),
            _get_number(entry, "max", name),
        )

    if condition in _SIMPLE_SETTLES_CONDITIONS:
        if "min" not in entry or "max" not in entry:
            raise ValueError(
                f"Check '{name}': condition 'settles_between' requires 'min' and 'max'"
            )
        if "within_ms" not in entry:
            raise ValueError(
                f"Check '{name}': condition 'settles_between' requires 'within_ms'"
            )
        return builder.settles_between(
            _get_number(entry, "min", name),
            _get_number(entry, "max", name),
        ).within(_get_int(entry, "within_ms", name))

    # equals → equals().always()
    if "value" not in entry:
        raise ValueError(
            f"Check '{name}': condition 'equals' requires 'value'"
        )
    return builder.equals(_get_number(entry, "value", name)).always()


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

    when = _get_dict(entry, "when", name)
    then = _get_dict(entry, "then", name)
    within_ms = _get_int(entry, "within_ms", name)

    # Validate when clause
    when_cond = _get_str(when, "condition", name)
    if when_cond not in _WHEN_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown when condition '{when_cond}'")

    when_signal = _get_str(when, "signal", name)
    when_value = _get_number(when, "value", name)

    when_builder = Check.when(when_signal)
    if when_cond == "exceeds":
        when_result = when_builder.exceeds(when_value)
    elif when_cond == "equals":
        when_result = when_builder.equals(when_value)
    else:  # drops_below
        when_result = when_builder.drops_below(when_value)

    # Validate then clause
    then_cond = _get_str(then, "condition", name)
    if then_cond not in _ALL_THEN_CONDITIONS:
        raise ValueError(f"Check '{name}': unknown then condition '{then_cond}'")

    then_signal = _get_str(then, "signal", name)
    then_builder = when_result.then(then_signal)

    if then_cond == "equals":
        then_result = then_builder.equals(_get_number(then, "value", name))
    elif then_cond == "exceeds":
        then_result = then_builder.exceeds(_get_number(then, "value", name))
    else:  # stays_between
        if "min" not in then or "max" not in then:
            raise ValueError(
                f"Check '{name}': then condition 'stays_between' requires 'min' and 'max'"
            )
        then_result = then_builder.stays_between(
            _get_number(then, "min", name),
            _get_number(then, "max", name),
        )

    return then_result.within(within_ms)

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""YAML loader for declarative CAN signal checks.

Loads check definitions from YAML files or strings and compiles them
through the Check API into LTL properties.

Usage:
    from pathlib import Path
    from aletheia import load_checks

    # From a file (must be a pathlib.Path)
    checks = load_checks(Path("my_checks.yaml"))

    # From an inline YAML string (must be a str)
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
from typing import TYPE_CHECKING

import yaml

from aletheia import checks
from aletheia._check_conditions import (
    ALL_SIMPLE_CONDITIONS,
    ALL_THEN_CONDITIONS,
    SIMPLE_EQUALS_CONDITIONS,
    SIMPLE_RANGE_CONDITIONS,
    SIMPLE_SETTLES_CONDITIONS,
    SIMPLE_VALUE_CONDITIONS,
    WHEN_CONDITIONS,
    dispatch_simple,
    dispatch_when,
)
from aletheia._loader_utils import (
    get_dict,
    get_int,
    get_number,
    get_str,
    reject_symlink_loader_path,
)
from aletheia.client import ValidationError, check_dbc_text_size_bound
from aletheia.protocols import is_object_list, is_str_dict

if TYPE_CHECKING:
    from aletheia.checks import CheckResult


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
        ValidationError: Invalid check definition (missing fields, unknown condition)
        FileNotFoundError: File path doesn't exist

    """
    raw = _load_yaml(source)

    if not is_str_dict(raw) or "checks" not in raw:
        msg = "YAML must contain a 'checks' list"
        raise ValidationError(msg)

    checks_raw = raw["checks"]
    if not is_object_list(checks_raw):
        msg = "YAML must contain a 'checks' list"
        raise ValidationError(msg)

    results: list[CheckResult] = []
    for entry in checks_raw:
        if not is_str_dict(entry):
            msg = "Each check must be a YAML mapping"
            raise ValidationError(msg)
        results.append(_parse_check(entry))
    return results


# ============================================================================
# Internal helpers
# ============================================================================


def _load_yaml(source: str | Path) -> object:
    """Load YAML from a file path or string.

    Dispatch is **type-based**, not content-based: pass a
    :class:`pathlib.Path` to load from a file, or a :class:`str` to
    parse inline YAML.  Content-based dispatch (treating a string that
    happens to match an existing path as a file reference) is a
    path-confusion vector — an attacker who can plant a file at a name
    a caller types literally could redirect the load.

    Adversarial-input bound: rejects YAML inputs longer than
    ``MAX_DBC_TEXT_BYTES`` (the same 64 MiB cap as the DBC-text parser,
    since YAML check definitions reference signal names from a parsed
    DBC) with a typed :class:`InputBoundExceededError`, per AGENTS.md
    universal rule "Adversarial-input bounds at parser surfaces".

    Returns the raw parsed object — caller must validate structure.

    Migration note: callers that previously passed a file path as a
    string now must wrap in ``pathlib.Path`` (e.g.
    ``load_checks(Path("checks.yaml"))`` rather than
    ``load_checks("checks.yaml")``).  Inline YAML strings continue to
    work unchanged.  See CHANGELOG.md ``[Unreleased] [Changed]``.
    """
    if isinstance(source, Path):
        reject_symlink_loader_path(source, "YAML")
        check_dbc_text_size_bound(source.stat().st_size)
        with source.open(encoding="utf-8") as f:
            return yaml.safe_load(f)
    # source: str — the public ``load_checks`` signature constrains this
    # branch by type; basedpyright/pyright catches non-(str|Path) callers
    # statically, so a runtime defensive ``isinstance(source, str)`` would
    # be dead code and is not added.
    check_dbc_text_size_bound(len(source.encode("utf-8")))
    return yaml.safe_load(source)


def _parse_check(entry: dict[str, object]) -> CheckResult:
    """Parse a single check entry from the YAML."""
    if "when" in entry:
        result = _parse_when_then_check(entry)
    elif "signal" in entry:
        result = _parse_simple_check(entry)
    else:
        name = _check_name(entry)
        msg = f"Check '{name}': must have 'signal' or 'when'/'then'"
        raise ValidationError(msg)

    # Apply metadata — CheckResult is immutable so re-bind on each call.
    raw_name = entry.get("name")
    if isinstance(raw_name, str):
        result = result.named(raw_name)
    raw_sev = entry.get("severity")
    if isinstance(raw_sev, str):
        result = result.severity(raw_sev)

    return result


def _parse_value_condition(
    name: str,
    signal: str,
    condition: str,
    entry: dict[str, object],
) -> CheckResult:
    """Parse a value-typed simple check (e.g. never_exceeds, never_below)."""
    if "value" not in entry:
        msg = f"Check '{name}': condition '{condition}' requires 'value'"
        raise ValidationError(msg)
    return dispatch_simple(signal, condition, get_number(entry, "value", _ctx(name)))


def _parse_range_condition(
    name: str,
    signal: str,
    condition: str,
    entry: dict[str, object],
) -> CheckResult:
    """Parse a range-typed simple check (stays_between)."""
    if "min" not in entry or "max" not in entry:
        msg = f"Check '{name}': condition '{condition}' requires 'min' and 'max'"
        raise ValidationError(msg)
    return checks.signal(signal).stays_between(
        get_number(entry, "min", _ctx(name)),
        get_number(entry, "max", _ctx(name)),
    )


def _parse_settles_condition(
    name: str,
    signal: str,
    entry: dict[str, object],
) -> CheckResult:
    """Parse a settles_between simple check."""
    if "min" not in entry or "max" not in entry:
        msg = f"Check '{name}': condition 'settles_between' requires 'min' and 'max'"
        raise ValidationError(msg)
    if "within_ms" not in entry:
        msg = f"Check '{name}': condition 'settles_between' requires 'within_ms'"
        raise ValidationError(msg)
    return (
        checks.signal(signal)
        .settles_between(
            get_number(entry, "min", _ctx(name)),
            get_number(entry, "max", _ctx(name)),
        )
        .within(get_int(entry, "within_ms", _ctx(name)))
    )


def _parse_equals_condition(
    name: str,
    signal: str,
    entry: dict[str, object],
) -> CheckResult:
    """Parse an equals simple check."""
    if "value" not in entry:
        msg = f"Check '{name}': condition 'equals' requires 'value'"
        raise ValidationError(msg)
    return checks.signal(signal).equals(get_number(entry, "value", _ctx(name))).always()


def _parse_simple_check(entry: dict[str, object]) -> CheckResult:
    """Parse a simple single-signal check."""
    name = _check_name(entry)
    condition = entry.get("condition", "")
    if not isinstance(condition, str):
        msg = f"Check '{name}': 'condition' must be a string"
        raise ValidationError(msg)
    signal = get_str(entry, "signal", _ctx(name))

    if condition not in ALL_SIMPLE_CONDITIONS:
        msg = f"Check '{name}': unknown condition '{condition}'"
        raise ValidationError(msg)

    if condition in SIMPLE_VALUE_CONDITIONS:
        return _parse_value_condition(name, signal, condition, entry)
    if condition in SIMPLE_RANGE_CONDITIONS:
        return _parse_range_condition(name, signal, condition, entry)
    if condition in SIMPLE_SETTLES_CONDITIONS:
        return _parse_settles_condition(name, signal, entry)
    if condition in SIMPLE_EQUALS_CONDITIONS:
        return _parse_equals_condition(name, signal, entry)

    msg = f"Check '{name}': unknown condition '{condition}'"
    raise ValidationError(msg)


def _parse_when_then_check(entry: dict[str, object]) -> CheckResult:
    """Parse a when/then causal check."""
    name = _check_name(entry)

    if "then" not in entry:
        msg = f"Check '{name}': must have 'signal' or 'when'/'then'"
        raise ValidationError(msg)
    if "within_ms" not in entry:
        msg = f"Check '{name}': when/then checks require 'within_ms'"
        raise ValidationError(msg)

    when = get_dict(entry, "when", _ctx(name))
    then = get_dict(entry, "then", _ctx(name))
    within_ms = get_int(entry, "within_ms", _ctx(name))

    # Validate when clause
    when_cond = get_str(when, "condition", _ctx(name))
    if when_cond not in WHEN_CONDITIONS:
        msg = f"Check '{name}': unknown when condition '{when_cond}'"
        raise ValidationError(msg)

    when_signal = get_str(when, "signal", _ctx(name))
    when_value = get_number(when, "value", _ctx(name))

    when_result = dispatch_when(checks.when(when_signal), when_cond, when_value)

    # Validate then clause
    then_cond = get_str(then, "condition", _ctx(name))
    if then_cond not in ALL_THEN_CONDITIONS:
        msg = f"Check '{name}': unknown then condition '{then_cond}'"
        raise ValidationError(msg)

    then_signal = get_str(then, "signal", _ctx(name))
    then_builder = when_result.then(then_signal)

    if then_cond == "equals":
        then_result = then_builder.equals(get_number(then, "value", _ctx(name)))
    elif then_cond == "exceeds":
        then_result = then_builder.exceeds(get_number(then, "value", _ctx(name)))
    else:  # stays_between
        if "min" not in then or "max" not in then:
            msg = f"Check '{name}': then condition 'stays_between' requires 'min' and 'max'"
            raise ValidationError(msg)
        then_result = then_builder.stays_between(
            get_number(then, "min", _ctx(name)),
            get_number(then, "max", _ctx(name)),
        )

    return then_result.within(within_ms)

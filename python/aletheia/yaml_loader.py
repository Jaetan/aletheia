# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""YAML loader for declarative CAN signal checks.

Loads check definitions from YAML files or strings and compiles them
through the Check API into LTL properties.

Usage:
    from pathlib import Path
    from aletheia import AletheiaClient, load_checks

    # The kernel reads every number of a document, so a client is open first
    with AletheiaClient() as client:
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
    THEN_SLOTS,
    WHEN_CONDITIONS,
    dispatch_simple,
    dispatch_then,
    dispatch_when,
)
from aletheia._loader_utils import (
    NumberText,
    get_dict,
    get_int,
    get_number,
    get_str,
    reject_symlink_loader_path,
)
from aletheia.client._types import ValidationError, check_dbc_text_size_bound
from aletheia.types import is_object_list, is_str_dict

if TYPE_CHECKING:
    from collections.abc import Mapping
    from fractions import Fraction
    from typing import TextIO

    from aletheia.checks import CheckResult
    from aletheia.types import JSONValue


# The tags that would turn a scalar into something other than its text: a
# number, a YAML 1.1 boolean (``true``, ``yes``, ``on``), a date, or the ``=``
# value key.
_YAML_TEXT_TAGS = (
    "tag:yaml.org,2002:int",
    "tag:yaml.org,2002:float",
    "tag:yaml.org,2002:bool",
    "tag:yaml.org,2002:timestamp",
    "tag:yaml.org,2002:value",
)

# The kernel decides what a number is, so the loader hands it every number as
# the document spells it.  This ``yaml.SafeLoader`` subclass drops PyYAML's
# implicit resolvers for those tags, so a plain ``42``, ``0x1F``, ``1.5``,
# ``yes``, ``2024-01-01`` or ``=`` stays a string (no key of a check reads a
# boolean or a date), and constructs a scalar explicitly tagged with one of
# them as its text; :func:`~aletheia._loader_utils.get_number` hands that text
# to the kernel.  The null resolver stays, so an empty value or
# ``~`` reads as missing.  Everything else inherits ``SafeLoader``'s safe
# construction (no arbitrary object instantiation).  Built with ``type()``
# rather than a ``class`` statement so the subclass does not inherit
# ``SafeLoader``'s deep ancestry into a flagged ``too-many-ancestors``; the
# fresh resolver dict (and fresh inner lists) and ``add_constructor``'s copy of
# the constructor table leave the parent's tables untouched.
_TextNumberSafeLoader: type[yaml.SafeLoader] = type(
    "_TextNumberSafeLoader",
    (yaml.SafeLoader,),
    {
        "yaml_implicit_resolvers": {
            first_char: [(tag, regexp) for tag, regexp in resolvers if tag not in _YAML_TEXT_TAGS]
            for first_char, resolvers in yaml.SafeLoader.yaml_implicit_resolvers.items()
        }
    },
)


def _construct_scalar_text(loader: yaml.SafeLoader, node: yaml.Node) -> NumberText:
    """Construct a scalar tagged ``!!int``, ``!!float``, ``!!bool`` or ``!!timestamp`` as its text.

    A tag of these on a mapping or a sequence has no text, and is invalid YAML
    with PyYAML's own wording, a mapping holding a ``=`` key included (which
    ``construct_scalar`` would read as that key's value).
    """
    if not isinstance(node, yaml.ScalarNode):
        raise yaml.MarkedYAMLError(
            problem=f"expected a scalar node, but found {node.id}", problem_mark=node.start_mark
        )
    return NumberText(loader.construct_scalar(node))


for _tag in _YAML_TEXT_TAGS:
    _TextNumberSafeLoader.add_constructor(_tag, _construct_scalar_text)


def _safe_load_text_numbers(stream: str | TextIO) -> object:
    """Parse *stream* with :class:`_TextNumberSafeLoader`, every number kept as its text.

    Invalid YAML raises :class:`ValidationError` reading ``invalid YAML:`` and
    PyYAML's reason, as the Go, C++ and Rust loaders refuse it.  Drives the
    loader instance directly, exactly as PyYAML's own ``yaml.load`` does,
    rather than calling ``yaml.load(stream, Loader=...)``.  The subclass is as
    safe as :class:`yaml.SafeLoader` (it only keeps scalars as text), but the
    ``yaml.load`` *call form* is what the security linter pattern-matches;
    using the loader directly needs no lint suppression.
    """
    try:
        loader = _TextNumberSafeLoader(stream)
        try:
            return loader.get_single_data()
        finally:
            loader.dispose()
    except yaml.YAMLError as exc:
        msg = f"invalid YAML: {exc}"
        raise ValidationError(msg) from exc


def _ctx(name: str) -> str:
    """Format a check name as an error context string."""
    return f"Check '{name}'"


def _check_name(entry: Mapping[str, JSONValue]) -> str:
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
        ValidationError: Invalid YAML, or an invalid check definition (missing
            fields, unknown condition, a number the kernel refuses, carrying
            the kernel's code)
        InputBoundExceededError: The document is larger than
            :data:`aletheia.limits.MAX_DBC_TEXT_BYTES`, or a number has a
            component past
            :data:`aletheia.limits.MAX_RATIONAL_COMPONENT_MAGNITUDE` (``field``
            ``"decimal"``)
        FFIError: The GHC runtime is not up (no client has started it), so
            the kernel cannot read a number
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
    """
    if isinstance(source, Path):
        reject_symlink_loader_path(source, "YAML")
        check_dbc_text_size_bound(source.stat().st_size)
        # open()'s encoding is NOT droppable (its default is the locale, not
        # utf-8), and "UTF-8" is a codec-name alias of "utf-8" → both the
        # case and the None mutant are runtime-equivalent here (pragma).
        with source.open(encoding="utf-8") as f:  # pragma: no mutate
            return _safe_load_text_numbers(f)
    # source: str — the public ``load_checks`` signature constrains this
    # branch by type; basedpyright/pyright catches non-(str|Path) callers
    # statically, so a runtime defensive ``isinstance(source, str)`` would
    # be dead code and is not added.
    check_dbc_text_size_bound(len(source.encode()))  # str.encode defaults to utf-8
    return _safe_load_text_numbers(source)


def _parse_check(entry: Mapping[str, JSONValue]) -> CheckResult:
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
    entry: Mapping[str, JSONValue],
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
    entry: Mapping[str, JSONValue],
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
    entry: Mapping[str, JSONValue],
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
    entry: Mapping[str, JSONValue],
) -> CheckResult:
    """Parse an equals simple check."""
    if "value" not in entry:
        msg = f"Check '{name}': condition 'equals' requires 'value'"
        raise ValidationError(msg)
    return checks.signal(signal).equals(get_number(entry, "value", _ctx(name))).always()


def _parse_simple_check(entry: Mapping[str, JSONValue]) -> CheckResult:
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

    # Unreachable: the dispatch above is exhaustive over ALL_SIMPLE_CONDITIONS
    # (the union of the VALUE / RANGE / SETTLES / EQUALS sub-sets), which the
    # `condition not in ALL_SIMPLE_CONDITIONS` guard already enforced.  Kept as
    # a type-required defensive fallback against the sub-sets drifting.
    # pragma: no mutate start
    msg = f"Check '{name}': unknown condition '{condition}'"
    raise ValidationError(msg)
    # pragma: no mutate end


def _then_values(
    then: Mapping[str, JSONValue],
    then_cond: str,
    name: str,
) -> dict[str, int | Fraction]:
    """Read the value slots the obligation takes, under this loader's own keys.

    Which slots those are is THEN_SLOTS' business; which keys hold them, and
    what to say when one is missing, is this loader's.  Only the slots the
    obligation reads are returned, so nothing carries a filler.
    """
    if THEN_SLOTS[then_cond] == "value":
        return {"value": get_number(then, "value", _ctx(name))}
    if "min" not in then or "max" not in then:
        msg = f"Check '{name}': then condition '{then_cond}' requires 'min' and 'max'"
        raise ValidationError(msg)
    return {
        "lo": get_number(then, "min", _ctx(name)),
        "hi": get_number(then, "max", _ctx(name)),
    }


def _parse_when_then_check(entry: Mapping[str, JSONValue]) -> CheckResult:
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

    return dispatch_then(then_builder, then_cond, _then_values(then, then_cond, name)).within(
        within_ms
    )


__all__ = ["load_checks"]

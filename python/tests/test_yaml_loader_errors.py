# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Mutation-killing tests for yaml_loader validation/error paths.

The check parsers (``_parse_simple_check`` / ``_parse_when_then_check`` and
their condition helpers) reach their error branches only on malformed input,
which the happy-path tests in ``test_yaml_loader.py`` never supply.  Each test
here feeds a YAML check that trips exactly one branch and asserts the *exact*
``ValidationError`` message — equality (not a substring match) kills both the
uppercase and the ``"XX...XX"``-wrapped string-literal mutants, and the
embedded ``Check 'C'`` context kills the ``_ctx(name)`` argument mutants
(``_ctx(None)`` / ``None`` would render ``Check 'None'`` / ``None``).
"""

from __future__ import annotations

import textwrap
from typing import TYPE_CHECKING

import pytest

from aletheia import ValidationError
from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from pathlib import Path


def _err(yaml_body: str) -> str:
    """Load *yaml_body* expecting a ValidationError; return its message."""
    with pytest.raises(ValidationError) as excinfo:
        load_checks(textwrap.dedent(yaml_body))
    return str(excinfo.value)


class TestLoadChecksStructure:
    """load_checks top-level structural validation."""

    def test_root_not_a_checks_mapping(self) -> None:
        """Reject a root that is not a mapping with a 'checks' key."""
        assert _err("just a string") == "YAML must contain a 'checks' list"

    def test_checks_not_a_list(self) -> None:
        """Reject a 'checks' value that is not a list."""
        assert _err("checks: 5") == "YAML must contain a 'checks' list"

    def test_check_entry_not_a_mapping(self) -> None:
        """Reject a check entry that is not a mapping."""
        assert _err("checks:\n  - 5") == "Each check must be a YAML mapping"

    def test_check_without_signal_or_when(self) -> None:
        """Reject a check with neither 'signal' nor 'when'/'then'."""
        assert (
            _err("checks:\n  - name: C\n    foo: bar")
            == "Check 'C': must have 'signal' or 'when'/'then'"
        )

    def test_symlink_path_rejected(self, tmp_path: Path) -> None:
        """Reject a symlinked YAML path, naming the 'YAML' loader kind."""
        real = tmp_path / "real.yaml"
        real.write_text("checks: []\n", encoding="utf-8")
        link = tmp_path / "link.yaml"
        link.symlink_to(real)
        with pytest.raises(ValidationError) as excinfo:
            load_checks(link)
        assert str(excinfo.value).startswith("YAML file is a symbolic link; refusing to load:")


class TestSimpleCheckErrors:
    """_parse_simple_check + its condition helpers."""

    def test_condition_not_a_string(self) -> None:
        """Reject a non-string 'condition'."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: [1]")
            == "Check 'C': 'condition' must be a string"
        )

    def test_condition_missing_is_empty_unknown(self) -> None:
        """Report a missing 'condition' (defaults to '') as unknown."""
        assert _err("checks:\n  - name: C\n    signal: S") == "Check 'C': unknown condition ''"

    def test_unknown_condition(self) -> None:
        """Reject an unrecognized condition string."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: bogus")
            == "Check 'C': unknown condition 'bogus'"
        )

    def test_signal_not_a_string(self) -> None:
        """Reject a 'signal' key that is present but not a string.

        (An absent 'signal' key dispatches earlier in _parse_check to the
        'must have signal or when/then' branch, so the key must be present.)
        """
        body = "checks:\n  - name: C\n    signal: [1]\n    condition: never_exceeds\n    value: 1"
        assert _err(body) == "Check 'C': missing or invalid 'signal' (expected string)"

    def test_value_condition_requires_value(self) -> None:
        """Reject never_exceeds without 'value' (naming the condition)."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: never_exceeds")
            == "Check 'C': condition 'never_exceeds' requires 'value'"
        )

    def test_value_condition_value_not_a_number(self) -> None:
        """Reject never_exceeds with a non-numeric 'value'."""
        body = "checks:\n  - name: C\n    signal: S\n    condition: never_exceeds\n    value: abc"
        assert _err(body) == "Check 'C': missing or invalid 'value' (expected number)"

    def test_range_condition_requires_min_and_max(self) -> None:
        """Reject stays_between without 'min' (naming the condition)."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: stays_between\n    max: 1")
            == "Check 'C': condition 'stays_between' requires 'min' and 'max'"
        )

    def test_range_condition_min_not_a_number(self) -> None:
        """Reject stays_between with a non-numeric 'min'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: stays_between\n"
            "    min: abc\n    max: 1"
        )
        assert _err(body) == "Check 'C': missing or invalid 'min' (expected number)"

    def test_range_condition_max_not_a_number(self) -> None:
        """Reject stays_between with a non-numeric 'max'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: stays_between\n"
            "    min: 1\n    max: abc"
        )
        assert _err(body) == "Check 'C': missing or invalid 'max' (expected number)"

    def test_settles_requires_min_and_max(self) -> None:
        """Reject settles_between with 'min' but no 'max' (the and/or guard)."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            "    min: 1\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': condition 'settles_between' requires 'min' and 'max'"

    def test_settles_requires_within_ms(self) -> None:
        """Reject settles_between without 'within_ms'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            "    min: 1\n    max: 2"
        )
        assert _err(body) == "Check 'C': condition 'settles_between' requires 'within_ms'"

    def test_settles_min_not_a_number(self) -> None:
        """Reject settles_between with a non-numeric 'min'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            "    min: abc\n    max: 2\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'min' (expected number)"

    def test_settles_max_not_a_number(self) -> None:
        """Reject settles_between with a non-numeric 'max'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            "    min: 1\n    max: abc\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'max' (expected number)"

    def test_settles_within_ms_not_an_int(self) -> None:
        """Reject settles_between with a non-integer 'within_ms'."""
        body = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            "    min: 1\n    max: 2\n    within_ms: abc"
        )
        assert _err(body) == "Check 'C': missing or invalid 'within_ms' (expected integer)"

    def test_equals_requires_value(self) -> None:
        """Reject equals without 'value' (naming the condition)."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: equals")
            == "Check 'C': condition 'equals' requires 'value'"
        )

    def test_equals_value_not_a_number(self) -> None:
        """Reject equals with a non-numeric 'value'."""
        assert (
            _err("checks:\n  - name: C\n    signal: S\n    condition: equals\n    value: abc")
            == "Check 'C': missing or invalid 'value' (expected number)"
        )


class TestWhenThenCheckErrors:
    """_parse_when_then_check validation branches."""

    def test_within_ms_not_an_int(self) -> None:
        """Reject a when/then check with a non-integer 'within_ms'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: abc"
        )
        assert _err(body) == "Check 'C': missing or invalid 'within_ms' (expected integer)"

    def test_when_not_a_mapping(self) -> None:
        """Reject a when/then check with a non-mapping 'when'."""
        body = (
            "checks:\n  - name: C\n    when: 5\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'when' (expected mapping)"

    def test_then_not_a_mapping(self) -> None:
        """Reject a when/then check with a non-mapping 'then'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: 5\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'then' (expected mapping)"

    def test_when_condition_missing(self) -> None:
        """Reject a when clause without 'condition'."""
        body = (
            "checks:\n  - name: C\n    when: {signal: A, value: 1}\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'condition' (expected string)"

    def test_when_unknown_condition(self) -> None:
        """Reject a when clause with an unrecognized condition."""
        body = (
            "checks:\n  - name: C\n    when: {condition: bogus, signal: A, value: 1}\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': unknown when condition 'bogus'"

    def test_when_signal_missing(self) -> None:
        """Reject a when clause without 'signal'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, value: 1}\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'signal' (expected string)"

    def test_when_value_not_a_number(self) -> None:
        """Reject a when clause with a non-numeric 'value'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: abc}\n"
            "    then: {condition: equals, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'value' (expected number)"

    def test_then_condition_missing(self) -> None:
        """Reject a then clause without 'condition'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'condition' (expected string)"

    def test_then_unknown_condition(self) -> None:
        """Reject a then clause with an unrecognized condition."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: bogus, signal: B, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': unknown then condition 'bogus'"

    def test_then_signal_missing(self) -> None:
        """Reject a then clause without 'signal'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: equals, value: 2}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'signal' (expected string)"

    def test_then_equals_value_not_a_number(self) -> None:
        """Reject a then 'equals' clause with a non-numeric 'value'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: equals, signal: B, value: abc}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'value' (expected number)"

    def test_then_exceeds_value_not_a_number(self) -> None:
        """Reject a then 'exceeds' clause with a non-numeric 'value'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: exceeds, signal: B, value: abc}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'value' (expected number)"

    def test_then_stays_between_requires_min_and_max(self) -> None:
        """Reject a then 'stays_between' clause without 'min'/'max'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: stays_between, signal: B}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': then condition 'stays_between' requires 'min' and 'max'"

    def test_then_stays_between_min_present_max_missing(self) -> None:
        """Reject a then 'stays_between' with 'min' but no 'max' (the and/or guard)."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: stays_between, signal: B, min: 1}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': then condition 'stays_between' requires 'min' and 'max'"

    def test_then_stays_between_min_not_a_number(self) -> None:
        """Reject a then 'stays_between' clause with a non-numeric 'min'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: stays_between, signal: B, min: abc, max: 1}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'min' (expected number)"

    def test_then_stays_between_max_not_a_number(self) -> None:
        """Reject a then 'stays_between' clause with a non-numeric 'max'."""
        body = (
            "checks:\n  - name: C\n    when: {condition: exceeds, signal: A, value: 1}\n"
            "    then: {condition: stays_between, signal: B, min: 1, max: abc}\n    within_ms: 10"
        )
        assert _err(body) == "Check 'C': missing or invalid 'max' (expected number)"

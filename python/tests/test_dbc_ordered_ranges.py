# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel refuses a DBC whose ranges admit no value or whose labels label nothing.

A minimum above its maximum, on a signal, a numeric attribute definition or an
environment variable, refuses the load with an error-severity
``min_exceeds_max`` naming the subject and both numbers; equal bounds load. A
value description key no raw value of its signal's bits takes, the signedness
and the bit length deciding, refuses the load with
``value_description_key_out_of_range``.
"""

from __future__ import annotations

from typing import NewType

import pytest

from aletheia import AletheiaClient, ValidationIssue
from aletheia.codes import IssueCode, IssueSeverity
from aletheia.common_types import Prose

DBCText = NewType("DBCText", str)
# The geometry, scaling, range and unit of an SG_ line, as the line spells them.
SignalSpec = NewType("SignalSpec", str)
# A value description key as a VAL_ line spells it.
KeyText = NewType("KeyText", str)

_HEAD = 'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n'


def _dbc(signal: SignalSpec, tail: DBCText = DBCText("")) -> DBCText:
    """Return a one-message DBC text carrying ``signal`` as its only SG_ line, then ``tail``."""
    return DBCText(_HEAD + f" SG_ S : {signal} ECU\n" + tail)


_UNSIGNED = SignalSpec('0|8@1+ (1,0) [0|255] ""')
_SIGNED = SignalSpec('0|8@1- (1,0) [-128|127] ""')


def _refusal_issues(text: DBCText) -> list[ValidationIssue]:
    """Load ``text``, assert the kernel refuses it at validation, and return its issues."""
    with AletheiaClient() as client:
        response = client.parse_dbc_text(text)
    assert response["status"] == "error", response
    assert response["code"] == "handler_validation_failed"
    assert "issues" in response, response
    return response["issues"]


def _loads(text: DBCText) -> list[ValidationIssue]:
    """Load ``text``, assert the kernel accepts it, and return its warnings."""
    with AletheiaClient() as client:
        response = client.parse_dbc_text(text)
    assert response["status"] == "success", response
    return response["warnings"]


def _error(code: IssueCode, detail: Prose) -> ValidationIssue:
    return {"severity": IssueSeverity.ERROR, "code": code, "detail": detail}


class TestMinExceedsMax:
    """A minimum above its maximum refuses the load, wherever the range sits."""

    def test_signal_range_inverted_refuses_the_load(self) -> None:
        """A signal declared [10|5] is refused, the text naming both numbers."""
        issues = _refusal_issues(_dbc(SignalSpec('0|8@1+ (1,0) [10|5] ""')))
        assert (
            _error(
                IssueCode.MIN_EXCEEDS_MAX,
                Prose("Message 'M', signal 'S': minimum 10 exceeds maximum 5"),
            )
            in issues
        )

    @pytest.mark.parametrize(
        ("definition", "detail"),
        [
            (
                DBCText('BA_DEF_ SG_ "A" INT 10 5;'),
                Prose("Attribute 'A': minimum 10 exceeds maximum 5"),
            ),
            (
                DBCText('BA_DEF_ SG_ "A" FLOAT 10.5 5.25;'),
                Prose("Attribute 'A': minimum 10.5 exceeds maximum 5.25"),
            ),
            (
                DBCText('BA_DEF_ SG_ "A" HEX 10 5;'),
                Prose("Attribute 'A': minimum 10 exceeds maximum 5"),
            ),
        ],
    )
    def test_attribute_range_inverted_refuses_the_load(
        self, definition: DBCText, detail: Prose
    ) -> None:
        """A numeric attribute definition whose minimum exceeds its maximum is refused."""
        issues = _refusal_issues(_dbc(_UNSIGNED, DBCText(f"\n{definition}\n")))
        assert issues == [_error(IssueCode.MIN_EXCEEDS_MAX, detail)]

    def test_environment_variable_range_inverted_refuses_the_load(self) -> None:
        """An environment variable declared [10|5] is refused."""
        text = _dbc(
            _UNSIGNED, DBCText('\nEV_ V: 0 [10|5] "" 0 1 DUMMY_NODE_VECTOR0 Vector__XXX;\n')
        )
        assert _refusal_issues(text) == [
            _error(
                IssueCode.MIN_EXCEEDS_MAX,
                Prose("Environment variable 'V': minimum 10 exceeds maximum 5"),
            )
        ]

    def test_equal_bounds_load(self) -> None:
        """A range of one value admits that value: [5|5] on the signal, INT 5 5, EV_ [5|5]."""
        text = _dbc(
            SignalSpec('0|8@1+ (1,0) [5|5] ""'),
            DBCText(
                '\nEV_ V: 0 [5|5] "" 5 1 DUMMY_NODE_VECTOR0 Vector__XXX;\n'
                + '\nBA_DEF_ SG_ "A" INT 5 5;\n'
            ),
        )
        assert all(w["code"] != IssueCode.MIN_EXCEEDS_MAX for w in _loads(text))


class TestValueDescriptionKeyOutOfRange:
    """A key no raw value of the signal's bits takes refuses the load."""

    @staticmethod
    def _key_issue(key: KeyText) -> ValidationIssue:
        return _error(
            IssueCode.VALUE_DESCRIPTION_KEY_OUT_OF_RANGE,
            Prose(
                f"Message 'M', signal 'S': value description key {key}"
                + " lies outside the values its bits carry"
            ),
        )

    @pytest.mark.parametrize(
        ("signal", "key"),
        [
            (_UNSIGNED, KeyText("256")),
            (_UNSIGNED, KeyText("-1")),
            (_SIGNED, KeyText("128")),
            (_SIGNED, KeyText("-129")),
        ],
    )
    def test_key_past_the_bits_refuses_the_load(self, signal: SignalSpec, key: KeyText) -> None:
        """Past 2^8-1 or below 0 unsigned, past 127 or below -128 signed, a key is refused."""
        text = _dbc(signal, DBCText(f'\nVAL_ 256 S {key} "x" ;\n'))
        assert _refusal_issues(text) == [self._key_issue(key)]

    @pytest.mark.parametrize(
        ("signal", "low", "high"),
        [(_UNSIGNED, KeyText("0"), KeyText("255")), (_SIGNED, KeyText("-128"), KeyText("127"))],
    )
    def test_keys_at_the_ends_of_the_bits_load(
        self, signal: SignalSpec, low: KeyText, high: KeyText
    ) -> None:
        """Both ends of the raw range are labels a value can carry."""
        text = _dbc(signal, DBCText(f'\nVAL_ 256 S {low} "low" {high} "high" ;\n'))
        assert all(w["code"] != IssueCode.VALUE_DESCRIPTION_KEY_OUT_OF_RANGE for w in _loads(text))

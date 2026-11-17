# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A reply reader's refusal reads ``reply <path>: expected <what>, got <what came>``."""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import pytest

from aletheia import ProtocolError
from aletheia.client._helpers.reply_shape import (
    A_RATIONAL,
    OBJECT,
    REPLY_ROOT,
    STRING,
    Arrival,
    Expectation,
    ReplyPath,
    at,
    came,
    came_as,
    came_word,
    field_member,
    field_word,
    json_kind,
    read_rational,
    reply_refusal,
    words,
)
from aletheia.codes import ErrorCode, IssueCode, IssueSeverity

if TYPE_CHECKING:
    from enum import StrEnum
    from typing import LiteralString

    from aletheia.client._helpers.reply_shape import JSONKind, ReplyFields
    from aletheia.types import JSONValue

_ISSUES = ReplyPath("issues")
_RESULTS = ReplyPath("results")
_WARNINGS = ReplyPath("warnings")
_SEVERITIES = ("error", "warning")
_STATUSES = ("fails", "holds", "unresolved")
_AN_ISSUE_CODE = Expectation("an issue code")
_AN_ERROR_CODE = Expectation("an error code")


@pytest.mark.parametrize(
    ("value", "kind"),
    [
        (None, "null"),
        (True, "boolean"),
        (False, "boolean"),
        (0, "number"),
        (1.5, "number"),
        ("", "string"),
        ([], "array"),
        ({}, "object"),
    ],
)
def test_a_value_is_named_by_its_json_kind(value: JSONValue, kind: JSONKind) -> None:
    """A boolean is named as a boolean, though Python's ``bool`` is an ``int``."""
    assert json_kind(value) == kind


def test_a_key_the_reply_lacks_came_as_nothing_and_a_null_as_null() -> None:
    """An absent key and a key holding null are told apart."""
    obj: ReplyFields = {"present": None}
    assert (came(obj, "absent"), came(obj, "present")) == ("nothing", "null")


def test_a_word_place_quotes_a_string_and_names_any_other_value_by_kind() -> None:
    """A string at a word place came quoted; any other value came as its kind."""
    obj: ReplyFields = {"status": "ack", "type": 3}
    assert came_word(obj, "status") == '"ack"'
    assert (came_word(obj, "type"), came_word(obj, "kind")) == ("number", "nothing")
    assert came_as([1]) == "array"


def test_words_are_quoted_and_joined_with_a_final_or() -> None:
    """One word stands alone, two are joined by or, three by a comma then or."""
    assert words("error") == '"error"'
    assert words("success", "error") == '"success" or "error"'
    assert words("ack", "error", "property_batch") == '"ack", "error" or "property_batch"'


def test_a_refusal_names_its_place_and_the_whole_reply_names_none() -> None:
    """A place's keys are joined from the root; the whole reply reads ``reply:``."""
    place = at(at(at(ReplyPath("dbc"), "messages"), "signals"), "presence")
    refusal = reply_refusal(place, STRING, came_as(1))
    assert isinstance(refusal, ProtocolError)
    assert str(refusal) == "reply dbc/messages/signals/presence: expected string, got number"
    assert at(REPLY_ROOT, "message") == "message"
    assert (
        str(reply_refusal(REPLY_ROOT, OBJECT, came_as([]))) == "reply: expected object, got array"
    )


@pytest.mark.parametrize(
    ("value", "rational"),
    [(3, Fraction(3)), (-3, Fraction(-3)), ({"numerator": -3, "denominator": 2}, Fraction(-3, 2))],
)
def test_a_rational_is_a_number_or_its_numerator_and_denominator(
    value: JSONValue, rational: Fraction
) -> None:
    """The kernel writes an integral value as digits and a fraction as an object."""
    assert read_rational(value, ReplyPath("values/value")) == rational


@pytest.mark.parametrize(
    ("value", "arrival"),
    [
        (True, Arrival("boolean")),
        (1.5, Arrival("number")),
        ("1/2", Arrival("string")),
        ({"numerator": "1", "denominator": 2}, Arrival("object")),
        ({"numerator": 1, "denominator": True}, Arrival("object")),
        ({"numerator": 1}, Arrival("object")),
        ({"denominator": 5}, Arrival("object")),
        ({"numerator": 1, "denominator": "2"}, Arrival("object")),
        (None, Arrival("null")),
    ],
)
def test_anything_else_at_a_rational_place_is_refused(value: JSONValue, arrival: Arrival) -> None:
    """A boolean, a fraction literal, a string or a malformed object is no rational."""
    with pytest.raises(ProtocolError) as refused:
        _ = read_rational(value, ReplyPath("values/value"))
    assert str(refused.value) == f"reply values/value: expected {A_RATIONAL}, got {arrival}"


@pytest.mark.parametrize(
    ("path", "key", "expected", "word"),
    [
        (_ISSUES, "severity", _SEVERITIES, "error"),
        (_ISSUES, "severity", _SEVERITIES, "warning"),
        (_RESULTS, "type", ("property",), "property"),
        (_RESULTS, "status", _STATUSES, "fails"),
        (_RESULTS, "status", _STATUSES, "holds"),
        (_RESULTS, "status", _STATUSES, "unresolved"),
        (_WARNINGS, "kind", ("uncached_atom",), "uncached_atom"),
    ],
)
def test_a_word_place_holding_one_of_its_words_reads_it(
    path: ReplyPath, key: LiteralString, expected: tuple[LiteralString, ...], word: LiteralString
) -> None:
    """Each word of a place's set is read as written."""
    obj: ReplyFields = {key: word}
    assert field_word(obj, path, key, *expected) == word


@pytest.mark.parametrize(
    ("entry", "path", "key", "expected", "text"),
    [
        (
            {"severity": "fatal", "code": "factor_zero", "detail": "d"},
            _ISSUES,
            "severity",
            _SEVERITIES,
            'reply issues/severity: expected "error" or "warning", got "fatal"',
        ),
        (
            {"code": "factor_zero", "detail": "d"},
            _ISSUES,
            "severity",
            _SEVERITIES,
            'reply issues/severity: expected "error" or "warning", got nothing',
        ),
        (
            {"severity": 0, "code": "factor_zero", "detail": "d"},
            _ISSUES,
            "severity",
            _SEVERITIES,
            'reply issues/severity: expected "error" or "warning", got number',
        ),
        (
            {"type": "verdict", "status": "holds", "property_index": 0},
            _RESULTS,
            "type",
            ("property",),
            'reply results/type: expected "property", got "verdict"',
        ),
        (
            {"status": "holds", "property_index": 0},
            _RESULTS,
            "type",
            ("property",),
            'reply results/type: expected "property", got nothing',
        ),
        (
            {"type": 0, "status": "holds", "property_index": 0},
            _RESULTS,
            "type",
            ("property",),
            'reply results/type: expected "property", got number',
        ),
        (
            {"type": "property", "status": "bogus", "property_index": 0, "reason": "r"},
            _RESULTS,
            "status",
            _STATUSES,
            'reply results/status: expected "fails", "holds" or "unresolved", got "bogus"',
        ),
        (
            {"type": "property", "property_index": 0, "reason": "r"},
            _RESULTS,
            "status",
            _STATUSES,
            'reply results/status: expected "fails", "holds" or "unresolved", got nothing',
        ),
        (
            {"type": "property", "status": 0, "property_index": 0, "reason": "r"},
            _RESULTS,
            "status",
            _STATUSES,
            'reply results/status: expected "fails", "holds" or "unresolved", got number',
        ),
        (
            {"kind": "stale_atom", "property_index": 0, "detail": "d"},
            _WARNINGS,
            "kind",
            ("uncached_atom",),
            'reply warnings/kind: expected "uncached_atom", got "stale_atom"',
        ),
        (
            {"property_index": 0, "detail": "d"},
            _WARNINGS,
            "kind",
            ("uncached_atom",),
            'reply warnings/kind: expected "uncached_atom", got nothing',
        ),
        (
            {"kind": 0, "property_index": 0, "detail": "d"},
            _WARNINGS,
            "kind",
            ("uncached_atom",),
            'reply warnings/kind: expected "uncached_atom", got number',
        ),
    ],
)
def test_a_word_place_refuses_any_other_value_expecting_its_words(
    entry: ReplyFields,
    path: ReplyPath,
    key: LiteralString,
    expected: tuple[LiteralString, ...],
    text: LiteralString,
) -> None:
    """An unknown word came quoted, a non-string as its kind, a missing key as nothing."""
    with pytest.raises(ProtocolError) as refused:
        _ = field_word(entry, path, key, *expected)
    assert str(refused.value) == text


@pytest.mark.parametrize(
    ("path", "key", "members", "expected"),
    [
        (_ISSUES, "severity", IssueSeverity, words(*_SEVERITIES)),
        (_ISSUES, "code", IssueCode, _AN_ISSUE_CODE),
        (REPLY_ROOT, "code", ErrorCode, _AN_ERROR_CODE),
    ],
)
def test_a_code_place_reads_each_member_by_its_word(
    path: ReplyPath, key: LiteralString, members: type[StrEnum], expected: Expectation
) -> None:
    """The member a word names is returned itself, not its word."""
    read = [field_member({key: member.value}, path, key, members, expected) for member in members]
    assert (read, [type(got) for got in read]) == (list(members), [members] * len(read))


@pytest.mark.parametrize(
    ("entry", "path", "members", "expected", "text"),
    [
        (
            {"severity": "warning", "code": "some_future_code", "detail": "d"},
            _ISSUES,
            IssueCode,
            _AN_ISSUE_CODE,
            'reply issues/code: expected an issue code, got "some_future_code"',
        ),
        (
            {"severity": "warning", "detail": "d"},
            _ISSUES,
            IssueCode,
            _AN_ISSUE_CODE,
            "reply issues/code: expected an issue code, got nothing",
        ),
        (
            {"severity": "warning", "code": 0, "detail": "d"},
            _ISSUES,
            IssueCode,
            _AN_ISSUE_CODE,
            "reply issues/code: expected an issue code, got number",
        ),
        (
            {"status": "error", "code": "c", "message": "m"},
            REPLY_ROOT,
            ErrorCode,
            _AN_ERROR_CODE,
            'reply code: expected an error code, got "c"',
        ),
        (
            {"status": "error", "message": "m"},
            REPLY_ROOT,
            ErrorCode,
            _AN_ERROR_CODE,
            "reply code: expected an error code, got nothing",
        ),
        (
            {"status": "error", "code": 0, "message": "m"},
            REPLY_ROOT,
            ErrorCode,
            _AN_ERROR_CODE,
            "reply code: expected an error code, got number",
        ),
    ],
)
def test_a_code_place_refuses_any_other_value_expecting_its_own_text(
    entry: ReplyFields,
    path: ReplyPath,
    members: type[StrEnum],
    expected: Expectation,
    text: LiteralString,
) -> None:
    """An unknown code came quoted, a non-string as its kind, a missing key as nothing."""
    with pytest.raises(ProtocolError) as refused:
        _ = field_member(entry, path, "code", members, expected)
    assert str(refused.value) == text


@pytest.mark.parametrize(
    ("value", "kind"),
    [(None, "null"), (True, "boolean"), (1.5, "number"), ([], "array"), ({}, "object")],
)
def test_a_word_or_code_place_names_a_non_string_by_its_kind(
    value: JSONValue, kind: JSONKind
) -> None:
    """A word place and a code place each expect their own text whatever kind came."""
    obj: ReplyFields = {"severity": value, "code": value}
    with pytest.raises(ProtocolError) as word_refused:
        _ = field_word(obj, _ISSUES, "severity", *_SEVERITIES)
    with pytest.raises(ProtocolError) as code_refused:
        _ = field_member(obj, _ISSUES, "code", IssueCode, _AN_ISSUE_CODE)
    assert (str(word_refused.value), str(code_refused.value)) == (
        f'reply issues/severity: expected "error" or "warning", got {kind}',
        f"reply issues/code: expected an issue code, got {kind}",
    )

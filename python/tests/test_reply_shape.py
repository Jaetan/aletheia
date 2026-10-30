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
    ReplyPath,
    at,
    came,
    came_as,
    came_word,
    json_kind,
    read_rational,
    reply_refusal,
    words,
)

if TYPE_CHECKING:
    from aletheia.client._helpers.reply_shape import JSONKind, ReplyFields
    from aletheia.types import JSONValue


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

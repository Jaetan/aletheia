# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The refusal every reply reader raises for a place holding what the kernel never writes there.

A refusal reads ``reply <path>: expected <what>, got <what came>``. The path is
the reply proof's: the keys from the reply's root joined by ``/``, an array's
entries keeping the array's path, the whole reply's path empty (``reply:
expected object, got array``). What is expected and what came are JSON kinds,
``string``, ``boolean``, ``number``, ``array``, ``object`` or ``null``, and a
key the reply lacks came as ``nothing``. A rational place expects ``a
rational``: a number, or the ``{numerator, denominator}`` object the kernel
writes a fraction as. A place holding one of a set of words expects them
quoted, and a string outside them came quoted; a code place, holding a member
of a code enumeration, expects its own text, such as ``an issue code``. A
whole-number place expects a ``number`` written as digits, all the kernel
writes there.

A reader narrows each place itself and builds its refusal here: ``held``
reads what a key holds, ``came`` names what a key held, ``came_as`` what a
value is, ``came_word`` what a word place held. ``field_word`` reads a word
place whole and ``field_member`` a code place.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import TYPE_CHECKING, Literal, LiteralString, NewType, Protocol

from aletheia.client._types import ProtocolError
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from collections.abc import Mapping
    from enum import StrEnum

    from aletheia.types import JSONValue

ReplyPath = NewType("ReplyPath", str)
"""A place in a reply: its keys from the root joined by ``/``, empty for the whole reply."""

REPLY_ROOT = ReplyPath("")

type JSONKind = Literal["string", "boolean", "number", "array", "object", "null"]

Expectation = NewType("Expectation", str)
"""What a place holds: a JSON kind, ``a rational``, or its words quoted."""

Arrival = NewType("Arrival", str)
"""What came at a place: a JSON kind, a string quoted at a word place, or ``nothing``."""

STRING = Expectation("string")
BOOLEAN = Expectation("boolean")
NUMBER = Expectation("number")
ARRAY = Expectation("array")
OBJECT = Expectation("object")
A_RATIONAL = Expectation("a rational")

_NOTHING = Arrival("nothing")


class ReplyFields(Protocol):
    """An object of a decoded reply, read by the keys its reader names."""

    def __contains__(self, key: LiteralString, /) -> bool: ...

    def __getitem__(self, key: LiteralString, /) -> JSONValue: ...


def held(obj: ReplyFields, key: LiteralString) -> JSONValue:
    """Read ``key`` of a reply object: its value, or ``None`` when the object lacks it."""
    if key not in obj:
        return None
    return obj[key]


def at(path: ReplyPath, key: LiteralString) -> ReplyPath:
    """Name the place of ``key`` in the object at ``path``, the key alone at the reply's root."""
    return ReplyPath(key if path == REPLY_ROOT else f"{path}/{key}")


def json_kind(value: JSONValue) -> JSONKind:
    """Name the JSON kind of a decoded value, ``bool`` read before ``int``, its subclass.

    The cases cover ``JSONValue`` whole, and the type checker refuses a match
    missing one.
    """
    match value:
        case None:
            return "null"
        case bool():
            return "boolean"
        case int() | float():
            return "number"
        case str():
            return "string"
        case list():
            return "array"
        case dict():
            return "object"


def came_as(value: JSONValue) -> Arrival:
    """Name what came at a place: the JSON kind of its value."""
    return Arrival(json_kind(value))


def came(obj: ReplyFields | Mapping[str, object], key: LiteralString) -> Arrival:
    """Name what ``key`` held in ``obj``: its value's JSON kind, or ``nothing``.

    ``obj`` is a reply object or a typed entry built from one, a ``dict`` with
    string keys either way, which ``is_str_dict`` reads as JSON.
    """
    return came_as(obj[key]) if key in obj and is_str_dict(obj) else _NOTHING


def came_word(obj: ReplyFields, key: LiteralString) -> Arrival:
    """Name what a word place held: its string quoted, another value's kind, or ``nothing``."""
    if key in obj and isinstance(value := obj[key], str):
        return Arrival(json.dumps(value))
    return came(obj, key)


def words(*expected: LiteralString) -> Expectation:
    """Name a word place's words quoted: ``"a"``, ``"a" or "b"``, ``"a", "b" or "c"``."""
    quoted = [json.dumps(word) for word in expected]
    if len(quoted) == 1:
        return Expectation(quoted[0])
    return Expectation(f"{', '.join(quoted[:-1])} or {quoted[-1]}")


def reply_refusal(path: ReplyPath, expected: Expectation, arrival: Arrival) -> ProtocolError:
    """Build the refusal of a reply place: ``reply <path>: expected <expected>, got <arrival>``."""
    where = "reply" if path == REPLY_ROOT else f"reply {path}"
    return ProtocolError(f"{where}: expected {expected}, got {arrival}")


def field_word[W: LiteralString](
    obj: ReplyFields, path: ReplyPath, key: LiteralString, *expected: W
) -> W:
    """Read the word at ``key`` of the object at ``path``, one of ``expected`` or refused."""
    value = held(obj, key)
    for word in expected:
        if word == value:
            return word
    raise reply_refusal(at(path, key), words(*expected), came_word(obj, key))


def field_member[M: StrEnum](
    obj: ReplyFields, path: ReplyPath, key: LiteralString, members: type[M], expected: Expectation
) -> M:
    """Read the member of ``members`` whose value is the word at ``key`` of the object at ``path``.

    Any other value is refused at its place as ``expected``.
    """
    if isinstance(word := held(obj, key), str) and word in members:
        return members(word)
    raise reply_refusal(at(path, key), expected, came_word(obj, key))


def read_rational(value: JSONValue, path: ReplyPath) -> Fraction:
    """Read the rational at ``path``, a number or its ``{numerator, denominator}`` object.

    Anything else is refused as ``a rational`` expected. A zero denominator
    raises Fraction's own error, the kernel writing none.
    """
    if isinstance(value, int) and not isinstance(value, bool):
        return Fraction(value)
    if is_str_dict(value):
        numerator, denominator = value.get("numerator"), value.get("denominator")
        if (
            isinstance(numerator, int)
            and not isinstance(numerator, bool)
            and isinstance(denominator, int)
            and not isinstance(denominator, bool)
        ):
            return Fraction(numerator, denominator)
    raise reply_refusal(path, A_RATIONAL, came_as(value))

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
quoted, and a string outside them came quoted. A whole-number place expects a
``number`` written as digits, all the kernel writes there.

A reader narrows each place itself and builds its refusal here: ``came``
names what a key held, ``came_as`` what a value is, ``came_word`` what a word
place held.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import TYPE_CHECKING, Literal, LiteralString, NewType, Protocol, assert_never, cast

from aletheia.client._types import ProtocolError
from aletheia.types import is_str_dict

if TYPE_CHECKING:
    from aletheia.types import JSONValue, Response

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


def fields(reply: Response) -> ReplyFields:
    """Read a reply held as its typed dictionary by the keys its reader names."""
    return cast("ReplyFields", reply)


def at(path: ReplyPath, key: LiteralString) -> ReplyPath:
    """Name the place of ``key`` in the object at ``path``."""
    return ReplyPath(f"{path}/{key}" if path else key)


def json_kind(value: JSONValue) -> JSONKind:
    """Name the JSON kind of a decoded value, ``bool`` read before ``int``, its subclass."""
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
        case _:
            assert_never(value)


def came_as(value: JSONValue) -> Arrival:
    """Name what came at a place: the JSON kind of its value."""
    return Arrival(json_kind(value))


def came(obj: ReplyFields, key: LiteralString) -> Arrival:
    """Name what ``key`` held in ``obj``: its value's JSON kind, or ``nothing``."""
    return came_as(obj[key]) if key in obj else _NOTHING


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
    where = f"reply {path}" if path else "reply"
    return ProtocolError(f"{where}: expected {expected}, got {arrival}")


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

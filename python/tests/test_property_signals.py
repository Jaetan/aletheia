# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A property's signal is decided as it is read: an identifier, then a signal of the loaded DBC.

``setProperties`` refuses a name past ``max-identifier-length`` with the bound's own code, a
DBC keyword, a name that is not an identifier, and a name no signal of the DBC carries; a
name the DBC carries is accepted.  Every row is the kernel's reply to one command.
"""

from __future__ import annotations

import json
from typing import Final, NamedTuple, NewType

import pytest
from _kernel_rows import (
    CodePoint,
    Command,
    FieldName,
    Index,
    KernelMessage,
    Keyword,
    Located,
    NameLength,
    kernel_reply,
    refusal,
)

from aletheia.codes import ErrorCode
from aletheia.common_types import Prose

# A DBC text, as a file holds it.
DBCText = NewType("DBCText", str)
# A signal name as a property spells it.
SignalName = NewType("SignalName", str)


class Refusal(NamedTuple):
    """One property signal name and the kernel's refusal of it."""

    label: Prose
    signal: SignalName
    code: ErrorCode
    message: KernelMessage
    located: Located


_DBC: Final = DBCText(
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: N\n\nBO_ 1 M: 8 N\n'
    + ' SG_ Speed : 0|8@1+ (1,0) [0|1] "u" N\n\n'
)
_LOAD: Final = Command(
    json.dumps({"type": "command", "command": "parseDBCText", "text": _DBC}).encode()
)

_REFUSED: Final = (
    Refusal(
        Prose("a signal no signal of the DBC carries"),
        SignalName("Nope"),
        ErrorCode.HANDLER_UNKNOWN_SIGNAL,
        KernelMessage("SetProperties: signal 'Nope' not found in DBC"),
        {},
    ),
    Refusal(
        Prose("a signal name of 129 characters"),
        SignalName("S" * 129),
        ErrorCode.INPUT_BOUND_EXCEEDED,
        KernelMessage("SetProperties: signal: identifier length 129 exceeds limit 128"),
        {
            "field": FieldName("signal"),
            "bound_kind": "identifier_length",
            "observed": NameLength(129),
            "limit": NameLength(128),
        },
    ),
    Refusal(
        Prose("a signal name holding a character outside ASCII"),
        SignalName("S\u00e9"),
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            "SetProperties: signal: character at index 1 (code point 233) "
            + "is outside the DBC character set"
        ),
        {"field": FieldName("signal"), "index": Index(1), "code_point": CodePoint(233)},
    ),
    Refusal(
        Prose("a DBC keyword as a signal name"),
        SignalName("BO_"),
        ErrorCode.DBC_KEYWORD_NAME,
        KernelMessage("SetProperties: signal: 'BO_' is a DBC keyword"),
        {"field": FieldName("signal"), "keyword": Keyword("BO_")},
    ),
    Refusal(
        Prose("a signal name that is not an identifier"),
        SignalName("1abc"),
        ErrorCode.PARSE_INVALID_IDENTIFIER,
        KernelMessage(
            "SetProperties: signal: '1abc' is not a valid DBC identifier "
            + "(must start with letter or '_', followed by alphanumerics or '_')"
        ),
        {"field": FieldName("signal")},
    ),
)


def _property_command(signal: SignalName) -> Command:
    predicate = {"predicate": "lessThan", "signal": signal, "value": 250}
    formula = {"operator": "always", "formula": {"operator": "atomic", "predicate": predicate}}
    return Command(
        json.dumps(
            {"type": "command", "command": "setProperties", "properties": [formula]}
        ).encode()
    )


@pytest.mark.parametrize("row", _REFUSED, ids=[row.label for row in _REFUSED])
def test_a_property_signal_outside_the_dbc_or_the_bound_is_refused(row: Refusal) -> None:
    """The kernel refuses the name with its code before any property is kept."""
    reply = kernel_reply(_property_command(row.signal), after=_LOAD)
    assert reply == refusal(row.code, row.message, row.located), row.label


def test_a_property_on_a_signal_of_the_dbc_is_accepted() -> None:
    """A name the DBC carries passes both checks."""
    assert kernel_reply(_property_command(SignalName("Speed")), after=_LOAD) == {
        "status": "success",
        "message": "Properties set successfully",
    }

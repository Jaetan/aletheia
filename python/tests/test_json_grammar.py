# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
r"""The kernel reads a command as RFC 8259 JSON text, and every reply it writes is such text.

A command is one JSON value with nothing after it.  Whitespace is space, tab,
line feed and carriage return; an integer has no leading zero; a string holds
no raw character below U+0020, and a ``\u`` escape names a Unicode scalar
value, a surrogate pair read as one character and a lone half refused.  A
reply escapes every control character it echoes, so every JSON reader reads it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, NewType, cast

import pytest

from aletheia import FFIBackend
from aletheia.client._ffi import KernelResponse, parse_json_object
from aletheia.common_types import Prose

if TYPE_CHECKING:
    from aletheia.types import Response

# A command's bytes, as the kernel receives them.
Command = NewType("Command", bytes)

# The column of the first character the kernel cannot read.
Column = NewType("Column", int)

# A message type the kernel echoes, as the reply's reader decodes it.
MessageType = NewType("MessageType", str)

_REFUSED: Final = (
    (
        Prose("a raw control character in a string"),
        Command(b'{"type": "a\x01b", "command": "validateDBC"}'),
        Column(12),
    ),
    (
        Prose("text after the value"),
        Command(b'{"type": "command", "command": "startStream"}xyz'),
        Column(46),
    ),
    (
        Prose("a vertical tab as whitespace"),
        Command(b'\x0b{"type": "command", "command": "startStream"}'),
        Column(1),
    ),
    (
        Prose("a no-break space as whitespace"),
        Command('\N{NO-BREAK SPACE}{"type": "command", "command": "startStream"}'.encode()),
        Column(1),
    ),
    (
        Prose("an integer with a leading zero"),
        Command(b'{"type": "command", "command": "startStream", "x": 01}'),
        Column(53),
    ),
    (Prose("a lone high surrogate"), Command(b'{"type": "\\ud800"}'), Column(17)),
    (Prose("a lone low surrogate"), Command(b'{"type": "\\udc00"}'), Column(17)),
)

_ECHOED: Final = (
    (
        Prose("a surrogate pair, read as one character"),
        Command(b'{"type": "\\ud83d\\ude00"}'),
        MessageType("\N{GRINNING FACE}"),
    ),
    (Prose("a backspace"), Command(b'{"type": "a\\bb"}'), MessageType("a\bb")),
    (Prose("a NUL"), Command(b'{"type": "a\\u0000b"}'), MessageType("a\x00b")),
    (Prose("a unit separator"), Command(b'{"type": "a\\u001fb"}'), MessageType("a\x1fb")),
)


def _answer(command: Command) -> Response:
    backend = FFIBackend()
    state = backend.init()
    try:
        return cast("Response", parse_json_object(KernelResponse(backend.process(state, command))))
    finally:
        backend.close(state)


@pytest.mark.parametrize(("label", "command", "column"), _REFUSED, ids=[row[0] for row in _REFUSED])
def test_text_outside_the_grammar_is_refused_at_its_position(
    label: Prose, command: Command, column: Column
) -> None:
    """A command RFC 8259 does not allow is refused at the first character it cannot read."""
    assert _answer(command) == {
        "status": "error",
        "code": "dispatch_invalid_json",
        "message": f"invalid JSON: parse failed at line 1, column {column}",
        "line": 1,
        "column": column,
    }, label


@pytest.mark.parametrize(("label", "command", "echoed"), _ECHOED, ids=[row[0] for row in _ECHOED])
def test_an_escaped_character_is_read_and_echoed_readably(
    label: Prose, command: Command, echoed: MessageType
) -> None:
    r"""A character a ``\u`` or short escape names is read, and the reply echoing it is JSON."""
    assert _answer(command) == {
        "status": "error",
        "code": "dispatch_unknown_message_type",
        "message": f"unknown message type '{echoed}'",
    }, label

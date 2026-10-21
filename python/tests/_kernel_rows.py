# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel's reply to one raw command, and the shape of a refusal it writes.

A row of a kernel test is one command and the reply the kernel owes it; the reply's
fields beside ``status``, ``code`` and ``message`` locate the refusal.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, NewType, TypedDict, cast

from aletheia import FFIBackend
from aletheia.client._ffi import KernelResponse, parse_json_object

if TYPE_CHECKING:
    from aletheia.codes import ErrorCode
    from aletheia.types import Response

# A command's bytes, as the kernel receives them.
Command = NewType("Command", bytes)
# The kernel's message, as the reply carries it.
KernelMessage = NewType("KernelMessage", str)
# The part of the input a refusal names.
FieldName = NewType("FieldName", str)
# A Unicode code point.
CodePoint = NewType("CodePoint", int)
# The index of a character in a field, counted from 0.
Index = NewType("Index", int)
# A line of a text, counted from 1.
Line = NewType("Line", int)
# A column of a text, counted from 1.
Column = NewType("Column", int)
# A DBC keyword, as the refusal carries it.
Keyword = NewType("Keyword", str)
# A length a bound refusal observed, or the bound itself.
NameLength = NewType("NameLength", int)


class Located(TypedDict, total=False):
    """The reply's fields beside status, code and message."""

    field: FieldName
    index: Index
    code_point: CodePoint
    line: Line
    column: Column
    statement_line: Line
    statement_column: Column
    keyword: Keyword
    bound_kind: Literal["identifier_length"]
    observed: NameLength
    limit: NameLength


def kernel_reply(command: Command, *, after: Command | None = None) -> Response:
    """Answer ``command`` on a fresh kernel session, ``after`` sent first and accepted."""
    backend = FFIBackend()
    state = backend.init()
    try:
        if after is not None:
            loaded = parse_json_object(KernelResponse(backend.process(state, after)))
            assert loaded["status"] == "success", loaded
        return cast("Response", parse_json_object(KernelResponse(backend.process(state, command))))
    finally:
        backend.close(state)


def refusal(code: ErrorCode, message: KernelMessage, located: Located) -> Response:
    """Build the refusal reply the kernel writes: ``code``, ``message`` and its location."""
    return cast("Response", {"status": "error", "code": code, "message": message, **located})

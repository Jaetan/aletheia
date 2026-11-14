# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The typed error a kernel refusal envelope carries.

One decoder for every entry that answers ``{"status": "error", "code": …,
"message": …}`` plus the code's own fields: a bound refusal lifts to
:class:`InputBoundExceededError`, every other refusal raises the caller's kind
with its code, its text the kernel's message verbatim.  A place of the
envelope holding what the kernel never writes there is refused in the one form
of :mod:`~aletheia.client._helpers.reply_shape`.  Below the rational helpers in
the import graph, so the decimal entry and the response parsers both reach it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, NoReturn

from aletheia.client._helpers.reply_shape import (
    NUMBER,
    REPLY_ROOT,
    STRING,
    Expectation,
    at,
    came,
    came_word,
    field_member,
    held,
    reply_refusal,
    words,
)
from aletheia.client._types import (
    InputBoundExceededError,
    KernelRefusal,
    ProtocolError,
    ValidationError,
)
from aletheia.codes import ErrorCode
from aletheia.common_types import Prose
from aletheia.limits import BoundField, BoundKind, Limit

if TYPE_CHECKING:
    from aletheia.client._helpers.reply_shape import ReplyFields
    from aletheia.common_types import PositiveInt

# The keys of a bound refusal's triple, in the order they are read.
_TRIPLE_KEYS: Final = ("bound_kind", "observed", "limit")

_AN_ERROR_CODE: Final = Expectation("an error code")


def read_error_code(envelope: ReplyFields) -> ErrorCode:
    """Read an error envelope's ``code`` as the :class:`ErrorCode` member it names.

    Raises:
        ProtocolError: If the code is absent, not a string, or no error code,
            refused at ``code`` as ``an error code``.

    """
    return field_member(envelope, REPLY_ROOT, "code", ErrorCode, _AN_ERROR_CODE)


def extract_bound_triple(reply: ReplyFields) -> tuple[BoundKind, PositiveInt, Limit] | None:
    """Return the ``(bound_kind, observed, limit)`` triple, or ``None`` if none of it is there.

    An envelope holding any of the three keys holds all three: ``bound_kind``
    a string, ``observed`` and ``limit`` whole numbers, read without a range
    check since the kernel proves them positive, a boolean refused though
    ``isinstance(True, int)`` holds. Each broken key is refused at its own
    place. Single source for the triple shape, shared by
    :func:`~aletheia.client._response_parsers.build_error_response` (which folds
    it into the ``ErrorResponse``) and :func:`raise_if_input_bound_exceeded`
    (which gates it on the wire code), so no call site re-derives the field
    rules.

    Raises:
        ProtocolError: If one key of the triple is there and another is
            absent or not of its kind.

    """
    if not any(key in reply for key in _TRIPLE_KEYS):
        return None
    bound_kind = held(reply, "bound_kind")
    if not isinstance(bound_kind, str):
        raise reply_refusal(at(REPLY_ROOT, "bound_kind"), STRING, came(reply, "bound_kind"))
    observed = held(reply, "observed")
    if not isinstance(observed, int) or isinstance(observed, bool):
        raise reply_refusal(at(REPLY_ROOT, "observed"), NUMBER, came(reply, "observed"))
    limit = held(reply, "limit")
    if not isinstance(limit, int) or isinstance(limit, bool):
        raise reply_refusal(at(REPLY_ROOT, "limit"), NUMBER, came(reply, "limit"))
    return (BoundKind(bound_kind), observed, limit)


def raise_if_input_bound_exceeded(reply: ReplyFields) -> None:
    """Raise :class:`InputBoundExceededError` for an ``input_bound_exceeded`` error envelope.

    Gates on the wire code, like
    :func:`~aletheia.client._response_parsers.lift_issues_envelope` and the Go /
    C++ / Rust decoders, then reads the triple with :func:`extract_bound_triple`,
    the ``field`` the refusal names, and the kernel's
    ``message``, which is the error's text. Returns normally when the code
    differs. The single lift-and-raise shared by every DBC command, the
    decimal entry and the binary-output entries.

    Raises:
        InputBoundExceededError: If the envelope is a whole bound refusal.
        ProtocolError: If its triple, its ``field`` or its ``message`` is not of
            its kind, the kernel writing the triple and the message on every
            bound refusal.

    """
    if held(reply, "code") != "input_bound_exceeded":
        return
    triple = extract_bound_triple(reply)
    if triple is None:
        raise reply_refusal(at(REPLY_ROOT, "bound_kind"), STRING, came(reply, "bound_kind"))
    field = bound_field(reply)
    message = envelope_message(reply)
    kind, observed, limit = triple
    raise InputBoundExceededError(
        kind,
        observed,
        limit,
        code=ErrorCode.INPUT_BOUND_EXCEEDED,
        refusal=KernelRefusal(message, field),
    )


def bound_field(reply: ReplyFields) -> BoundField | None:
    """Return the part of the input a bound refusal names, or ``None`` when it names none.

    Raises:
        ProtocolError: If ``field`` is there and not a string.

    """
    if "field" not in reply:
        return None
    field = reply["field"]
    if not isinstance(field, str):
        raise reply_refusal(at(REPLY_ROOT, "field"), STRING, came(reply, "field"))
    return BoundField(field)


def envelope_message(reply: ReplyFields) -> Prose:
    """Return an error envelope's text: the kernel's ``message``, verbatim.

    Raises:
        ProtocolError: If the envelope has no string ``message``, which the
            kernel writes on every error envelope.

    """
    message = held(reply, "message")
    if not isinstance(message, str):
        raise reply_refusal(at(REPLY_ROOT, "message"), STRING, came(reply, "message"))
    return Prose(message)


def raise_entry_refusal(
    envelope: ReplyFields,
    *,
    error: type[ProtocolError | ValidationError] = ProtocolError,
) -> NoReturn:
    """Raise the typed error a failed entry's ``err`` envelope carries.

    The envelope is the one every entry answers with (``{"status": "error",
    "code": …, "message": …}`` plus the code's own fields): the kernel's
    refusal, or the shared library's own ``ffi_validation_error``, for an
    argument it cannot read or a buffer too small for the result. A bound
    refusal lifts to :class:`InputBoundExceededError` through
    :func:`raise_if_input_bound_exceeded`; every other refusal raises *error*
    carrying the envelope's ``code``, its text the kernel's ``message``
    verbatim: :class:`ProtocolError` for the binary-output entries,
    :class:`ValidationError` for the decimal entry, whose text is the caller's
    own. An envelope whose ``status`` is not ``"error"``, whose ``code`` is no
    error code, or without a string ``message``, is malformed: it raises a
    :class:`ProtocolError` without a code whatever *error* is, refused at the
    first of ``status``, ``code`` and ``message`` that is broken. The one
    decoder shared by both.
    """
    if held(envelope, "status") != "error":
        raise reply_refusal(at(REPLY_ROOT, "status"), words("error"), came_word(envelope, "status"))
    code = read_error_code(envelope)
    message = held(envelope, "message")
    if not isinstance(message, str):
        raise reply_refusal(at(REPLY_ROOT, "message"), STRING, came(envelope, "message"))
    raise_if_input_bound_exceeded(envelope)
    raise error(message, code=code)

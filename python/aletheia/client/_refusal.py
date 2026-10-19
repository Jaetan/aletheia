# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The typed error a kernel refusal envelope carries.

One decoder for every entry that answers ``{"status": "error", "code": …,
"message": …}`` plus the code's own fields: a bound refusal lifts to
:class:`InputBoundExceededError`, every other refusal raises the caller's kind
with its code, its text the kernel's message verbatim.  Below the rational
helpers in the import graph, so the decimal entry and the response parsers both
reach it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NoReturn

from aletheia.client._types import (
    InputBoundExceededError,
    KernelRefusal,
    ProtocolError,
    ValidationError,
)
from aletheia.common_types import Prose
from aletheia.limits import BoundField, BoundKind, Limit

if TYPE_CHECKING:
    from aletheia.common_types import PositiveInt
    from aletheia.types import Response


def extract_bound_triple(response: Response) -> tuple[BoundKind, PositiveInt, Limit] | None:
    """Return the ``(bound_kind, observed, limit)`` triple, or ``None`` if absent.

    All-or-nothing: a partial triple is treated as missing, matching the C++
    binding's degrade-to-nullopt rule in ``make_json_error``. ``observed`` and
    ``limit`` are positive integers; ``bool`` is excluded because
    ``isinstance(True, int)`` is ``True`` and a boolean is a malformed wire
    value, not a count. Single source for the triple shape, shared by
    :func:`~aletheia.client._response_parsers.build_error_response` (which folds
    it into the ``ErrorResponse``) and :func:`raise_if_input_bound_exceeded`
    (which gates it on the wire code), so
    no call site re-derives the field rules.
    """
    bound_kind = response.get("bound_kind")
    observed = response.get("observed")
    limit = response.get("limit")
    if not (isinstance(bound_kind, str) and isinstance(observed, int) and isinstance(limit, int)):
        return None
    if isinstance(observed, bool) or isinstance(limit, bool) or min(observed, limit) <= 0:
        return None
    return (BoundKind(bound_kind), observed, limit)


def raise_if_input_bound_exceeded(response: Response) -> None:
    """Raise :class:`InputBoundExceededError` for an ``input_bound_exceeded`` error envelope.

    Gates on the wire code, like
    :func:`~aletheia.client._response_parsers.lift_issues_envelope` and the Go /
    C++ / Rust decoders, then reads the triple with :func:`extract_bound_triple`,
    the ``field`` the refusal names, and the kernel's
    ``message``, which is the error's text. Returns normally when the code
    differs, the triple is not whole, ``field`` is present and not a string, or
    ``message`` is not a string, so the caller raises its own fallback rather
    than an error with fabricated fields. The single lift-and-raise shared by
    every DBC command, the decimal entry and the binary-output entries.
    """
    if response.get("code") != "input_bound_exceeded":
        return
    triple = extract_bound_triple(response)
    field = response.get("field")
    message = response.get("message")
    if triple is None or not (field is None or isinstance(field, str)):
        return
    if not isinstance(message, str):
        return
    kind, observed, limit = triple
    raise InputBoundExceededError(
        kind,
        observed,
        limit,
        code="input_bound_exceeded",
        refusal=KernelRefusal(Prose(message), None if field is None else BoundField(field)),
    )


def envelope_message(response: Response, missing: Prose) -> Prose:
    """Return an error envelope's text: the kernel's ``message``, verbatim.

    An envelope without a string ``message`` is a malformed reply, and its text
    is *missing*, the binding's own.
    """
    message = response.get("message")
    return Prose(message) if isinstance(message, str) else missing


def raise_entry_refusal(
    envelope: Response,
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
    own. An envelope whose ``status`` is not ``"error"``, or without a string
    ``code`` and ``message``, is malformed and raises a :class:`ProtocolError`
    without a code whatever *error* is. The one decoder shared by both.
    """
    code = envelope.get("code")
    message = envelope.get("message")
    if (
        envelope.get("status") != "error"
        or not isinstance(code, str)
        or not isinstance(message, str)
    ):
        msg = f"malformed error envelope {envelope!r}"
        raise ProtocolError(msg)
    raise_if_input_bound_exceeded(envelope)
    raise error(message, code=code)

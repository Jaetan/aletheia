# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A failed entry's envelope is the kernel's refusal only when it reads as one.

The decimal entry and the binary-output entries share one decoder.  An
envelope whose ``status`` is not ``"error"``, or without a string ``code`` and
``message``, is malformed and raises a :class:`~aletheia.ProtocolError`
without a code, refused at its broken key; a refusal raises the caller's kind
with the kernel's message verbatim.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, cast

import pytest

from aletheia import ProtocolError, ValidationError
from aletheia.client._refusal import raise_entry_refusal
from aletheia.common_types import Prose

if TYPE_CHECKING:
    from aletheia.types import Response

_MESSAGE = "parse failed at line 1, column 1"


def _envelope(status: Literal["error", "success"] | None) -> Response:
    """Return a ``text_parse_failure`` envelope under *status*, or under none."""
    if status is None:
        return cast("Response", {"code": "text_parse_failure", "message": _MESSAGE})
    return cast("Response", {"status": status, "code": "text_parse_failure", "message": _MESSAGE})


def test_a_refusal_is_the_kernels_message_and_code() -> None:
    """The caller's kind carries the kernel's message verbatim and its code."""
    with pytest.raises(ValidationError) as excinfo:
        raise_entry_refusal(_envelope("error"), error=ValidationError)
    assert str(excinfo.value) == _MESSAGE
    assert excinfo.value.code == "text_parse_failure"


@pytest.mark.parametrize(
    ("status", "said"),
    [
        (None, Prose('reply status: expected "error", got nothing')),
        ("success", Prose('reply status: expected "error", got "success"')),
    ],
)
def test_an_envelope_that_is_not_an_error_is_malformed(
    status: Literal["success"] | None, said: Prose
) -> None:
    """An envelope without the ``error`` status raises a code-less ProtocolError."""
    with pytest.raises(ProtocolError) as excinfo:
        raise_entry_refusal(_envelope(status), error=ValidationError)
    assert excinfo.type is ProtocolError
    assert excinfo.value.code is None
    assert str(excinfo.value) == said


@pytest.mark.parametrize(
    ("envelope", "said"),
    [
        (
            {"status": "error", "message": _MESSAGE},
            Prose("reply code: expected string, got nothing"),
        ),
        (
            {"status": "error", "code": 7, "message": _MESSAGE},
            Prose("reply code: expected string, got number"),
        ),
        (
            {"status": "error", "code": "text_parse_failure"},
            Prose("reply message: expected string, got nothing"),
        ),
        (
            {"status": "error", "code": "text_parse_failure", "message": None},
            Prose("reply message: expected string, got null"),
        ),
    ],
    ids=["no-code", "number-code", "no-message", "null-message"],
)
def test_an_envelope_without_a_string_code_or_message_is_malformed(
    envelope: Response, said: Prose
) -> None:
    """An error envelope lacking a string ``code`` or ``message`` is refused at that key."""
    with pytest.raises(ProtocolError) as excinfo:
        raise_entry_refusal(envelope, error=ValidationError)
    assert excinfo.type is ProtocolError
    assert (str(excinfo.value), excinfo.value.code) == (said, None)

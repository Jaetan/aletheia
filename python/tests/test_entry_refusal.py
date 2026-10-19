# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A failed entry's envelope is the kernel's refusal only when it reads as one.

The decimal entry and the binary-output entries share one decoder.  An
envelope whose ``status`` is not ``"error"`` is malformed and raises a
:class:`~aletheia.ProtocolError` without a code, as the Go decoder refuses it;
a refusal raises the caller's kind with the kernel's message verbatim.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, cast

import pytest

from aletheia import ProtocolError, ValidationError
from aletheia.client._refusal import raise_entry_refusal

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


@pytest.mark.parametrize("status", [None, "success"])
def test_an_envelope_that_is_not_an_error_is_malformed(
    status: Literal["success"] | None,
) -> None:
    """An envelope without the ``error`` status raises a code-less ProtocolError."""
    with pytest.raises(ProtocolError) as excinfo:
        raise_entry_refusal(_envelope(status), error=ValidationError)
    assert excinfo.type is ProtocolError
    assert excinfo.value.code is None
    assert str(excinfo.value).startswith("malformed error envelope ")

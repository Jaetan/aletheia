# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared decimal test cases for the decimal-SSOT suites.

The public ``from_decimal`` test (``test_from_decimal``) and the raw-FFI
``aletheia_parse_decimal`` test (``test_parse_decimal_ffi``) exercise the
identical kernel decimal grammar and bound, so the case set lives here rather
than duplicated in both (pylint R0801).  The C++/Go/Rust suites mirror this set
in their own languages (a cross-language parity set that cannot share this
module).

A refusal is the kernel's error, rendered as every kernel refusal is: ``status``,
``code``, ``message`` and the code's own fields.  A literal the grammar refuses
answers ``text_parse_failure`` (nothing parsed, with the ``line`` and ``column``
of the failure) or ``text_trailing_input`` (a literal parsed and input remains,
with the ``line``/``column`` where the parse stopped and the
``statement_line``/``statement_column`` where the unparsed statement starts).  A
component of the exact rational past the Int64 magnitude answers
``input_bound_exceeded`` with ``field`` ``"decimal"`` and the observed magnitude,
which the kernel saturates at 18446744073709551615, its message then saying
"at least".
"""

from __future__ import annotations

from typing import Literal, NamedTuple, NewType, NotRequired, TypedDict

from aletheia.codes import ErrorCode
from aletheia.common_types import PositiveInt, Prose
from aletheia.limits import (
    BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
    MAX_RATIONAL_COMPONENT_MAGNITUDE,
    BoundField,
    BoundKind,
    Limit,
)

# The text handed to the decimal entry, as the caller spells it.
DecimalText = NewType("DecimalText", str)
_FAILURE = ErrorCode.TEXT_PARSE_FAILURE
_TRAILING = ErrorCode.TEXT_TRAILING_INPUT

# (input, expected numerator, expected denominator) — exact rationals only.
SUCCESS_CASES = [
    ("3.14", 157, 50),
    ("42", 42, 1),
    ("0.1", 1, 10),
    ("-3.14", -157, 50),
    ("0", 0, 1),
    ("-0", 0, 1),  # negative zero collapses to +0
    ("0.000", 0, 1),  # trailing-zero fraction canonicalises
    ("0.10", 1, 10),  # trailing zero trimmed
    ("00.1", 1, 10),  # leading zeros accepted
    ("9223372036854775807", 9223372036854775807, 1),  # the magnitude bound fits
    ("-9223372036854775807", -9223372036854775807, 1),  # and so does its negative
]


class ParseRefusal(TypedDict):
    """The envelope of a ``text_parse_failure`` or ``text_trailing_input`` refusal."""

    status: Literal["error"]
    code: ErrorCode
    message: Prose
    line: PositiveInt
    column: PositiveInt
    statement_line: NotRequired[PositiveInt]
    statement_column: NotRequired[PositiveInt]


class StatementStart(NamedTuple):
    """Where the unparsed statement of a ``text_trailing_input`` refusal starts."""

    line: PositiveInt
    column: PositiveInt


class ParseFailCase(NamedTuple):
    """A literal the grammar refuses, with the position the kernel reports.

    ``statement`` is where the unparsed statement starts for a
    ``text_trailing_input`` refusal, ``None`` for a ``text_parse_failure``.
    """

    text: DecimalText
    code: ErrorCode
    line: PositiveInt
    column: PositiveInt
    statement: StatementStart | None

    def envelope(self) -> ParseRefusal:
        """Return the exact error envelope the kernel answers for ``text``."""
        message = f"parse failed at line {self.line}, column {self.column}"
        out: ParseRefusal = {
            "status": "error",
            "code": self.code,
            "message": Prose(message),
            "line": self.line,
            "column": self.column,
        }
        if self.statement is not None:
            start = f"line {self.statement.line}, column {self.statement.column}"
            out["message"] = Prose(f"{message} (first unparseable statement starts at {start})")
            out["statement_line"] = self.statement.line
            out["statement_column"] = self.statement.column
        return out


# Malformed per the grammar -?digits[.digits+]: no '+', no leading '.', no
# exponent, no fraction syntax, and full consumption (trailing input refused).
PARSE_FAIL_CASES = [
    ParseFailCase(DecimalText("3.14xyz"), _TRAILING, 1, 5, StatementStart(1, 5)),
    ParseFailCase(DecimalText("1e3"), _TRAILING, 1, 2, StatementStart(1, 2)),
    ParseFailCase(DecimalText(".5"), _FAILURE, 1, 1, None),
    ParseFailCase(DecimalText("+1"), _FAILURE, 1, 1, None),
    ParseFailCase(DecimalText("1/2"), _TRAILING, 1, 2, StatementStart(1, 2)),
    # A dot with no fractional digit: the literal ends before the dot.
    ParseFailCase(DecimalText("1."), _TRAILING, 1, 3, StatementStart(1, 2)),
    # A trailing space.
    ParseFailCase(DecimalText("1 "), _TRAILING, 1, 2, StatementStart(1, 2)),
    # A leading space.
    ParseFailCase(DecimalText(" 1"), _FAILURE, 1, 1, None),
    ParseFailCase(DecimalText(""), _FAILURE, 1, 1, None),
    ParseFailCase(DecimalText("-"), _FAILURE, 1, 2, None),
]
PARSE_FAIL_IDS = [repr(case.text) for case in PARSE_FAIL_CASES]


class BoundRefusal(TypedDict):
    """The envelope of the decimal entry's ``input_bound_exceeded`` refusal."""

    status: Literal["error"]
    code: ErrorCode
    message: Prose
    field: BoundField
    bound_kind: BoundKind
    observed: PositiveInt
    limit: Limit


class OverflowCase(NamedTuple):
    """A literal whose exact rational has a component past the magnitude bound.

    ``observed`` is the magnitude the kernel reports; ``saturated`` says it is
    the ceiling 18446744073709551615 standing for a larger magnitude, which the
    message spells "at least".
    """

    text: DecimalText
    observed: PositiveInt
    saturated: bool

    def envelope(self) -> BoundRefusal:
        """Return the exact bound-refusal envelope the kernel answers for ``text``."""
        magnitude = f"{'at least ' if self.saturated else ''}{self.observed}"
        limit = MAX_RATIONAL_COMPONENT_MAGNITUDE
        return {
            "status": "error",
            "code": ErrorCode.INPUT_BOUND_EXCEEDED,
            "message": Prose(
                f"decimal: rational component magnitude {magnitude} exceeds limit {limit}"
            ),
            "field": BoundField("decimal"),
            "bound_kind": BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
            "observed": self.observed,
            "limit": MAX_RATIONAL_COMPONENT_MAGNITUDE,
        }


OVERFLOW_CASES = [
    OverflowCase(DecimalText("99999999999999999999.5"), 18446744073709551615, saturated=True),
    OverflowCase(DecimalText("0.0000000000000000001"), 10000000000000000000, saturated=False),
    # One past the bound on the negative side: the magnitude is what is bounded.
    OverflowCase(DecimalText("-9223372036854775808"), 9223372036854775808, saturated=False),
]
OVERFLOW_IDS = [case.text for case in OVERFLOW_CASES]

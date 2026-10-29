# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel refuses a property it cannot read and says why, field by field.

Every refusal reads ``SetProperties: property N: <reason>`` with the code
``handler_property_parse_failed``: an absent field, a field of the wrong kind,
an unknown operator or predicate, an entry that is not an object, a fraction
whose numerator or denominator is not a whole number or whose denominator is
not positive, a ``between`` whose minimum exceeds its maximum, a negative
``stableWithin`` tolerance, a negative or fractional time bound. A predicate's
own field names the predicate first. A time bound past 2^64-1 microseconds is
``input_bound_exceeded`` against that limit. Equal bounds, a zero tolerance
and a time bound of 2^64-1 load.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType, cast

import pytest

from aletheia import AletheiaClient
from aletheia.common_types import Prose

if TYPE_CHECKING:
    from aletheia.types import ErrorResponse, JSONValue, LTLFormula, SuccessResponse

# The position of a property in the list set_properties sends.
PropertyIndex = NewType("PropertyIndex", int)

_DBC = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 M: 8 ECU\n'
    + ' SG_ S : 0|8@1+ (1,0) [0|255] "" ECU\n'
)
_U64_MAX = 2**64 - 1


def _atom(predicate: JSONValue) -> JSONValue:
    return {"operator": "always", "formula": {"operator": "atomic", "predicate": predicate}}


def _send(*properties: JSONValue) -> SuccessResponse | ErrorResponse:
    """Set ``properties`` on a client holding a one-signal DBC and return the reply."""
    with AletheiaClient() as client:
        assert client.parse_dbc_text(_DBC)["status"] == "success"
        return client.set_properties(cast("list[LTLFormula]", list(properties)))


def _refusal(*properties: JSONValue) -> ErrorResponse:
    reply = _send(*properties)
    assert reply["status"] == "error", reply
    return reply


def _refused_because(
    reason: Prose, *properties: JSONValue, index: PropertyIndex = PropertyIndex(0)
) -> None:
    reply = _refusal(*properties)
    assert reply["code"] == "handler_property_parse_failed", reply
    assert reply["message"] == f"SetProperties: property {index}: {reason}", reply


_FRACTION_CASES: list[tuple[JSONValue, Prose]] = [
    ({"numerator": 1, "denominator": 0}, Prose("equals: value denominator 0 is not positive")),
    ({"numerator": 1, "denominator": -2}, Prose("equals: value denominator -2 is not positive")),
    (
        {"numerator": 1, "denominator": 1.5},
        Prose("equals: value denominator 1.5 is not a whole number"),
    ),
    (
        {"numerator": 1.5, "denominator": 2},
        Prose("equals: value numerator 1.5 is not a whole number"),
    ),
    ({"numerator": 1}, Prose("equals: field 'value' is not a rational")),
    ({"numerator": "1", "denominator": 2}, Prose("equals: field 'value' is not a rational")),
    ("1", Prose("equals: field 'value' is not a rational")),
]


class TestShape:
    """An absent field, a field of the wrong kind and an unknown name each say which."""

    def test_an_absent_operator_field_is_named(self) -> None:
        """An ``always`` without its formula."""
        _refused_because(Prose("field 'formula' is missing"), {"operator": "always"})

    def test_an_operator_field_of_the_wrong_kind_is_named(self) -> None:
        """An ``always`` whose formula is a number."""
        _refused_because(
            Prose("field 'formula' is not an object"), {"operator": "always", "formula": 5}
        )

    def test_an_operator_that_is_not_a_string_is_named(self) -> None:
        """An operator written as a number."""
        _refused_because(Prose("field 'operator' is not a string"), {"operator": 5})

    def test_an_unknown_operator_is_named(self) -> None:
        """An operator the kernel does not know."""
        _refused_because(Prose("operator 'foo' is unknown"), {"operator": "foo"})

    def test_an_unknown_predicate_is_named(self) -> None:
        """A predicate the kernel does not know."""
        _refused_because(
            Prose("predicate 'foo' is unknown"), _atom({"predicate": "foo", "signal": "S"})
        )

    def test_an_entry_that_is_not_an_object(self) -> None:
        """A property that is a bare number."""
        _refused_because(Prose("is not an object"), 5)

    def test_a_predicate_field_opens_with_the_predicate(self) -> None:
        """A between without its maximum."""
        _refused_because(
            Prose("between: field 'max' is missing"),
            _atom({"predicate": "between", "signal": "S", "min": 1}),
        )

    def test_a_signal_of_the_wrong_kind_opens_with_the_predicate(self) -> None:
        """An equals whose signal is a number."""
        _refused_because(
            Prose("equals: field 'signal' is not a string"),
            _atom({"predicate": "equals", "signal": 5, "value": 1}),
        )

    def test_the_index_is_the_refused_property(self) -> None:
        """The second of two properties is the one refused."""
        good = _atom({"predicate": "equals", "signal": "S", "value": 1})
        _refused_because(
            Prose("operator 'foo' is unknown"), good, {"operator": "foo"}, index=PropertyIndex(1)
        )


@pytest.mark.parametrize(("value", "reason"), _FRACTION_CASES)
def test_a_fraction_that_is_not_one(value: JSONValue, reason: Prose) -> None:
    """A fraction object names the part that is not a whole number or not positive."""
    _refused_because(reason, _atom({"predicate": "equals", "signal": "S", "value": value}))


class TestOrdering:
    """An ordered pair out of order and a negative tolerance are refused; the edges load."""

    def test_an_inverted_between_is_refused(self) -> None:
        """A between from 5 to 1."""
        _refused_because(
            Prose("between: min 5 exceeds max 1"),
            _atom({"predicate": "between", "signal": "S", "min": 5, "max": 1}),
        )

    def test_a_negative_tolerance_is_refused(self) -> None:
        """A stableWithin of tolerance -1."""
        _refused_because(
            Prose("stableWithin: tolerance -1 is negative"),
            _atom({"predicate": "stableWithin", "signal": "S", "tolerance": -1}),
        )

    @pytest.mark.parametrize(
        "predicate",
        [
            {"predicate": "between", "signal": "S", "min": 5, "max": 5},
            {"predicate": "stableWithin", "signal": "S", "tolerance": 0},
        ],
    )
    def test_the_edges_load(self, predicate: JSONValue) -> None:
        """Equal bounds and a zero tolerance."""
        assert _send(_atom(predicate))["status"] == "success"


class TestTimeBound:
    """A time bound is a whole, non-negative number of microseconds at most 2^64-1."""

    @staticmethod
    def _bounded(timebound: JSONValue) -> JSONValue:
        atom: JSONValue = {
            "operator": "atomic",
            "predicate": {"predicate": "lessThan", "signal": "S", "value": 10},
        }
        return {"operator": "metricEventually", "timebound": timebound, "formula": atom}

    @pytest.mark.parametrize(
        ("timebound", "reason"),
        [
            (-1000, Prose("timebound -1000 is negative")),
            (1.5, Prose("timebound 1.5 is not a whole number")),
            ("5", Prose("field 'timebound' is not a number")),
        ],
    )
    def test_a_time_bound_the_kernel_cannot_read(self, timebound: JSONValue, reason: Prose) -> None:
        """Negative, fractional and textual time bounds."""
        _refused_because(reason, self._bounded(timebound))

    def test_past_the_limit_is_a_bound_refusal(self) -> None:
        """2^64 microseconds is refused against the time bound's own limit."""
        reply = _refusal(self._bounded(2**64))
        assert reply["code"] == "input_bound_exceeded", reply
        assert reply.get("field") == "time bound", reply
        assert reply.get("observed") == 2**64, reply
        assert reply.get("limit") == _U64_MAX, reply

    def test_the_limit_loads(self) -> None:
        """2^64-1 microseconds loads."""
        assert _send(self._bounded(_U64_MAX))["status"] == "success"

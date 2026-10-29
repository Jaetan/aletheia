# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel refuses a check where it is built, and a loader says which check.

A builder that carries a checked field hands the formula it made to the
kernel's property check, so a reversed range, a negative tolerance or a value
past the rational bound is refused by the call that wrote it, with the reason
set_properties would give.  A loader building the check locates that refusal at
the check, as ``<location>: <reason>``.  A value too wide for the build's
128-bit slot is refused as the kernel refuses a JSON number past the bound.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import pytest
from _dbc_helpers import dbc, message, signal
from _excel_helpers import make_checks_workbook, make_when_then_workbook

from aletheia import (
    AletheiaClient,
    InputBoundExceededError,
    Signal,
    ValidationError,
    checks,
    load_checks,
    load_checks_from_excel,
)
from aletheia.common_types import Prose
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.excel_loader import CellValue

pytestmark = pytest.mark.usefixtures("rts_up")

_LIMIT = 2**128 - 1
_SATURATED = f"rational component magnitude exceeds limit {_LIMIT}"


def _refused_as(refused: pytest.ExceptionInfo[ValidationError], reason: Prose) -> None:
    assert refused.value.code == "handler_property_parse_failed"
    assert str(refused.value) == reason


class TestBuilders:
    """Each builder carrying a checked field is refused where it writes the field."""

    def test_a_negative_tolerance_is_refused(self) -> None:
        """stable_within names the tolerance it refuses."""
        with pytest.raises(ValidationError) as refused:
            Signal("S").stable_within(-1)
        _refused_as(refused, Prose("stableWithin: tolerance -1 is negative"))

    def test_a_value_past_the_bound_is_refused(self) -> None:
        """A comparison's value past the rational bound is the kernel's bound refusal."""
        with pytest.raises(InputBoundExceededError) as refused:
            Signal("S").equals(2**128)
        err = refused.value
        assert (err.kind, err.observed, err.limit) == (
            "rational_component_magnitude",
            _LIMIT,
            _LIMIT,
        )
        assert str(err) == _SATURATED

    def test_a_check_threshold_past_the_bound_is_refused_before_it_renders(self) -> None:
        """No check description can render a threshold the renderer's slot cannot hold."""
        with pytest.raises(InputBoundExceededError):
            checks.signal("S").never_exceeds(Fraction(1, 2**128))

    def test_stays_between_reversed_is_refused(self) -> None:
        """The check API's range builder is refused with the kernel's reason."""
        with pytest.raises(ValidationError) as refused:
            checks.signal("S").stays_between(5, 1)
        _refused_as(refused, Prose("between: min 5 exceeds max 1"))

    def test_settles_between_reversed_is_refused_before_its_window(self) -> None:
        """settles_between refuses the range it is given, before within is called."""
        with pytest.raises(ValidationError) as refused:
            checks.signal("S").settles_between(5, 1)
        _refused_as(refused, Prose("between: min 5 exceeds max 1"))

    def test_a_then_range_reversed_is_refused(self) -> None:
        """A when/then check's range is refused where the then-clause writes it."""
        with pytest.raises(ValidationError) as refused:
            checks.when("A").exceeds(1).then("B").stays_between(5, 1)
        _refused_as(refused, Prose("between: min 5 exceeds max 1"))

    def test_combinators_leave_depth_to_set_properties(self) -> None:
        """A combinator writes no checked field, so it builds what set_properties refuses."""
        prop = Signal("S").equals(1).always()
        for _ in range(70):
            prop = prop.always()
        assert prop.to_dict()["operator"] == "always"


class TestLoaders:
    """A loader locates the kernel's refusal of the check it built, at the check."""

    def test_a_yaml_check_refused_at_build_names_the_check(self) -> None:
        """YAML: ``Check '<name>': <reason>``, the code kept, no key."""
        document = (
            "checks:\n  - name: C\n    signal: S\n    condition: stays_between\n"
            + "    min: 5\n    max: 1\n"
        )
        with pytest.raises(ValidationError) as refused:
            load_checks(document)
        assert (refused.value.code, refused.value.location, refused.value.key) == (
            "handler_property_parse_failed",
            "Check 'C'",
            None,
        )
        assert str(refused.value) == "Check 'C': between: min 5 exceeds max 1"

    def test_a_yaml_number_refusal_keeps_its_key(self) -> None:
        """A number its reader refused stays located at its key."""
        document = (
            "checks:\n  - name: C\n    signal: S\n    condition: settles_between\n"
            + "    min: 1\n    max: 5\n    within_us: -1500\n"
        )
        with pytest.raises(ValidationError) as refused:
            load_checks(document)
        assert str(refused.value) == "Check 'C': invalid 'within_us': timebound -1500 is negative"

    def test_an_excel_check_refused_at_build_names_the_row(self, tmp_path: Path) -> None:
        """Excel: ``Row <n>: <reason>``."""
        path = make_checks_workbook(
            tmp_path, [[None, "S", "stays_between", None, "5", "1", None, None]]
        )
        with pytest.raises(ValidationError) as refused:
            load_checks_from_excel(path)
        assert str(refused.value) == "Row 2: between: min 5 exceeds max 1"

    def test_an_excel_when_then_check_refused_at_build_names_the_row(self, tmp_path: Path) -> None:
        """The When-Then sheet locates a builder's refusal the same way."""
        row: list[CellValue] = [
            "C",
            "A",
            "exceeds",
            "1",
            "B",
            "stays_between",
            None,
            "5",
            "1",
            "100",
            None,
        ]
        path = make_when_then_workbook(tmp_path, [row])
        with pytest.raises(ValidationError) as refused:
            load_checks_from_excel(path)
        assert str(refused.value) == "Row 2: between: min 5 exceeds max 1"


def test_a_padded_excel_time_cell_reads_its_microseconds(tmp_path: Path) -> None:
    """An Excel time window is read as its trimmed text, its spaces not the kernel's to read."""
    path = make_checks_workbook(
        tmp_path, [[None, "S", "settles_between", None, "1", "5", " 1500 ", None]]
    )
    loaded = load_checks_from_excel(path)
    assert loaded[0].to_dict() == checks.signal("S").settles_between(1, 5).within(1500).to_dict()


@pytest.mark.parametrize("value", [Fraction(2**128), Fraction(-(2**128)), Fraction(1, 2**128)])
def test_a_build_value_wider_than_its_slot_is_refused(value: Fraction) -> None:
    """A frame's value past the 128-bit slots is refused as the kernel refuses a JSON number."""
    big = signal("Big", length=64, maximum=2**64 - 1)
    with AletheiaClient() as client:
        assert client.parse_dbc(dbc([message(0x100, "Msg", [big])]))["status"] == "success"
        with pytest.raises(InputBoundExceededError) as refused:
            client.build_frame(0x100, DLCCode(8), {"Big": value})
    err = refused.value
    assert (err.kind, err.observed, err.limit, err.field, err.code) == (
        "rational_component_magnitude",
        _LIMIT,
        _LIMIT,
        "signal value",
        "input_bound_exceeded",
    )
    assert str(err) == f"signal value: {_SATURATED}"

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``aletheia mux-query --value``: the selector read by the kernel's decimal parser.

The text is read as the kernel reads a decimal, as the Go and C++ CLIs read
it. A text the kernel refuses is named with the kernel's message; then a
number that is not whole is refused; then a negative one, named as the
kernel's canonical number. What remains is the selector, a whole number up to
2^128-1. The value is read before it is paired with ``--mux``. Each refusal is
one ``Error:`` line on stderr, exit 2.
"""

from __future__ import annotations

from pathlib import Path
from typing import NewType

import pytest

from aletheia.cli import main
from aletheia.common_types import Prose

# The text a test gives --value.
ValueText = NewType("ValueText", str)

_MUX_DBC = Path(__file__).parent / "fixtures" / "dbc_corpus" / "multiplexing.dbc"

# Message 100 is BasicMux, multiplexed by Mode.
_SELECT = ["mux-query", "--dbc", str(_MUX_DBC), "100", "--mux", "Mode", "--value"]

# The largest whole number the kernel reads, the last multiplex value.
_MAX_MUX_VALUE = 2**128 - 1


def test_a_zero_fraction_selects_the_whole_number(capsys: pytest.CaptureFixture[Prose]) -> None:
    """--value 1.0 is the kernel's exact 1, so it selects what 1 selects."""
    assert main([*_SELECT, "1.0"]) == 0
    out = capsys.readouterr().out
    assert "Multiplexor Mode = 1: 3 signals present" in out
    assert "PayloadB" in out
    assert "PayloadA" not in out


def test_2_128_minus_1_is_a_selector(capsys: pytest.CaptureFixture[Prose]) -> None:
    """--value 2^128-1 is a multiplex value no signal has: the always-present ones remain."""
    assert main([*_SELECT, str(_MAX_MUX_VALUE)]) == 0
    out = capsys.readouterr().out
    assert f"Multiplexor Mode = {_MAX_MUX_VALUE}: 2 signals present" in out
    assert "CommonCounter" in out


@pytest.mark.parametrize(
    ("value", "refusal"),
    [
        pytest.param(ValueText("1.5"), Prose("invalid --value: 1.5"), id="fraction"),
        pytest.param(ValueText("-1.5"), Prose("invalid --value: -1.5"), id="negative-fraction"),
        pytest.param(ValueText("-1"), Prose("--value must not be negative, got -1"), id="negative"),
        pytest.param(
            ValueText("-1.0"),
            Prose("--value must not be negative, got -1"),
            id="negative-zero-fraction",
        ),
        pytest.param(
            ValueText("abc"),
            Prose("invalid --value: abc: parse failed at line 1, column 1"),
            id="not-a-number",
        ),
        pytest.param(
            ValueText(str(_MAX_MUX_VALUE + 1)),
            Prose(
                f"invalid --value: {_MAX_MUX_VALUE + 1}: decimal: rational component "
                + f"magnitude exceeds limit {_MAX_MUX_VALUE}"
            ),
            id="past-2-128-minus-1",
        ),
    ],
)
def test_a_value_no_multiplexor_has_is_refused(
    capsys: pytest.CaptureFixture[Prose], value: ValueText, refusal: Prose
) -> None:
    """A refused value is one ``Error:`` line on stderr, exit 2."""
    assert main([*_SELECT, value]) == 2
    assert capsys.readouterr().err == f"Error: {refusal}\n"


def test_the_value_is_read_before_it_is_paired_with_mux(
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A refused --value is named even without --mux."""
    assert main(["mux-query", "--dbc", str(_MUX_DBC), "100", "--value", "abc"]) == 2
    assert capsys.readouterr().err == (
        "Error: invalid --value: abc: parse failed at line 1, column 1\n"
    )

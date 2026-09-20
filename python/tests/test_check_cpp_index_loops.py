# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The counting-loop scan reads every spelling of a step, and records what it read.

A row of ``docs/CPP_INDEX_LOOPS.yaml`` is keyed by the loop header's own text,
so the header a ``while`` or a ``do`` records has to be the source's, literals
included: the scan blanks comments and literals to find the loops, and a row
that carried the blanked text would name a header the file does not hold. And
a step is what makes a loop a counting loop, so the spelling a gate reading
only the operators would miss, a variable assigned its own sum, is a step too.
"""

from __future__ import annotations

from tools.check_cpp_index_loops import loops_in, steps_variable


def test_a_while_row_carries_the_literals_its_condition_compares() -> None:
    """The recorded header is the source's, not the blanked scan's."""
    source = "while (i < n && text[i] != '*') {\n    ++i;\n}\n"
    assert loops_in(source) == ["while (i < n && text[i] != '*')"]


def test_a_do_row_carries_the_literals_its_condition_compares() -> None:
    """The ``do`` tail is recorded from the source as well."""
    source = "do {\n    ++i;\n} while (i < n && text[i] != '/');\n"
    assert loops_in(source) == ["do ... while (i < n && text[i] != '/')"]


def test_a_variable_assigned_its_own_sum_is_stepped() -> None:
    """``i = i + 1`` counts as a step wherever it is written."""
    assert steps_variable("i = i + 1", "i")
    assert steps_variable("j=j-2;", "j")
    assert loops_in("for (std::size_t i = 0; i < v.size(); i = i + 1) g(v[i]);\n") == [
        "for (std::size_t i = 0; i < v.size(); i = i + 1)"
    ]
    assert loops_in("while (j < v.size()) {\n    j = j + 1;\n}\n") == ["while (j < v.size())"]


def test_a_variable_assigned_something_else_is_not_stepped() -> None:
    """An assignment from another value is a reset, not a step."""
    assert not steps_variable("i = j + 1", "i")
    assert not steps_variable("i = f(i)", "i")
    assert loops_in("while (pos < n) {\n    pos = next(pos);\n}\n") == []

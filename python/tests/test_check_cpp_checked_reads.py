# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The checked-read rule counts the library's reads alone, and says what to write instead.

What the rule's matchers bind under clang-query is held over a fixture tree by
the tests of ``tools/check_cpp_ast.py``, which runs every rule in one parse;
these hold what the rule makes of clang-query's output: a read outside the
library's sources, or bound by another rule's matcher, is not counted, and
every read counted is printed with its checked form and fails the gate.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import check_cpp_checked_reads as rule
from tools._clang_query import QueryOutput
from tools._common import RelPath
from tools.check_cpp_checked_reads import (
    BindName,
    LineNumber,
    Read,
    UnitCount,
    judge,
    reads_in,
    report,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


def _printed(monkeypatch: pytest.MonkeyPatch) -> list[Prose]:
    """Collect what the rule prints, line by line."""
    lines: list[Prose] = []
    monkeypatch.setattr(rule, "emit", lines.append)
    return lines


def test_a_library_path_inside_a_dependency_is_not_the_library(tmp_path: Path) -> None:
    """The library is read from the tree's root, not from wherever cpp/src occurs in a path."""
    vendored = tmp_path / "cpp/build-tidy/_deps/lib-src/cpp/include/lib.hpp"
    output = QueryOutput(f'{vendored}:3:5: note: "unchecked subscript" binds here\n')
    assert not reads_in(tmp_path, output)


def test_another_rules_bind_is_not_a_read(tmp_path: Path) -> None:
    """The one parse prints every rule's binds; only this rule's names are reads."""
    source = tmp_path / "cpp/src/a.cpp"
    output = QueryOutput(
        f'{source}:4:5: note: "restated declaration" binds here\n'
        + f'{source}:9:12: note: "unchecked end" binds here\n'
    )
    assert reads_in(tmp_path, output) == [
        Read(RelPath("cpp/src/a.cpp"), LineNumber(9), BindName("unchecked end"))
    ]


def test_each_read_is_printed_with_its_checked_form(monkeypatch: pytest.MonkeyPatch) -> None:
    """A finding names the line, the rule and what to write instead, and fails the gate."""
    printed = _printed(monkeypatch)
    read = Read(RelPath("cpp/src/a.cpp"), LineNumber(7), BindName("unchecked error"))
    assert report({read}, UnitCount(1)) == ExitStatus(1)
    assert printed == [
        "cpp/src/a.cpp:7: unchecked error: read it through detail::error_of",
        "1 unchecked reads of a ruled-out state (AGENTS/cpp.md cat 24)",
    ]


def test_a_clean_tree_passes_and_counts_the_units(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """No read is a pass, and the line counts one unit per output."""
    printed = _printed(monkeypatch)
    assert judge(tmp_path, [QueryOutput(""), QueryOutput("")]) == ExitStatus(0)
    assert printed == ["every read of a ruled-out state is checked over 2 units"]

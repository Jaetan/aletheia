# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The restated-type rule's judge refuses both directions, and a record it cannot read.

A declaration the record does not name fails, and so does a row naming more
declarations than the tree holds, since such a row is standing permission to
write one back; a record that cannot be read is a gate that cannot run, never
one that passes. What the rule's matcher binds is held over a fixture tree by
the tests of ``tools/check_cpp_ast.py``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import check_cpp_restated_types as rule
from tools._clang_query import QueryOutput
from tools._common import RelPath
from tools._ratchet import CanonicalText, as_row
from tools.check_cpp_restated_types import ALLOWLIST, BIND, judge

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

_FILE = RelPath("cpp/src/a.cpp")
_DECLARATION = CanonicalText("const std::string copy = s.substr(0)")
_ROW = as_row(_FILE, _DECLARATION, 1)


def _printed(monkeypatch: pytest.MonkeyPatch) -> list[Prose]:
    """Collect what the rule prints, line by line."""
    lines: list[Prose] = []
    monkeypatch.setattr(rule, "emit", lines.append)
    return lines


def _output(repo: Path) -> QueryOutput:
    """clang-query's diagnostic for the declaration: its location, its line, the caret run."""
    return QueryOutput(
        f'{repo / _FILE}:3:5: note: "{BIND}" binds here\n'
        + f"    3 |     {_DECLARATION};\n"
        + f"      |     ^{'~' * (len(_DECLARATION) - 1)}\n"
    )


def _record(repo: Path, *, recorded: bool) -> None:
    """Write the ratchet's record, naming the declaration or nothing."""
    (repo / ALLOWLIST).parent.mkdir(parents=True)
    rows = f"\n{_ROW}\n" if recorded else " []\n"
    _ = (repo / ALLOWLIST).write_text(f"declarations:{rows}", encoding="utf-8")


def test_a_recorded_declaration_passes(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The tree's declarations are the record's, so the gate passes and counts them."""
    printed = _printed(monkeypatch)
    _record(tmp_path, recorded=True)
    assert judge(tmp_path, [_output(tmp_path)]) == ExitStatus(0)
    assert printed == ["C++ declarations restating their type: 1, every one recorded"]


def test_an_unrecorded_declaration_fails(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The failure prints the row that would allow the declaration."""
    printed = _printed(monkeypatch)
    _record(tmp_path, recorded=False)
    assert judge(tmp_path, [_output(tmp_path)]) == ExitStatus(1)
    assert _ROW in printed
    assert printed[-1] == "1 unrecorded, 0 stale"


def test_a_stale_row_fails(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A row the tree no longer holds is refused, naming the count to lower it to."""
    printed = _printed(monkeypatch)
    _record(tmp_path, recorded=True)
    assert judge(tmp_path, []) == ExitStatus(1)
    assert "  count to 0, in the change that deduced it." in printed
    assert printed[-1] == "0 unrecorded, 1 stale"


def test_a_missing_record_fails(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """With nothing to ratchet against the gate cannot run, and says so."""
    printed = _printed(monkeypatch)
    assert judge(tmp_path, [_output(tmp_path)]) == ExitStatus(1)
    assert printed == [f"{ALLOWLIST} is missing; the gate has no record to ratchet against"]

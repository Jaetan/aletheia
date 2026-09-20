# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A unit clang-query could not parse is a failed run, never a clean unit.

clang-query exits zero after a fatal diagnostic, a header it could not find
included, and matches nothing in the unit it could not parse. A gate reading
only the exit code would take that unit's silence for the absence of the
declarations it refuses, which is the one outcome a gate must not have.
"""

from __future__ import annotations

import subprocess
from typing import TYPE_CHECKING

from tools import check_cpp_restated_types as gate
from tools.check_cpp_restated_types import UnitPath

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


def _stub_clang_query(monkeypatch: pytest.MonkeyPatch, stdout: str, stderr: str) -> None:
    """Make the module's clang-query call answer with a zero exit and this output."""

    def run(*_args: object, **_kwargs: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(args=[], returncode=0, stdout=stdout, stderr=stderr)

    monkeypatch.setattr(gate.subprocess, "run", run)


def test_a_fatal_diagnostic_fails_the_unit(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The failure names the unit and the diagnostic."""
    _stub_clang_query(
        monkeypatch,
        stdout="",
        stderr="src/enrich.cpp:3:10: fatal error: 'aletheia/enrich.hpp' file not found\n",
    )
    result = gate.run_matcher(tmp_path, tmp_path / "q", UnitPath("src/enrich.cpp"))
    assert isinstance(result, str)
    assert "src/enrich.cpp" in result
    assert "file not found" in result


def test_a_clean_unit_with_no_hits_is_an_empty_list(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A warning on stderr is not a failure, and no diagnostic is no hit."""
    _stub_clang_query(monkeypatch, stdout="", stderr="warning: something advisory\n")
    assert gate.run_matcher(tmp_path, tmp_path / "q", UnitPath("src/enrich.cpp")) == []

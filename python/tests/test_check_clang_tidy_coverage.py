# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_clang_tidy_coverage`` — the C++ lint-coverage guard.

Two layers, mirroring the gate's own discipline:

* ``uncovered_sources`` — the pure set-difference.  The discriminating case is
  an *extra* DB entry (a test / third-party TU) that must NOT be flagged: the
  guard checks sources-are-covered, not the converse.
* ``main`` — a hermetic end-to-end run in a throwaway git repo, both polarities:
  a source present in the compile DB passes; the same source absent from the DB
  fails. This is the [[feedback_orchestrator_end_to_end_validation]] check —
  proving the guard actually *bites* (and that path normalization works), so it
  can't silently always-pass.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

from tools.check_clang_tidy_coverage import main, uncovered_sources

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


class TestUncoveredSources:
    """Pure set-difference: src files absent from the compile DB."""

    def test_all_covered_is_empty(self) -> None:
        """Every source present in the DB → no uncovered files."""
        assert (
            uncovered_sources(
                {"cpp/src/a.cpp", "cpp/src/b.cpp"}, {"cpp/src/a.cpp", "cpp/src/b.cpp"}
            )
            == []
        )

    def test_missing_source_is_reported(self) -> None:
        """A source absent from the DB is returned (the guard's whole point)."""
        assert uncovered_sources({"cpp/src/a.cpp", "cpp/src/b.cpp"}, {"cpp/src/a.cpp"}) == [
            "cpp/src/b.cpp"
        ]

    def test_extra_db_entries_are_ignored(self) -> None:
        """DB entries with no on-disk source counterpart (tests, _deps) are not flagged."""
        # The DB also lists tests / third-party TUs; those must not be flagged.
        assert (
            uncovered_sources(
                {"cpp/src/a.cpp"},
                {"cpp/src/a.cpp", "cpp/tests/t.cpp", "cpp/build/_deps/x.cpp"},
            )
            == []
        )


def _make_repo(tmp_path: Path, db_files: list[str]) -> Path:
    """Create a repo tree with two cpp/src sources + a compile DB listing ``db_files``."""
    repo = tmp_path / "repo"
    (repo / "cpp" / "src" / "detail").mkdir(parents=True)
    (repo / "cpp" / "build").mkdir(parents=True)
    (repo / "cpp" / "src" / "a.cpp").write_text("int a;\n", encoding="utf-8")
    (repo / "cpp" / "src" / "detail" / "b.cpp").write_text("int b;\n", encoding="utf-8")
    db = [
        {"directory": str(repo / "cpp" / "build"), "file": str(repo / f), "command": "cc"}
        for f in db_files
    ]
    (repo / "cpp" / "build" / "compile_commands.json").write_text(json.dumps(db), encoding="utf-8")
    return repo


def test_main_passes_when_all_sources_in_db(tmp_path: Path) -> None:
    """End-to-end: both sources in the DB → exit 0."""
    repo = _make_repo(tmp_path, ["cpp/src/a.cpp", "cpp/src/detail/b.cpp"])
    assert main(repo=repo) == 0


def test_main_fails_when_a_source_is_missing_from_db(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """End-to-end: b.cpp on disk but absent from the DB → exit 1, names the file."""
    repo = _make_repo(tmp_path, ["cpp/src/a.cpp"])
    assert main(repo=repo) == 1
    assert "cpp/src/detail/b.cpp" in capsys.readouterr().out


def test_main_errors_when_db_absent(tmp_path: Path) -> None:
    """No compile_commands.json → exit 2 (build not configured)."""
    repo = tmp_path / "repo"
    (repo / "cpp" / "src").mkdir(parents=True)
    assert main(repo=repo) == 2

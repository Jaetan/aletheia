# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A unit clang-query could not query is a failed run, never a clean unit.

clang-query exits zero after a fatal diagnostic, a header it could not find
included, and matches nothing in the unit it could not parse. A gate reading
only the exit code would take that unit's silence for the absence of what it
refuses, which is the one outcome a gate must not have. The units are the
binding's own, read from the lint tree's compile database without the
dependencies its configure fetched there.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

from tools import _clang_query as clang_query
from tools._clang_query import (
    COMPILE_DB,
    QueryFailedError,
    QueryOutput,
    UnitPath,
    query_unit,
    translation_units,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

_UNIT = UnitPath("src/enrich.cpp")


def _stand_in(
    monkeypatch: pytest.MonkeyPatch,
    repo: Path,
    finished: tuple[ExitStatus, QueryOutput, Prose],
) -> None:
    """Make clang-query a stand-in that prints this output and errors and exits with this status."""
    status, stdout, stderr = finished
    (repo / "cpp").mkdir()
    _ = (repo / "stdout").write_text(stdout, encoding="utf-8")
    _ = (repo / "stderr").write_text(stderr, encoding="utf-8")
    tool = repo / "clang-query-23"
    _ = tool.write_text(
        f'#!/bin/sh\ncat "{repo}/stdout"\ncat "{repo}/stderr" >&2\nexit {status}\n',
        encoding="utf-8",
    )
    tool.chmod(0o755)
    monkeypatch.setattr(clang_query, "CLANG_QUERY", str(tool))


def test_a_fatal_diagnostic_fails_the_unit(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The failure names the unit and the diagnostic, though clang-query exited zero."""
    _stand_in(
        monkeypatch,
        tmp_path,
        (
            ExitStatus(0),
            QueryOutput(""),
            Prose("src/enrich.cpp:3:10: fatal error: 'aletheia/enrich.hpp' file not found\n"),
        ),
    )
    with pytest.raises(
        QueryFailedError, match=r"could not parse src/enrich\.cpp: .*file not found"
    ):
        _ = query_unit(tmp_path, tmp_path / "q", _UNIT)


def test_a_failed_run_names_the_unit(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A non-zero exit fails the unit with the first line clang-query printed."""
    _stand_in(
        monkeypatch,
        tmp_path,
        (ExitStatus(1), QueryOutput(""), Prose("unknown command: matchh\nmore\n")),
    )
    with pytest.raises(
        QueryFailedError, match=r"failed on src/enrich\.cpp: unknown command: matchh$"
    ):
        _ = query_unit(tmp_path, tmp_path / "q", _UNIT)


def test_a_missing_clang_query_is_a_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A tool that cannot be started is named with the package it comes from."""
    monkeypatch.setattr(clang_query, "CLANG_QUERY", str(tmp_path / "clang-query-23"))
    with pytest.raises(QueryFailedError, match=r"could not be run .*ships with clang-tidy-23"):
        _ = query_unit(tmp_path, tmp_path / "q", _UNIT)


def test_a_clean_unit_returns_what_clang_query_printed(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A warning on stderr is not a failure, and the output is handed back whole."""
    printed = QueryOutput('/r/cpp/src/a.cpp:1:1: note: "x" binds here\n')
    _stand_in(monkeypatch, tmp_path, (ExitStatus(0), printed, Prose("warning: advisory\n")))
    assert query_unit(tmp_path, tmp_path / "q", _UNIT) == printed


def test_a_missing_database_names_the_configure(tmp_path: Path) -> None:
    """Without the lint tree there is nothing to read, and the gate says how to make it."""
    refusal = translation_units(tmp_path)
    assert isinstance(refusal, str)
    assert f"{COMPILE_DB} is missing" in refusal
    assert "cmake -B build-tidy" in refusal


def test_the_units_are_the_bindings_own(tmp_path: Path) -> None:
    """A dependency fetched into the lint tree is not a unit; each unit is named once, in order."""
    cpp = tmp_path / "cpp"
    database = tmp_path / COMPILE_DB
    database.parent.mkdir(parents=True)
    files = [
        f"{cpp}/src/z.cpp",
        f"{cpp}/build-tidy/_deps/yaml-cpp-src/src/node.cpp",
        f"{cpp}/src/a.cpp",
        f"{cpp}/src/z.cpp",
    ]
    _ = database.write_text(json.dumps([{"file": file} for file in files]), encoding="utf-8")
    assert translation_units(tmp_path) == [f"{cpp}/src/a.cpp", f"{cpp}/src/z.cpp"]

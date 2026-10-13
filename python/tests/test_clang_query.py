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

import errno
import json
import subprocess
from dataclasses import dataclass, field
from functools import partial
from pathlib import Path
from types import SimpleNamespace
from typing import NamedTuple

import pytest
from _executors import DrivenExecutor, Order
from _processes import CommandWord

from tools import _clang_query as clang_query
from tools._clang_query import (
    COMPILE_DB,
    PrintedPath,
    Queried,
    Query,
    QueryFailedError,
    QueryOutput,
    UnitPath,
    printed_file,
    query_tree,
    query_unit,
    query_units,
    translation_units,
)

from aletheia.common_types import ExitStatus, Prose

_UNIT = UnitPath("src/enrich.cpp")


class _Call(NamedTuple):
    """One command clang-query was handed, and the directory it was run in."""

    argv: list[CommandWord]
    cwd: Path


def _handed(repo: Path) -> _Call:
    """Return the command that queries ``_UNIT`` with the script ``repo / "q"``, run in cpp/."""
    words = ["clang-query-23", "-p", "build-tidy", "-f", f"{repo / 'q'}", _UNIT]
    return _Call([CommandWord(word) for word in words], repo / "cpp")


@dataclass
class _ClangQuery:
    """clang-query as ``query_unit`` sees it: how it finishes, and every command it is handed."""

    finished: tuple[ExitStatus, QueryOutput, Prose] | OSError
    calls: list[_Call] = field(default_factory=list[_Call])

    def run(
        self,
        argv: list[CommandWord],
        *,
        cwd: Path,
        capture_output: bool,
        text: bool,
        check: bool,
    ) -> subprocess.CompletedProcess[QueryOutput | Prose]:
        """Record the command, then raise the start failure or return the output and status."""
        assert capture_output
        assert text
        assert not check
        self.calls.append(_Call(argv, cwd))
        if isinstance(self.finished, OSError):
            raise self.finished
        status, stdout, stderr = self.finished
        return subprocess.CompletedProcess(argv, status, stdout, stderr)


def _stand_in(
    monkeypatch: pytest.MonkeyPatch, finished: tuple[ExitStatus, QueryOutput, Prose] | OSError
) -> _ClangQuery:
    """Make clang-query finish as ``finished`` says, its output and errors or its start failure."""
    clang = _ClangQuery(finished)
    monkeypatch.setattr(clang_query, "subprocess", SimpleNamespace(run=clang.run))
    return clang


def test_a_fatal_diagnostic_fails_the_unit(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """The failure names the unit and the diagnostic, though clang-query exited zero."""
    clang = _stand_in(
        monkeypatch,
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
    assert clang.calls == [_handed(tmp_path)]


def test_a_failed_run_names_the_unit(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """A non-zero exit fails the unit with the first line clang-query printed."""
    clang = _stand_in(
        monkeypatch, (ExitStatus(1), QueryOutput(""), Prose("unknown command: matchh\nmore\n"))
    )
    with pytest.raises(
        QueryFailedError, match=r"failed on src/enrich\.cpp: unknown command: matchh$"
    ):
        _ = query_unit(tmp_path, tmp_path / "q", _UNIT)
    assert clang.calls == [_handed(tmp_path)]


def test_a_missing_clang_query_is_a_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A tool that cannot be started is named with the package it comes from."""
    clang = _stand_in(
        monkeypatch,
        FileNotFoundError(errno.ENOENT, "No such file or directory", clang_query.CLANG_QUERY),
    )
    with pytest.raises(QueryFailedError, match=r"could not be run .*ships with clang-tidy-23"):
        _ = query_unit(tmp_path, tmp_path / "q", _UNIT)
    assert clang.calls == [_handed(tmp_path)]


def test_a_clean_unit_returns_what_clang_query_printed(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A warning on stderr is not a failure, and the output is handed back whole."""
    printed = QueryOutput('/r/cpp/src/a.cpp:1:1: note: "x" binds here\n')
    clang = _stand_in(monkeypatch, (ExitStatus(0), printed, Prose("warning: advisory\n")))
    assert query_unit(tmp_path, tmp_path / "q", _UNIT) == printed
    assert clang.calls == [_handed(tmp_path)]


def test_a_printed_file_lands_where_its_parent_segments_lead() -> None:
    """A header a relative include reaches is the header's own path, ``..`` folded away."""
    printed = PrintedPath("/r/cpp/tests/../src/./detail/x.hpp")
    assert printed_file(printed) == Path("/r/cpp/src/detail/x.hpp")


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


def test_a_queried_tree_carries_its_root_units_and_outputs(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The tree queried whole is the repository root, every unit, and what each printed."""
    cpp = tmp_path / "cpp"
    database = tmp_path / COMPILE_DB
    database.parent.mkdir(parents=True)
    units = [UnitPath(f"{cpp}/src/a.cpp"), UnitPath(f"{cpp}/src/b.cpp")]
    _ = database.write_text(json.dumps([{"file": file} for file in units]), encoding="utf-8")

    def query(_repo: Path, _script: Path, unit: UnitPath) -> QueryOutput:
        return QueryOutput(f"in {unit}")

    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    monkeypatch.setattr(clang_query, "query_unit", query)
    assert query_tree(Query("m"), executor=DrivenExecutor) == Queried(
        tmp_path, units, [QueryOutput(f"in {unit}") for unit in units]
    )


def test_a_tree_that_cannot_be_queried_is_none_and_the_reason_printed(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without a database, or with a unit that fails its query, the tree is None and says why."""
    monkeypatch.setattr(clang_query, "git_toplevel", lambda: tmp_path)
    assert query_tree(Query("m"), executor=DrivenExecutor) is None
    assert f"{COMPILE_DB} is missing" in capsys.readouterr().out
    database = tmp_path / COMPILE_DB
    database.parent.mkdir(parents=True)
    _ = database.write_text(json.dumps([{"file": f"{tmp_path}/cpp/src/a.cpp"}]), encoding="utf-8")

    def fail(_repo: Path, _script: Path, unit: UnitPath) -> QueryOutput:
        msg = f"{unit}: clang-query could not parse it"
        raise QueryFailedError(msg)

    monkeypatch.setattr(clang_query, "query_unit", fail)
    assert query_tree(Query("m"), executor=DrivenExecutor) is None
    assert capsys.readouterr().out == f"{tmp_path}/cpp/src/a.cpp: clang-query could not parse it\n"


def test_every_unit_runs_on_the_executor_handed_in_and_keeps_its_place(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The units run on the caller's executor, last first here, and come back in unit order."""
    queried: list[UnitPath] = []

    def query(_repo: Path, _script: Path, unit: UnitPath) -> QueryOutput:
        queried.append(unit)
        return QueryOutput(f"matches in {unit}")

    monkeypatch.setattr(clang_query, "query_unit", query)
    units = [UnitPath("a.cpp"), UnitPath("b.cpp"), UnitPath("c.cpp")]
    outputs = query_units(
        tmp_path, units, Query("m"), executor=partial(DrivenExecutor, order=Order.LAST_SUBMITTED)
    )
    assert queried == [UnitPath("c.cpp"), UnitPath("b.cpp"), UnitPath("a.cpp")]
    assert outputs == [QueryOutput(f"matches in {unit}") for unit in units]


def test_a_unit_that_fails_its_query_fails_the_run_by_its_reason(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A unit whose query fails turns the run into that failure's reason."""

    def query(_repo: Path, _script: Path, unit: UnitPath) -> QueryOutput:
        if unit == UnitPath("b.cpp"):
            msg = "clang-query refused b.cpp"
            raise QueryFailedError(msg)
        return QueryOutput("")

    monkeypatch.setattr(clang_query, "query_unit", query)
    units = [UnitPath("a.cpp"), UnitPath("b.cpp")]
    assert query_units(tmp_path, units, Query("m"), executor=DrivenExecutor) == Prose(
        "clang-query refused b.cpp"
    )

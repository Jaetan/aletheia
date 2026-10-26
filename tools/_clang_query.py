# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run a clang-query script over every translation unit of the C++ binding.

``tools/check_cpp_ast.py`` runs the rules matched on the C++ AST through it,
``tools/check_cpp_restated_types.py`` (AGENTS/cpp.md cat 34) and
``tools/check_cpp_checked_reads.py`` (cat 24), and ``tools/check_cpp_const_locals.py``
(cat 5) lists its candidates through it.  ``clang-query`` ships with
``clang-tidy`` (the ``clang-tidy-23`` package Depends on ``clang-tools-23``),
so wherever the lint gate runs this can, and it reads the lint tree's compile
database, so it runs in clang-tidy's lane after the configure that writes it.

Each unit is queried by a process of its own, the units in parallel.  A unit
clang-query could not parse fails the run: clang-query exits zero after a fatal
diagnostic, a header it could not find included, and matches nothing in that
unit, which read as clean would drop the unit from the gate.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import subprocess
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, NamedTuple, NewType, NotRequired, TypedDict, cast

from tools._common import CPP_LINT_TREE, WorkerCount, emit, git_toplevel

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools._common import ExecutorFactory

# A translation unit as the compile database names it: the absolute path CMake
# writes, the spelling in which clang-query reports each match's file and the
# rules' path checks read it.
UnitPath = NewType("UnitPath", str)

# A clang-query script: `set` commands, and one `match` per matcher.
Query = NewType("Query", str)

# What clang-query printed for one unit it parsed.
QueryOutput = NewType("QueryOutput", str)


# One argument of a compile command, and a whole one as one string; the
# directory a command runs from.
CompileArg = NewType("CompileArg", str)
CommandLine = NewType("CommandLine", str)
DirectoryName = NewType("DirectoryName", str)


class DatabaseEntry(TypedDict):
    """One compile database entry: its file, directory, and command as words or one line."""

    file: UnitPath
    directory: DirectoryName
    arguments: NotRequired[list[CompileArg]]
    command: NotRequired[CommandLine]


def unit_arguments(entry: DatabaseEntry) -> list[CompileArg]:
    """Return an entry's command as its arguments, its ``command`` split as a shell would."""
    return entry.get("arguments") or [
        CompileArg(arg) for arg in shlex.split(entry.get("command", CommandLine("")))
    ]


# The compile database the lint gate reads, and the directory clang-query
# resolves it from.
CPP_ROOT = Path("cpp")
BUILD_DIR = CPP_LINT_TREE
COMPILE_DB = CPP_ROOT / BUILD_DIR / "compile_commands.json"

# The lint gate names the same version, and clang-query comes with it.
CLANG_QUERY = "clang-query-23"

# Third-party sources the configure fetches into the lint tree; the standards
# cover cpp/ itself.
VENDORED = f"/{BUILD_DIR}/_deps/"

# A diagnostic clang-query prints for a unit it could not parse; its exit code
# does not carry it.
_ERROR = re.compile(r"^.*\berror: .*$", re.MULTILINE)


class QueryFailedError(Exception):
    """clang-query could not be run over a unit, or could not parse it."""


# A file as a clang-query diagnostic spells it.
PrintedPath = NewType("PrintedPath", str)


def printed_file(printed: PrintedPath) -> Path:
    """Return the file a clang-query diagnostic names, its ``..`` segments folded away.

    A header a relative include reaches prints as the includer's directory
    joined to the include's text, ``cpp/tests/../src/x.hpp``; folded, it is the
    header's one path whichever unit reaches it, and a check of the directory
    it lies in reads the header's directory rather than the includer's.
    """
    return Path(os.path.normpath(printed))


def translation_units(repo: Path) -> list[UnitPath] | Prose:
    """Return the binding's own translation units, or why they cannot be read."""
    database = repo / COMPILE_DB
    if not database.is_file():
        return Prose(
            f"{COMPILE_DB} is missing, so the gate cannot run.  Configure the"
            + f" binding first: cd {CPP_ROOT} && cmake -B {BUILD_DIR}"
            + " -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23"
        )
    entries = cast("list[DatabaseEntry]", json.loads(database.read_text(encoding="utf-8")))
    return sorted({entry["file"] for entry in entries if VENDORED not in entry["file"]})


def query_unit(repo: Path, script: Path, unit: UnitPath) -> QueryOutput:
    """Run the script over one unit and return what it printed.

    Raises ``QueryFailedError`` naming the unit when clang-query could not be
    run, failed, or could not parse the unit.
    """
    try:
        finished = subprocess.run(
            [CLANG_QUERY, "-p", BUILD_DIR, "-f", str(script), unit],
            cwd=repo / CPP_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as failure:
        message = f"{CLANG_QUERY} could not be run ({failure}); it ships with clang-tidy-23"
        raise QueryFailedError(message) from failure
    if finished.returncode != 0:
        detail = (finished.stderr or finished.stdout).strip().splitlines()
        message = f"{CLANG_QUERY} failed on {unit}: {detail[0] if detail else 'no output'}"
        raise QueryFailedError(message)
    diagnostic = _ERROR.search(finished.stderr)
    if diagnostic is not None:
        message = f"{CLANG_QUERY} could not parse {unit}: {diagnostic.group(0).strip()}"
        raise QueryFailedError(message)
    return QueryOutput(finished.stdout)


def query_units(
    repo: Path,
    units: list[UnitPath],
    query: Query,
    *,
    executor: ExecutorFactory = ThreadPoolExecutor,
) -> list[QueryOutput] | Prose:
    """Run the query over every unit, returning what each printed or why one failed.

    ``executor`` builds what the units are queried on: a thread pool by
    default, and in a test an executor that runs each query on the test's own
    thread.
    """
    with TemporaryDirectory() as scratch:
        script = Path(scratch) / "gate.query"
        _ = script.write_text(query, encoding="utf-8")
        try:
            # The thread pool's own default count, spelled out for the factory.
            with executor(WorkerCount(min(32, (os.process_cpu_count() or 1) + 4))) as pool:
                return list(pool.map(partial(query_unit, repo, script), units))
        except QueryFailedError as failure:
            return Prose(str(failure))


class Queried(NamedTuple):
    """The tree queried whole: its root, its units, and what clang-query printed for each."""

    repo: Path
    units: list[UnitPath]
    outputs: list[QueryOutput]


def query_tree(query: Query, *, executor: ExecutorFactory = ThreadPoolExecutor) -> Queried | None:
    """Query every unit of the binding from the repository root, or print why not and give None.

    ``executor`` is handed to ``query_units``.
    """
    repo = git_toplevel()
    units = translation_units(repo)
    if isinstance(units, str):
        emit(units)
        return None
    outputs = query_units(repo, units, query, executor=executor)
    if isinstance(outputs, str):
        emit(outputs)
        return None
    return Queried(repo, units, outputs)

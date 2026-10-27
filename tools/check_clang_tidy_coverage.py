# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_clang_tidy_coverage.py: every gated C++ source is in the lint DB, at the standard.

The C++ clang-tidy gate runs ``run-clang-tidy -p build-tidy`` over cpp/src,
cpp/tests and cpp/benchmarks, which lints exactly the translation units present
in ``compile_commands.json``.  Driving the lint from the compile database makes
the build system the single source of truth for coverage: no directory can be
dropped, as a hand-maintained glob of sources can drop one.

This guard holds, of that database and the gated sources (every ``.cpp`` under
those directories but the fuzz targets and the sources built to fail):

* every gated source is in it: a source on disk that is not wired into any
  CMake target never appears there, so ``run-clang-tidy`` silently skips it,
  and it is silently unbuilt;
* every command for a gated source names the project's standard, C++23 with
  the GNU extensions, and compiles at it: the standard reaches most targets
  through the library's PUBLIC compile feature, so a target linking neither
  the library nor a dependency carrying it falls back to the compiler's
  default, which a compiler version decides.  The compiler decides the rest:
  the command, unchanged but for ``-###``, makes clang's driver print the
  compile jobs it would run, each with the frontend arguments the command
  resolves to; the first job, the one reading the source, must name a
  standard, whatever the default; and the compiler says what it predefines at
  the standard the job names last.  Only a program named as a clang driver is
  asked, with ccache disabled and clang's default configuration files and
  ``CCC_OVERRIDE_OPTIONS`` left out, so the standard comes from the command
  alone (a configuration file the command names included); a command whose
  program is named otherwise, a launcher such as ccache before the compiler
  among them, is refused without being run.  A build that reads a default
  configuration file or that variable can compile at another standard than the
  one read here.

Exit codes:
  0: every property above holds.
  1: a gated source is missing from the database, compiled at another
     standard, or compiled by a command that is refused.
  2: compile_commands.json not found (run ``cmake -S cpp -B cpp/build-tidy``
     first), or no gated source found.
"""

from __future__ import annotations

import argparse
import functools
import itertools
import json
import os
import re
import shlex
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

from tools._clang_query import CompileArg, UnitPath, unit_arguments
from tools._common import CPP_LINT_TREE, RelPath, WorkerCount, emit, git_toplevel

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools._clang_query import DatabaseEntry
    from tools._common import ExecutorFactory

# A macro the compiler predefines, and the value it gives it.
MacroName = NewType("MacroName", str)
MacroValue = NewType("MacroValue", str)

# What the compiler predefines at the project's standard, the one
# cpp/CMakeLists.txt asks of the binding's own targets (cxx_std_23, the
# compiler's extensions left on): C++23 as ``__cplusplus``, and no
# ``__STRICT_ANSI__``, which the GNU extensions leave undefined.
CPLUSPLUS = MacroName("__cplusplus")
CPLUSPLUS_23 = MacroValue("202302L")
STRICT_ANSI = MacroName("__STRICT_ANSI__")

# The name every clang driver's program starts with: a command whose program is
# named otherwise is not asked.
_CLANG = "clang"

# What the compiler is asked under: ccache, which a masquerading clang name can
# be, compiles nothing and records nothing, and clang reads no default
# configuration file; ``CCC_OVERRIDE_OPTIONS`` is left out of the environment.
_ASKED_ENVIRONMENT = {"CCACHE_DISABLE": "1", "CLANG_NO_DEFAULT_CONFIG": "1"}
_LEFT_OUT = "CCC_OVERRIDE_OPTIONS"

# The language a gated source is compiled as, in a compile job's ``-x``, and
# the spellings of the option a compile job names its standard with.
CXX = CompileArg("c++")
_FRONTEND_STANDARD = ("-std=", "--std=")

# One line of ``-dM`` output: ``#define NAME`` and its value, if any.
_DEFINE = re.compile(r"^#define (\S+)(?: (.*))?$", re.MULTILINE)

# The status given here to a compiler the system cannot start, the one a shell
# gives a command it cannot find.
_NOT_RUN = ExitStatus(127)


class Unit(NamedTuple):
    """One compile database entry: its source, repo-relative and as written, and its command."""

    source: RelPath
    written: UnitPath
    directory: Path
    arguments: list[CompileArg]


class Answer(NamedTuple):
    """What a compiler run printed: its exit status, its output and its diagnostics."""

    status: ExitStatus
    output: Prose
    diagnostics: Prose


class Job(NamedTuple):
    """A compile job the driver lists: the language it reads, and the standard it names last."""

    language: CompileArg | None
    standard: CompileArg | None


class Off(NamedTuple):
    """A gated source, and how its command misses the standard or why it is refused."""

    source: RelPath
    reason: Prose


class Verdicts(NamedTuple):
    """The gated sources compiled at another standard, and those whose command is refused."""

    off: list[Off]
    refused: list[Off]


type AskDriver = Callable[[Unit], Answer]
type AskMacros = Callable[[CompileArg, CompileArg, Path], Answer]


def uncovered_sources(src_files: set[RelPath], db_files: set[RelPath]) -> list[RelPath]:
    """Return the sorted src files (repo-relative) absent from the compile DB.

    Pure set difference ``src_files - db_files``: only membership of each source
    file in the DB matters.  Extra DB entries (a fetched dependency's units
    under ``_deps``, anything outside the gated directories) are intentionally
    ignored, since this guard checks *coverage of sources*, not the converse.
    """
    return sorted(src_files - db_files)


def driver_command(unit: Unit) -> list[CompileArg]:
    """Return the unit's command with ``-###`` after its program.

    The driver then prints the jobs the command would run, each with the
    frontend arguments the command resolves to, and runs none of them: nothing
    is written, and no option is left unused.  The frontend takes the last
    standard a job names; the compiler's macros settle an alias.
    """
    return [unit.arguments[0], CompileArg("-###"), *unit.arguments[1:]]


def macros_command(compiler: CompileArg, standard: CompileArg) -> list[CompileArg]:
    """Return the command printing what ``compiler`` predefines at ``standard``, over empty C++."""
    empty = [CompileArg("-x"), CXX, CompileArg("-E"), CompileArg("-dM"), CompileArg(os.devnull)]
    return [compiler, CompileArg(f"-std={standard}"), *empty]


def _run(command: list[CompileArg], directory: Path) -> Answer:
    """Run ``command`` from ``directory``, reading nothing, and return what it printed.

    It runs under ``_ASKED_ENVIRONMENT``, without ``CCC_OVERRIDE_OPTIONS``.  A
    compiler the system cannot start is a refused command, its error the diagnostic.
    """
    environment = {**os.environ, **_ASKED_ENVIRONMENT}
    _ = environment.pop(_LEFT_OUT, None)
    try:
        finished = subprocess.run(
            command,
            cwd=directory,
            env=environment,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as error:
        return Answer(_NOT_RUN, Prose(""), Prose(str(error)))
    return Answer(ExitStatus(finished.returncode), Prose(finished.stdout), Prose(finished.stderr))


def ask_driver(unit: Unit) -> Answer:
    """Run ``driver_command(unit)`` from the unit's directory."""
    return _run(driver_command(unit), unit.directory)


def ask_macros(compiler: CompileArg, standard: CompileArg, directory: Path) -> Answer:
    """Run ``macros_command(compiler, standard)`` from ``directory``, the unit's."""
    return _run(macros_command(compiler, standard), directory)


def compile_jobs(answer: Answer) -> list[Job]:
    """Return the compile jobs a driver's ``-###`` diagnostics list.

    Each job is a line naming ``-cc1``, its words quoted as a shell quotes
    them; its language is its last ``-x``, its standard its last ``-std=`` or
    ``--std=``, the two spellings the frontend takes, the driver passing either.
    """
    jobs: list[Job] = []
    for line in answer.diagnostics.splitlines():
        words = [CompileArg(word) for word in shlex.split(line)] if '"-cc1"' in line else []
        if "-cc1" not in words:
            continue
        languages = [after for before, after in itertools.pairwise(words) if before == "-x"]
        standards = [
            CompileArg(word.partition("=")[2])
            for word in words
            if word.startswith(_FRONTEND_STANDARD)
        ]
        jobs.append(Job(languages[-1] if languages else None, standards[-1] if standards else None))
    return jobs


def refusal(answer: Answer) -> Prose:
    """Return why the compiler refused a command: its exit status and its first error."""
    lines = answer.diagnostics.splitlines()
    error = next((line for line in lines if "error:" in line), next(iter(lines), ""))
    return Prose(f"exit {answer.status}: {error}")


def missed_standard(answer: Answer) -> Prose | None:
    """Return how predefined macros miss the project's standard, or None when they are at it."""
    if answer.status != 0:
        return Prose(f"the compiler refused to print its macros ({refusal(answer)})")
    macros = {
        MacroName(name): MacroValue(value or "") for name, value in _DEFINE.findall(answer.output)
    }
    missed: list[Prose] = []
    if macros.get(CPLUSPLUS) != CPLUSPLUS_23:
        shown = macros.get(CPLUSPLUS, "undefined")
        missed.append(Prose(f"{CPLUSPLUS} is {shown}, not {CPLUSPLUS_23}"))
    if STRICT_ANSI in macros:
        missed.append(Prose(f"{STRICT_ANSI} is defined, so the GNU extensions are off"))
    return Prose("; ".join(missed)) if missed else None


def _job_missed(job: Job, unit: Unit, macros: AskMacros) -> Prose | None:
    """Return how the job reading a unit's source misses the standard, or None when it is at it."""
    if job.language != CXX:
        return Prose(f"the source is compiled as {job.language}")
    if job.standard is None:
        return Prose("the job names no standard, so the compiler's version decides it")
    missed = missed_standard(macros(unit.arguments[0], job.standard, unit.directory))
    return None if missed is None else Prose(f"{missed} (-std={job.standard})")


def off_standard(
    units: list[Unit],
    driver: AskDriver = ask_driver,
    macros: AskMacros = ask_macros,
    *,
    executor: ExecutorFactory = ThreadPoolExecutor,
) -> Verdicts:
    """Return, sorted, the gated sources a command compiles at another standard, and those refused.

    Every entry is asked, since a source two targets compile has two, but one
    whose program is not named as a clang driver, which is refused unrun.  The
    driver is asked on what ``executor`` builds: a thread pool by default, and
    in a test an executor on the test's own thread; the macros once for each
    command program, standard and directory.  The first job is judged, the one
    reading the source; a job after it, as ``-save-temps`` adds, reads what the
    first wrote.  A driver whose job list cannot be read refuses the command.
    """
    refused = {
        Off(unit.source, Prose(f"the command runs {unit.arguments[0]}, not a clang driver"))
        for unit in units
        if not Path(unit.arguments[0]).name.startswith(_CLANG)
    }
    asked = [unit for unit in units if Path(unit.arguments[0]).name.startswith(_CLANG)]
    # The thread pool's own default count, spelled out for the factory.
    with executor(WorkerCount(min(32, (os.process_cpu_count() or 1) + 4))) as pool:
        answers = list(pool.map(driver, asked))
    once = functools.cache(macros)
    off: set[Off] = set()
    for unit, answer in zip(asked, answers, strict=True):
        try:
            jobs = compile_jobs(answer)
        except ValueError as error:
            refused.add(Off(unit.source, Prose(f"the driver's jobs cannot be read: {error}")))
            continue
        if answer.status != 0 or not jobs:
            refused.add(Off(unit.source, refusal(answer)))
            continue
        missed = _job_missed(jobs[0], unit, once)
        if missed is not None:
            off.add(Off(unit.source, missed))
    return Verdicts(sorted(off), sorted(refused))


def _units(db: list[DatabaseEntry], repo: Path) -> list[Unit]:
    """Read every entry inside the repository, its ``file`` as a repo-relative POSIX path."""
    units: list[Unit] = []
    for entry in db:
        directory = Path(entry["directory"])
        try:
            source = RelPath((directory / entry["file"]).resolve().relative_to(repo).as_posix())
        except ValueError:
            continue  # an entry outside the repository is no gated source
        units.append(Unit(source, entry["file"], directory, unit_arguments(entry)))
    return units


# The directories of cpp/tests no test build compiles into the database.
_UNBUILT_TEST_DIRS = frozenset({"fuzz", "compile_fail"})


def _gated_sources(repo: Path) -> set[RelPath]:
    """Return every .cpp the gate lints, repo-relative.

    The gate lints the tests and the benchmarks too, so an unwired source in
    either must fail here rather than go unlinted.  Two directories of the
    tests are left out, since this database never lists them: the fuzz
    targets compile only with ``-DALETHEIA_FUZZ=ON``, in a build tree of their
    own (the recipe in cpp/tests/fuzz/fuzz_parse_response.cpp), and the
    sources under compile_fail are built to fail, each by a test that runs the
    compiler on it.
    """
    cpp = repo / "cpp"
    found = [*(cpp / "src").rglob("*.cpp"), *(cpp / "benchmarks").rglob("*.cpp")]
    found += [
        p
        for p in (cpp / "tests").rglob("*.cpp")
        if _UNBUILT_TEST_DIRS.isdisjoint(p.relative_to(cpp / "tests").parts)
    ]
    return {RelPath(p.resolve().relative_to(repo).as_posix()) for p in found}


def _emit_group(heading: Prose, sources: list[Off] | list[RelPath]) -> None:
    """Print one heading and its sources, each with its reason where it has one."""
    if not sources:
        return
    emit(f"check-clang-tidy-coverage: {heading}")
    for source in sources:
        emit(f"  {source.source}: {source.reason}" if isinstance(source, Off) else f"  {source}")


def main(
    repo: Path | None = None,
    *,
    driver: AskDriver = ask_driver,
    macros: AskMacros = ask_macros,
    executor: ExecutorFactory = ThreadPoolExecutor,
) -> ExitStatus:
    """Fail (exit 1) if a gated source is missing from the database or off the standard.

    ``repo`` defaults to the enclosing git work tree; tests inject a temp tree,
    the compiler's answers and an executor running on their own thread.
    """
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    repo = (repo if repo is not None else git_toplevel()).resolve()
    db_path = repo / "cpp" / CPP_LINT_TREE / "compile_commands.json"
    if not db_path.is_file():
        emit(
            f"check-clang-tidy-coverage: {db_path} not found; "
            + f"run 'cmake -S cpp -B cpp/{CPP_LINT_TREE}' first"
        )
        return ExitStatus(2)

    db = cast("list[DatabaseEntry]", json.loads(db_path.read_text(encoding="utf-8")))
    units = _units(db, repo)
    src_files = _gated_sources(repo)
    if not src_files:
        emit(
            "check-clang-tidy-coverage: FAIL, no gated .cpp sources found under"
            + f" {repo / 'cpp'}'s src, tests (the fuzz targets and compile_fail aside)"
            + " or benchmarks."
        )
        emit(
            "This gate reports 'every source is covered' by finding none uncovered, so an\n"
            + "empty source set passes vacuously.  Zero sources means the tree moved out\n"
            + "from under the glob, not that coverage is complete."
        )
        return ExitStatus(2)

    missing = uncovered_sources(src_files, {unit.source for unit in units})
    gated = [unit for unit in units if unit.source in src_files]
    verdicts = off_standard(gated, driver, macros, executor=executor)
    _emit_group(
        Prose(
            "gated C++ sources missing from compile_commands.json"
            + " (not wired into a CMake target, so silently unbuilt and unlinted):"
        ),
        missing,
    )
    _emit_group(
        Prose(
            "gated C++ sources compiled at another standard than"
            + " C++23 with the GNU extensions (-std=gnu++23):"
        ),
        verdicts.off,
    )
    _emit_group(
        Prose("gated C++ sources whose command is refused (no clang driver, or refused by it):"),
        verdicts.refused,
    )
    if missing or verdicts.off or verdicts.refused:
        return ExitStatus(1)

    emit(
        f"check-clang-tidy-coverage: ok ({len(src_files)} gated C++ sources all in the compile DB,"
        + " each compiled at C++23 with the GNU extensions)"
    )
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())

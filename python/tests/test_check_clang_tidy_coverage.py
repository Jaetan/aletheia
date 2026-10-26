# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_clang_tidy_coverage``, the C++ lint database guard.

In layers, mirroring the gate's own discipline:

* the pure parts: ``uncovered_sources``, whose discriminating case is an
  *extra* DB entry (a fetched dependency's unit) that must NOT be flagged, since
  the guard checks sources-are-covered, not the converse; the two commands the
  compiler is asked; the compile jobs read from the driver's ``-###`` lines; and
  the predefined macros read against the standard.
* ``off_standard`` and ``main`` over a stand-in driver and compiler and an
  executor on the test's own thread: every entry asked, both polarities of each
  arm, proving the guard bites and that path normalization works.
* the compiler itself: the standard a command compiles at is its own reading,
  whatever spelling, override or unrelated option the command carries.
"""

from __future__ import annotations

import json
import os
import shutil
from functools import partial
from pathlib import Path
from typing import Literal, NamedTuple

import pytest
from _executors import DrivenExecutor, Order

from tools._clang_query import CommandLine, CompileArg, UnitPath
from tools._common import CPP_LINT_TREE, RelPath
from tools.check_clang_tidy_coverage import (
    CXX,
    Answer,
    Job,
    Off,
    Unit,
    Verdicts,
    ask_macros,
    compile_jobs,
    driver_command,
    macros_command,
    main,
    missed_standard,
    off_standard,
    refusal,
    uncovered_sources,
)

from aletheia.common_types import ExitStatus, Prose

COMPILER = CompileArg("clang++-23")
STANDARD = CompileArg("-std=gnu++23")
COMPILE = CompileArg("-c")
OLDER = CompileArg("-std=c++17")
CCACHE = CompileArg("/usr/bin/ccache")
GNU23, CXX17, CXX20 = CompileArg("gnu++23"), CompileArg("c++17"), CompileArg("c++20")

A_CPP, B_CPP = RelPath("cpp/src/a.cpp"), RelPath("cpp/src/detail/b.cpp")

# What clang++-23 predefines at C++23 with the GNU extensions, at its default
# (C++17 with them), and at C++17 without them, excerpts of its -E -dM output.
GNU_23 = Answer(
    ExitStatus(0), Prose("#define __GNUC__ 4\n#define __cplusplus 202302L\n"), Prose("")
)
GNU_17 = Answer(
    ExitStatus(0), Prose("#define __GNUC__ 4\n#define __cplusplus 201703L\n"), Prose("")
)
STRICT_17 = Answer(
    ExitStatus(0), Prose("#define __STRICT_ANSI__ 1\n#define __cplusplus 201703L\n"), Prose("")
)

# The opening words of a compile job as clang++-23's -### prints it.
JOB_WORDS = ["/usr/lib/llvm-23/bin/clang", "-cc1", "-triple", "x86_64-pc-linux-gnu", "-emit-obj"]


def _driver_says(standards: list[CompileArg], language: CompileArg = CXX) -> Answer:
    """Return what the driver prints for a job naming ``standards`` and reading ``language``.

    The driver prints its version first, then each job with every word in double quotes.
    """
    words = [*JOB_WORDS, *(f"-std={value}" for value in standards), "-x", language, "/repo/a.cpp"]
    job = " ".join(f'"{word}"' for word in words)
    return Answer(ExitStatus(0), Prose(""), Prose(f"clang version 23.1.2\n {job}\n"))


def _stand_in_driver(unit: Unit) -> Answer:
    """Answer as the driver would for the one option the tests vary, the standard's."""
    named = [
        CompileArg(arg.removeprefix("-std=")) for arg in unit.arguments if arg.startswith("-std=")
    ]
    return _driver_says(named[-1:])


def _stand_in_macros(_compiler: CompileArg, standard: CompileArg, _directory: Path) -> Answer:
    """Answer as the compiler would at the standards the tests name, C++17 with GNU otherwise."""
    return {GNU23: GNU_23, CXX17: STRICT_17}.get(standard, GNU_17)


class TestUncoveredSources:
    """Pure set-difference: src files absent from the compile DB."""

    def test_all_covered_is_empty(self) -> None:
        """Every source present in the DB: no uncovered files."""
        assert uncovered_sources({A_CPP, B_CPP}, {A_CPP, B_CPP}) == []

    def test_missing_source_is_reported(self) -> None:
        """A source absent from the DB is returned (the guard's whole point)."""
        assert uncovered_sources({A_CPP, B_CPP}, {A_CPP}) == [B_CPP]

    def test_extra_db_entries_are_ignored(self) -> None:
        """DB entries with no gated counterpart (a fetched dependency's unit) are not flagged."""
        assert uncovered_sources({A_CPP}, {A_CPP, RelPath("cpp/build/_deps/x.cpp")}) == []


def test_the_driver_command_is_the_unit_s_command_with_the_dry_run_after_its_program() -> None:
    """``-###`` goes right after the program, every other word unchanged, a ``--`` included."""
    written = UnitPath("/repo/cpp/src/a.cpp")
    rest = [STANDARD, CompileArg("-o"), CompileArg("a.o"), COMPILE, CompileArg("--")]
    unit = Unit(A_CPP, written, Path("/b"), [COMPILER, *rest, CompileArg(written)])
    assert driver_command(unit) == [COMPILER, CompileArg("-###"), *rest, CompileArg(written)]


def test_the_macros_command_names_the_job_s_standard_over_an_empty_input() -> None:
    """The compiler is asked at the standard the job names."""
    empty = [CompileArg("-x"), CXX, CompileArg("-E"), CompileArg("-dM"), CompileArg(os.devnull)]
    assert macros_command(COMPILER, GNU23) == [COMPILER, STANDARD, *empty]


class TestCompileJobs:
    """The jobs the driver lists, each with its language and its last standard."""

    def test_a_job_reads_its_language_and_its_standard(self) -> None:
        """One ``-cc1`` line: its ``-x`` and its ``-std=``; the version line is no job."""
        assert compile_jobs(_driver_says([GNU23])) == [Job(CXX, GNU23)]

    def test_the_last_standard_a_job_names_is_its_standard(self) -> None:
        """A job naming two standards, as ``-Xclang`` leaves it, compiles at the last."""
        assert compile_jobs(_driver_says([GNU23, CXX20])) == [Job(CXX, CXX20)]

    def test_a_job_reads_the_standard_in_either_spelling_the_driver_passes(self) -> None:
        """The driver passes ``--std=`` to the frontend as written, which takes it as ``-std=``."""
        words = [*JOB_WORDS, "--std=gnu++23", "-x", "c++", "/repo/a.cpp"]
        job = " ".join(f'"{word}"' for word in words)
        said = Answer(ExitStatus(0), Prose(""), Prose(f" {job}\n"))
        assert compile_jobs(said) == [Job(CXX, GNU23)]

    def test_a_job_naming_no_standard_has_none(self) -> None:
        """No ``-std=``: the compiler's default, read later as such."""
        assert compile_jobs(_driver_says([], CompileArg("c"))) == [Job(CompileArg("c"), None)]

    def test_a_refusal_lists_no_job(self) -> None:
        """A driver that only complains lists nothing to compile."""
        said = Answer(ExitStatus(1), Prose(""), Prose("clang++-23: error: no input files\n"))
        assert not compile_jobs(said)


def test_a_refusal_names_the_first_error_not_the_warnings_before_it() -> None:
    """The reason is the first line saying ``error:``, else the first line."""
    said = "clang++-23: warning: argument unused\nclang++-23: error: unknown argument: '--bogus'\n"
    assert refusal(Answer(ExitStatus(1), Prose(""), Prose(said))) == (
        "exit 1: clang++-23: error: unknown argument: '--bogus'"
    )
    assert refusal(Answer(ExitStatus(127), Prose(""), Prose("[Errno 2] gone"))) == (
        "exit 127: [Errno 2] gone"
    )


class TestMissedStandard:
    """The predefined macros say whether a command compiles at C++23 with the GNU extensions."""

    def test_gnu_23_is_at_the_standard(self) -> None:
        """``__cplusplus`` 202302L and no ``__STRICT_ANSI__``: at the standard."""
        assert missed_standard(GNU_23) is None

    def test_another_language_version_misses_it(self) -> None:
        """Another ``__cplusplus``, or none, names what the compiler gave."""
        assert missed_standard(GNU_17) == "__cplusplus is 201703L, not 202302L"
        nothing = Answer(ExitStatus(0), Prose(""), Prose(""))
        assert missed_standard(nothing) == "__cplusplus is undefined, not 202302L"

    def test_the_strict_dialect_misses_it(self) -> None:
        """A standard without the GNU extensions defines ``__STRICT_ANSI__``."""
        assert missed_standard(STRICT_17) == (
            "__cplusplus is 201703L, not 202302L;"
            + " __STRICT_ANSI__ is defined, so the GNU extensions are off"
        )

    def test_a_refusal_to_print_the_macros_misses_it(self) -> None:
        """A compiler refusing the macros command says nothing of the standard."""
        refused = Answer(ExitStatus(1), Prose(""), Prose("clang++-23: error: invalid value\n"))
        assert missed_standard(refused) == (
            "the compiler refused to print its macros (exit 1: clang++-23: error: invalid value)"
        )


def _unit(source: RelPath, *words: CompileArg) -> Unit:
    """Return a unit of ``source`` whose command is the compiler and ``words``."""
    return Unit(source, UnitPath(f"/repo/{source}"), Path("/b"), [COMPILER, *words])


class TestOffStandard:
    """Every entry is asked, each answer read for its own unit, the macros once per standard."""

    def test_every_entry_of_a_source_is_asked(self) -> None:
        """A source compiled by two targets is off when either command is."""
        units = [_unit(A_CPP, STANDARD), _unit(A_CPP, OLDER), _unit(B_CPP, STANDARD)]
        verdicts = off_standard(units, _stand_in_driver, _stand_in_macros, executor=DrivenExecutor)
        missed = missed_standard(STRICT_17)
        assert verdicts == Verdicts([Off(A_CPP, Prose(f"{missed} (-std=c++17)"))], [])

    def test_each_answer_is_read_for_the_unit_it_was_asked_for(self) -> None:
        """Answers finishing in the reverse of their asking still name their own units."""
        units = [_unit(A_CPP, OLDER), _unit(B_CPP, STANDARD)]
        last_first = partial(DrivenExecutor, order=Order.LAST_SUBMITTED)
        verdicts = off_standard(units, _stand_in_driver, _stand_in_macros, executor=last_first)
        assert [entry.source for entry in verdicts.off] == [A_CPP]

    def test_the_compiler_is_asked_its_macros_once_per_standard(self) -> None:
        """Units sharing a compiler and a standard share one macros run."""
        asked: list[CompileArg | None] = []

        def counted(compiler: CompileArg, standard: CompileArg, directory: Path) -> Answer:
            asked.append(standard)
            return _stand_in_macros(compiler, standard, directory)

        units = [_unit(A_CPP, STANDARD), _unit(B_CPP, STANDARD), _unit(A_CPP, OLDER)]
        _ = off_standard(units, _stand_in_driver, counted, executor=DrivenExecutor)
        assert asked == [GNU23, CXX17]

    def test_a_job_naming_no_standard_is_off_whatever_the_default(self) -> None:
        """No ``-std`` leaves the standard to the compiler's version, even a default of C++23."""
        verdicts = off_standard(
            [_unit(A_CPP)], _stand_in_driver, lambda _c, _s, _d: GNU_23, executor=DrivenExecutor
        )
        reason = Prose("the job names no standard, so the compiler's version decides it")
        assert verdicts.off == [Off(A_CPP, reason)]

    def test_a_command_not_run_by_clang_is_refused_unrun(self) -> None:
        """A launcher before the compiler is no clang driver: refused by name, nothing run."""
        launched = Unit(A_CPP, UnitPath("/repo/a.cpp"), Path("/b"), [CCACHE, COMPILER, STANDARD])

        def never(_unit: Unit) -> Answer:
            asked = "the driver was asked"
            raise AssertionError(asked)

        verdicts = off_standard([launched], never, _stand_in_macros, executor=DrivenExecutor)
        reason = Prose(f"the command runs {CCACHE}, not a clang driver")
        assert verdicts == Verdicts([], [Off(A_CPP, reason)])

    def test_a_source_compiled_as_another_language_is_off(self) -> None:
        """A job reading the source as C compiles it at no C++ standard."""
        verdicts = off_standard(
            [_unit(A_CPP, STANDARD)],
            lambda _unit: _driver_says([GNU23], CompileArg("c")),
            _stand_in_macros,
            executor=DrivenExecutor,
        )
        assert verdicts.off == [Off(A_CPP, Prose("the source is compiled as c"))]

    def test_a_refused_command_is_refused_not_off(self) -> None:
        """A command the driver refuses, or one listing no job, is reported as refused."""
        said = Answer(ExitStatus(1), Prose(""), Prose("clang++-23: error: unknown argument\n"))
        silent = Answer(ExitStatus(0), Prose(""), Prose(""))
        answers = {A_CPP: said, B_CPP: silent}
        verdicts = off_standard(
            [_unit(A_CPP, STANDARD), _unit(B_CPP, STANDARD)],
            lambda unit: answers[unit.source],
            _stand_in_macros,
            executor=DrivenExecutor,
        )
        assert verdicts == Verdicts([], [Off(A_CPP, refusal(said)), Off(B_CPP, refusal(silent))])


def _make_repo(
    tmp_path: Path, db_files: list[RelPath], commands: dict[RelPath, CommandLine] | None = None
) -> Path:
    """Create a tree with cpp/src sources A_CPP and B_CPP and a lint database listing ``db_files``.

    Each entry's command is the one ``commands`` gives it, else the compiler's
    at the standard.
    """
    repo = tmp_path / "repo"
    tree = repo / "cpp" / CPP_LINT_TREE
    (repo / "cpp" / "src" / "detail").mkdir(parents=True)
    tree.mkdir(parents=True)
    _ = (repo / A_CPP).write_text("int a;\n", encoding="utf-8")
    _ = (repo / B_CPP).write_text("int b;\n", encoding="utf-8")
    given = commands or {}
    db = [
        {
            "directory": str(tree),
            "file": str(repo / f),
            "command": given.get(f, CommandLine(f"{COMPILER} {COMPILE} {repo / f} {STANDARD}")),
        }
        for f in db_files
    ]
    _ = (tree / "compile_commands.json").write_text(json.dumps(db), encoding="utf-8")
    return repo


def _main_with_stand_ins(repo: Path) -> ExitStatus:
    """Run the gate over ``repo`` with the stand-in driver and compiler, on the test's thread."""
    return main(
        repo=repo, driver=_stand_in_driver, macros=_stand_in_macros, executor=DrivenExecutor
    )


def test_main_passes_when_all_sources_in_db_at_the_standard(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """End-to-end: both sources in the DB, each at the standard: exit 0."""
    repo = _make_repo(tmp_path, [A_CPP, B_CPP])
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_coverage"])
    assert _main_with_stand_ins(repo) == 0


def test_main_reads_a_relative_file_from_its_directory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """End-to-end: an entry naming its file relative to its directory names the gated source."""
    repo = _make_repo(tmp_path, [A_CPP, B_CPP])
    db = [
        {"directory": str(repo / "cpp"), "file": name, "command": f"{COMPILER} {STANDARD}"}
        for name in ("src/a.cpp", "src/detail/b.cpp")
    ]
    db_path = repo / "cpp" / CPP_LINT_TREE / "compile_commands.json"
    _ = db_path.write_text(json.dumps(db), encoding="utf-8")
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_coverage"])
    assert _main_with_stand_ins(repo) == 0


def test_main_holds_only_the_gated_sources_to_the_standard(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """End-to-end: a fetched dependency's unit, at another standard, passes."""
    vendored = RelPath(f"cpp/{CPP_LINT_TREE}/_deps/x-src/x.cpp")
    repo = _make_repo(
        tmp_path, [A_CPP, B_CPP, vendored], {vendored: CommandLine(f"{COMPILER} {OLDER}")}
    )
    (repo / vendored).parent.mkdir(parents=True)
    _ = (repo / vendored).write_text("int x;\n", encoding="utf-8")
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_coverage"])
    assert _main_with_stand_ins(repo) == 0


class Refusal(NamedTuple):
    """A database the gate refuses for b.cpp, and the words naming what b.cpp lacks."""

    db_files: list[RelPath]
    commands: dict[RelPath, CommandLine]
    named: Prose


# The option the refusal test's driver refuses.
_REFUSED_OPTION = CompileArg("--refused")


@pytest.mark.parametrize(
    "refused_case",
    [
        pytest.param(
            Refusal([A_CPP], {}, Prose("missing from compile_commands.json")), id="missing"
        ),
        pytest.param(
            Refusal(
                [A_CPP, B_CPP],
                {B_CPP: CommandLine(f"{COMPILER} {COMPILE} {OLDER}")},
                Prose("another standard than C++23 with the GNU extensions"),
            ),
            id="off-standard",
        ),
        pytest.param(
            Refusal(
                [A_CPP, B_CPP],
                {B_CPP: CommandLine(f"{COMPILER} {_REFUSED_OPTION}")},
                Prose("whose command is refused"),
            ),
            id="refused",
        ),
    ],
)
def test_main_fails_naming_the_source_and_what_it_lacks(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
    refused_case: Refusal,
) -> None:
    """End-to-end: b.cpp absent, compiled at another standard, or refused: exit 1, naming it."""
    repo = _make_repo(tmp_path, refused_case.db_files, refused_case.commands)
    refused = Answer(ExitStatus(1), Prose(""), Prose("clang++-23: error: unknown argument\n"))

    def driver(unit: Unit) -> Answer:
        return refused if _REFUSED_OPTION in unit.arguments else _stand_in_driver(unit)

    monkeypatch.setattr("sys.argv", ["check_clang_tidy_coverage"])
    assert main(repo=repo, driver=driver, macros=_stand_in_macros, executor=DrivenExecutor) == 1
    out = capsys.readouterr().out
    assert refused_case.named in out, out
    assert f"\n  {B_CPP}" in out, out
    assert A_CPP not in out, out


def test_main_errors_when_db_absent(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """No compile_commands.json: exit 2 (build not configured)."""
    repo = tmp_path / "repo"
    (repo / "cpp" / "src").mkdir(parents=True)
    monkeypatch.setattr("sys.argv", ["check_clang_tidy_coverage"])
    assert _main_with_stand_ins(repo) == 2


type Reading = Literal["at", "off", "refused"]


class Spelling(NamedTuple):
    """Options a command carries, and how the compiler reads them: at the standard, off, refused."""

    options: CommandLine
    reading: Reading


@pytest.mark.process("the standard a command compiles at is the compiler's own reading of it")
@pytest.mark.parametrize(
    "spelling",
    [
        pytest.param(Spelling(CommandLine("-std=gnu++23"), "at"), id="cmake-form"),
        pytest.param(Spelling(CommandLine("--std=gnu++23"), "at"), id="double-dash"),
        pytest.param(Spelling(CommandLine("--std gnu++23"), "at"), id="apart"),
        pytest.param(Spelling(CommandLine("-std=gnu++2b"), "at"), id="older-alias"),
        pytest.param(Spelling(CommandLine("-std=c++20 -std=gnu++23"), "at"), id="last-wins"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -Werror"), "at"), id="werror"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -oz.o"), "at"), id="output-joined"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 --output=z.o"), "at"), id="output-long"),
        pytest.param(
            Spelling(CommandLine("-std=gnu++23 -MD -MT y.o -MF y.o.d"), "at"), id="depfile"
        ),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -include /no/such.h"), "at"), id="include"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -std=c++20"), "off"), id="later-std"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -ansi"), "off"), id="ansi"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 --std c++20"), "off"), id="apart-later"),
        pytest.param(Spelling(CommandLine("-Xclang -std=c++20 -std=gnu++23"), "off"), id="xclang"),
        pytest.param(Spelling(CommandLine("-std=c++23"), "off"), id="strict"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -x c"), "off"), id="as-c"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 -save-temps"), "at"), id="save-temps"),
        pytest.param(Spelling(CommandLine(""), "off"), id="the-default"),
        pytest.param(Spelling(CommandLine("-std=gnu++23 --bogus-option"), "refused"), id="refused"),
    ],
)
def test_the_compiler_reads_the_standard_of_the_command(tmp_path: Path, spelling: Spelling) -> None:
    """Every spelling, override and unrelated option is read as clang reads it, writing nothing."""
    compiler = shutil.which(COMPILER)
    assert compiler is not None, f"{COMPILER} is not on PATH"
    source, directory = tmp_path / "unit.cpp", tmp_path / "tree"
    directory.mkdir()
    _ = source.write_text("int unit;\n", encoding="utf-8")
    written = UnitPath(str(source))
    options = [CompileArg(word) for word in spelling.options.split()]
    tail = [CompileArg("-o"), CompileArg("unit.o"), COMPILE, CompileArg("--"), CompileArg(written)]
    arguments = [CompileArg(compiler), *options, *tail]
    unit = Unit(RelPath("cpp/src/unit.cpp"), written, directory, arguments)
    verdicts = off_standard([unit], executor=DrivenExecutor)
    read: Reading = "off" if verdicts.off else "refused" if verdicts.refused else "at"
    assert read == spelling.reading, verdicts
    assert not list(directory.iterdir()), "asking the compiler wrote a file"


def _clang_unit(directory: Path, program: CompileArg, *words: CompileArg) -> Unit:
    """Return a unit of a source in ``directory`` compiled by ``program`` with ``words``."""
    source = directory / "unit.cpp"
    _ = source.write_text("int unit;\n", encoding="utf-8")
    written = UnitPath(str(source))
    tail = [CompileArg("-o"), CompileArg("unit.o"), COMPILE, CompileArg(written)]
    return Unit(RelPath("cpp/src/unit.cpp"), written, directory, [program, *words, *tail])


@pytest.mark.process("the environment a compiler is asked under is the child's own")
def test_the_compiler_is_asked_without_ccache_default_configuration_or_override(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A stand-in compiler prints what it was run under: from the unit's directory, so asked."""
    monkeypatch.setenv("CCC_OVERRIDE_OPTIONS", "+-std=gnu++23")
    monkeypatch.delenv("CCACHE_DISABLE", raising=False)
    monkeypatch.delenv("CLANG_NO_DEFAULT_CONFIG", raising=False)
    printer = tmp_path / "clang++-printer"
    _ = printer.write_text(
        "#!/bin/sh\n"
        + 'echo "${CCACHE_DISABLE-unset} ${CLANG_NO_DEFAULT_CONFIG-unset}'
        + ' ${CCC_OVERRIDE_OPTIONS-unset} $(pwd)"\n',
        encoding="utf-8",
    )
    printer.chmod(0o755)
    directory = tmp_path / "tree"
    directory.mkdir()
    answer = ask_macros(CompileArg(str(printer)), GNU23, directory)
    assert answer.output == f"1 1 unset {directory}\n", answer


@pytest.mark.process("the standard a job names is clang's own reading of the command")
def test_an_override_variable_names_no_standard_for_the_command(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """``CCC_OVERRIDE_OPTIONS`` adding the standard does not make a command name it."""
    monkeypatch.setenv("CCC_OVERRIDE_OPTIONS", "+-std=gnu++23")
    compiler = shutil.which(COMPILER)
    assert compiler is not None, f"{COMPILER} is not on PATH"
    verdicts = off_standard([_clang_unit(tmp_path, CompileArg(compiler))], executor=DrivenExecutor)
    reason = Prose("the job names no standard, so the compiler's version decides it")
    assert verdicts.off == [Off(RelPath("cpp/src/unit.cpp"), reason)], verdicts


@pytest.mark.process("the standard a job names is clang's own reading of the command")
def test_a_compiler_named_relative_to_the_unit_s_directory_is_asked_there(tmp_path: Path) -> None:
    """A program the database names relative to its directory is run from that directory."""
    compiler = shutil.which(COMPILER)
    assert compiler is not None, f"{COMPILER} is not on PATH"
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "clang++").symlink_to(compiler)
    unit = _clang_unit(tmp_path, CompileArg("bin/clang++"), STANDARD)
    assert off_standard([unit], executor=DrivenExecutor) == Verdicts([], [])


@pytest.mark.process("the standard a job names is clang's own reading of the command")
def test_a_job_list_split_by_a_quoted_newline_is_a_refused_command(tmp_path: Path) -> None:
    """An argument holding a newline splits the driver's job line: refused, not raised."""
    compiler = shutil.which(COMPILER)
    assert compiler is not None, f"{COMPILER} is not on PATH"
    unit = _clang_unit(tmp_path, CompileArg(compiler), STANDARD, CompileArg('-DX="a\nb"'))
    verdicts = off_standard([unit], executor=DrivenExecutor)
    ((source, reason),) = verdicts.refused
    assert source == RelPath("cpp/src/unit.cpp")
    assert reason.startswith("the driver's jobs cannot be read: "), reason


@pytest.mark.process("whether the system can start a compiler is the system's own answer")
def test_a_compiler_the_system_cannot_start_is_a_refused_command(tmp_path: Path) -> None:
    """A clang driver that is not there is refused, saying why, and raises nothing."""
    absent = CompileArg(str(tmp_path / "clang++-absent"))
    unit = Unit(A_CPP, UnitPath(str(tmp_path / "a.cpp")), tmp_path, [absent, STANDARD, COMPILE])
    verdicts = off_standard([unit], executor=DrivenExecutor)
    assert verdicts.off == []
    ((source, reason),) = verdicts.refused
    assert source == A_CPP
    assert "exit 127: " in reason, reason
    assert "clang++-absent" in reason, reason

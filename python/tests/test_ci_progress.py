# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools._ci_progress``: every step of the sweep declares how it reports its progress.

The table names exactly the steps the sweep registers, every lane on and every
tool found, no more and no fewer.  Each pattern reads the lines its tool
prints, taken from a sweep's step files, with the share of the work they say
is done, and passes over lines that are no count.
"""

from __future__ import annotations

import ast
import contextlib
import io
import itertools
import re
import shlex
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType

import pytest
from _ci_runner import ci_runner
from _processes import CommandWord

from tools import _ci_steps
from tools._ci_progress import ALLOWANCE_FLOOR, LONGEST_QUIET, STEP_PROGRESS
from tools._ci_steps import register_all_steps
from tools._common import GateName
from tools._progress import ItemCount, report
from tools._run_ci_options import OptInLanes
from tools._watchdog import Chunk, heard_line
from tools._workflow_steps import WATCHED

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from tools._scheduler import Step
    from tools._watchdog import Line, PatternText, Share

# A module of the tools package, named without the package.
ModuleName = NewType("ModuleName", str)

TOOLS = Path(__file__).resolve().parents[2] / "tools"


def test_the_table_names_every_step_the_sweep_registers_and_no_other(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With every lane on and every tool found, the registered steps are the table's."""
    registered = {GateName(step.name) for step in _registered(tmp_path, monkeypatch)}
    assert not registered - set(STEP_PROGRESS), registered - set(STEP_PROGRESS)
    assert not set(STEP_PROGRESS) - registered, set(STEP_PROGRESS) - registered


def _registered(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> list[Step]:
    """Return the steps the sweep registers with every lane on and every tool found."""
    (tmp_path / ".github" / "workflows").mkdir(parents=True)

    def found(name: CommandWord) -> CommandWord:
        return CommandWord(f"/usr/bin/{name}")

    monkeypatch.setattr(_ci_steps.shutil, "which", found)
    runner = ci_runner(tmp_path, python=CommandWord(sys.executable))
    runner.opts.lanes = OptInLanes(repro=True, stability=True, mutation=True, coverage=True)
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    return list(runner.registered_steps)


def _reports_through_the_helper(module: ModuleName) -> bool:
    """Answer whether ``tools/<module>.py`` imports the progress helper."""
    source = (TOOLS / f"{module}.py").read_text(encoding="utf-8")
    return any(
        isinstance(node, ast.ImportFrom) and node.module == "tools._progress"
        for node in ast.walk(ast.parse(source))
    )


def _our_line() -> Line:
    """Return a report our progress helper prints, as the watchdog hears it."""
    printed = io.StringIO()
    with contextlib.redirect_stderr(printed):
        report(ItemCount(1), ItemCount(2), Prose("files"))
    return heard_line(Chunk(printed.getvalue().encode()))


def _step_module(step: Step) -> ModuleName | None:
    """Return the tools module a sweep step runs with ``-m``, from its words or its shell line."""
    words = shlex.split(step.cmd) if isinstance(step.cmd, str) else list(step.cmd)
    return next(
        (
            ModuleName(module.removeprefix("tools."))
            for flag, module in itertools.pairwise(words)
            if flag == "-m" and module.startswith("tools.")
        ),
        None,
    )


def _watched_module(runs: PatternText) -> ModuleName | None:
    """Return the tools module a watched workflow step's pattern names."""
    found = re.search(r"-m tools\\\.(\w+)", runs)
    return None if found is None else ModuleName(found.group(1))


def test_every_step_declaring_our_reports_runs_a_tool_that_makes_them(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A step whose pattern reads our report line runs a tool importing the progress helper.

    Every step of the sweep and every watched step of the workflows, a pattern
    joined with other tools' and a step run as a shell line included.  A short
    tool ends inside the window the sweep gives a reporting step before it fails
    one that made no report, so a tool that stopped reporting is caught here
    rather than by a run.
    """
    ours = _our_line()
    reading = [
        (step.name, _step_module(step))
        for step in _registered(tmp_path, monkeypatch)
        if STEP_PROGRESS[GateName(step.name)].reports(ours)
    ] + [
        (step.runs, _watched_module(step.runs))
        for step in WATCHED
        if step.progress is not None and step.progress.reports(ours)
    ]
    unnamed = [name for name, module in reading if module is None]
    silent = [
        name
        for name, module in reading
        if module is not None and not _reports_through_the_helper(module)
    ]
    assert not unnamed, unnamed
    assert not silent, silent


@pytest.mark.parametrize(
    ("step", "line", "share"),
    [
        ("pytest", "tests/test_agda_open_grammar.py ........................ [ 42%]", 0.42),
        ("ctest", " 2/18 Test  #2: rational_runtime_refused .......   Passed    0.91 sec", 2 / 18),
        ("ubsan ctest", "[ 50%] Built target miniz", 0.5),
        ("cpp build", "[ 98%] Built target Demo9", 0.98),
        ("clang-tidy", "[ 26/104][5.5s] clang-tidy-23 -p=build-tidy -quiet cpp/tests/x.cpp", 0.25),
        ("agda gates", "[16/64]   1.5s OK   Aletheia/Parser/Properties.agda", 0.25),
        ("build", "[ 136 of 544] Compiling MAlonzo.Code.Aletheia.Main", 0.25),
        ("build", "# agda (for build/MAlonzo/Code/Aletheia/Main.hs)", None),
        (
            "build",
            "Checking Aletheia.Main (/home/runner/work/aletheia/aletheia/src/Aletheia/Main.agda).",
            None,
        ),
        ("go test -race", "ok  \tgithub.com/Jaetan/aletheia/go/v5/aletheia\t40.265s", None),
        ("cargo test", "test frame::tests::refuses_a_long_payload ... ok", None),
        ("cargo test", "running 182 tests", None),
        ("cargo clippy", "    Checking aletheia v5.0.0 (/x/rust)", None),
        ("iwyu", "progress: 3/12 modules", 0.25),
        ("mutation testing", "⠦ 922/3688  🎉 922 🫥 0  ⏰ 0  🤔 0  🙁 0  🔇 0  🧙 0", 0.25),
        ("mutation testing", "       [########------------------------] 19/76. 7ms", 0.25),
        ("mutation testing", "      KILLED INVERT_BITWISE at client.go:68:7", None),
        (
            "mutation testing",
            "caught   src/types.rs:198:51: replace / with % in Rational::reduced"
            + " in 0s build + 1s test",
            None,
        ),
        ("mutation testing", "ok       Unmutated baseline in 8s build + 5s test", None),
        ("mutation testing", "progress: 1/4 bindings", 0.25),
        (
            "mutation testing",
            "[ 72%] Building CXX object CMakeFiles/aletheia-cpp.dir/src/json_parse.cpp.o",
            0.72,
        ),
        (
            "check-cpp-slices-census-build",
            "[ 72%] Building CXX object CMakeFiles/aletheia-cpp.dir/src/property_check.cpp.o",
            0.72,
        ),
        ("coverage python", "tests/test_x.py ........................... [ 25%]", 0.25),
        ("coverage go", "progress: 1/4 bindings", 0.25),
        (
            "coverage go",
            "ok  \tgithub.com/Jaetan/aletheia/go/v5/aletheia\t22.517s"
            + "\tcoverage: 94.8% of statements",
            None,
        ),
        ("coverage cpp", "progress: 1/4 bindings", 0.25),
        (
            "coverage cpp",
            " 2/18 Test  #2: rational_runtime_refused ..........   Passed    1.85 sec",
            2 / 18,
        ),
        ("coverage rust", "test frame::tests::refuses_a_long_payload ... ok", None),
    ],
)
def test_each_pattern_reads_the_count_its_tool_prints(
    step: GateName, line: Line, share: Share | None
) -> None:
    """The line is a report of the step, and says the share of the work done where it counts."""
    progress = STEP_PROGRESS[step]
    assert progress.reports(heard_line(Chunk(line.encode())))
    found = progress.share(heard_line(Chunk(line.encode())))
    assert found == (None if share is None else pytest.approx(share))


@pytest.mark.parametrize(
    ("step", "line"),
    [
        ("pytest", "======================== 3 passed in 1.21s ========================"),
        ("ctest", "100% tests passed, 0 tests failed out of 18"),
        ("clang-tidy", "warning: 3 issues found [readability]"),
        ("iwyu", "iwyu gate: whole tree - 338 file(s)"),
        ("go test -race", "PASS"),
        ("ruff", "All checks passed!"),
        ("mutation testing", "Found 90 mutants to test"),
    ],
)
def test_a_line_that_is_no_count_is_no_report(step: GateName, line: Line) -> None:
    """A summary, a warning or a silent tool's verdict moves no deadline."""
    assert not STEP_PROGRESS[step].reports(heard_line(Chunk(line.encode())))


def test_every_step_has_an_allowance_no_shorter_than_the_floor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each registered step is stopped once it goes its allowance without a report, never sooner."""
    short = [
        step.name
        for step in _registered(tmp_path, monkeypatch)
        if (allowance := STEP_PROGRESS[GateName(step.name)].allowance) is None
        or allowance < ALLOWANCE_FLOOR
    ]
    assert not short, short


def test_every_measured_stretch_names_a_step_and_sets_its_allowance() -> None:
    """A measurement is of a declared step, and that step's allowance is five times it."""
    assert set(LONGEST_QUIET) <= set(STEP_PROGRESS)
    for name, quiet in LONGEST_QUIET.items():
        assert STEP_PROGRESS[name].allowance == max(ALLOWANCE_FLOOR, 5 * quiet), name

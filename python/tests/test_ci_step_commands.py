# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The commands of the sweep's lint and build steps, read off the registered steps.

A step's command can register, run and pass while doing less than its name
says: a linter handed no file exits zero, a listing taken from the wrong
directory misses sources, a build leaves its executable in the tree.  Each
test here runs the registered command over a scratch tree, where the verdict
is the tool's own, or holds the command to the words its claim rests on; and
the command a document prints for a step is held to the step's.
"""

from __future__ import annotations

import os
import re
import shlex
import shutil
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _ci_runner import ci_runner
from _cli_check_helpers import CliRun
from _git_repo import git
from _processes import CommandWord

from tools._ci_steps import (
    CPP_COMPILERS,
    DOC_EXAMPLE_DOCS,
    DOC_EXAMPLE_PACKAGE,
    GO_BUILD_NO_CGO,
    in_every_go_module,
    register_all_steps,
)
from tools._common import (
    CPP_LINT_LANE,
    CPP_LINT_TREE,
    GateName,
    RelPath,
    find_executable,
    git_clean_env,
    git_ls_files,
    run_capture,
)
from tools._markdown import code_blocks
from tools._resources import cpu_budget
from tools.run_ci import LaneName, OptInLanes

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from tools._scheduler import Step

# A command line as a shell reads it.
ShellLine = NewType("ShellLine", str)

# The checkout this suite is part of: the configurations a scratch tree copies
# and the document the doc-example command is read from.
_REPO = Path(__file__).resolve().parents[2]


def _registered_steps(tmp_path: Path, *, lanes: OptInLanes | None = None) -> tuple[Step, ...]:
    """Return the sweep's steps, registered over ``tmp_path`` with the suite's Python.

    The suite's interpreter sits beside the venv's pinned linters, so a lint
    step names the binary the sweep runs.  ``lanes`` turns opt-in lanes on, for
    the steps that read them from the runner as for those that read them from
    the options handed over.
    """
    runner = ci_runner(tmp_path, python=CommandWord(sys.executable))
    if lanes is not None:
        runner.opts.lanes = lanes
    register_all_steps(runner, ["cabal", "run", "shake", "--"], runner.opts)
    return runner.registered_steps


def _registered_step(tmp_path: Path, name: GateName) -> Step:
    """Return the sweep's step ``name``, registered over ``tmp_path``."""
    (step,) = (entry for entry in _registered_steps(tmp_path) if entry.name == name)
    return step


def _run_in(tree: Path, step: Step) -> CliRun:
    """Run ``step``'s shell command from ``tree``, the root the sweep runs it from.

    Git runs clear of the variables a hook exports, so the command lists the
    scratch tree's index rather than the hook's.
    """
    assert isinstance(step.cmd, str)
    assert step.cwd is None, f"{step.name} runs from {step.cwd}, not the root"
    result = run_capture([find_executable("sh"), "-c", step.cmd], cwd=tree, env=git_clean_env())
    return CliRun(ExitStatus(result.returncode), Prose(result.stdout), Prose(result.stderr))


_THE_INDEX_AND_THE_TOOL_ANSWER = (
    "which files the index lists is git's answer, and the verdict the tool's own"
    + " under the step's argv and the tree's configuration"
)


@pytest.mark.process(_THE_INDEX_AND_THE_TOOL_ANSWER)
def test_the_cmake_gate_scans_each_file_git_lists_and_fails_a_violation(tmp_path: Path) -> None:
    """The cmake-lint step scans a nested CMakeLists.txt the index lists, and fails it when wrong.

    The configuration option takes one or more values, so a command without
    the ``--`` after it hands the file paths to that option: the tool scans
    nothing, prints ``files scanned: 0`` and exits zero, a gate that cannot
    fail.  The scratch tree reads the repository's ``.cmake-format.yaml``.
    """
    step = _registered_step(tmp_path, GateName("cmake-lint"))
    _ = shutil.copy(_REPO / ".cmake-format.yaml", tmp_path)
    nested = tmp_path / "sub" / "CMakeLists.txt"
    nested.parent.mkdir()
    _ = git(tmp_path, "init", "-q")
    head = "cmake_minimum_required(VERSION 3.25)\nif(TRUE)\n"
    _ = nested.write_text(f"{head}    set(VALUE 1)\nendif()\n", encoding="utf-8")
    _ = git(tmp_path, "add", "sub/CMakeLists.txt")
    clean = _run_in(tmp_path, step)
    assert clean.returncode == 0, clean
    assert "files scanned: 1" in clean.stdout, clean
    _ = nested.write_text(f"{head}  set(VALUE 1)\nendif()\n", encoding="utf-8")
    _ = git(tmp_path, "add", "sub/CMakeLists.txt")
    wrong = _run_in(tmp_path, step)
    assert wrong.returncode != 0, wrong
    assert "files scanned: 1" in wrong.stdout, wrong


@pytest.mark.process(_THE_INDEX_AND_THE_TOOL_ANSWER)
def test_the_format_gate_checks_every_tracked_source_in_the_binding_s_style(
    tmp_path: Path,
) -> None:
    """The clang-format step reads every source the index lists, in and out of cpp/, in its style.

    Each tracked source is indented as ``cpp/.clang-format`` says and not as
    the tool's default style does, and the one outside the binding has no
    configuration above it, so the step passes them only when it names that
    style.  A mis-formatted file the index does not list, as a build tree's
    generated source, passes only while the listing is git's; each tracked
    source written mis-formatted fails the step.
    """
    step = _registered_step(tmp_path, GateName("clang-format"))
    (tmp_path / "cpp" / "build").mkdir(parents=True)
    (tmp_path / "cpp" / "src").mkdir()
    (tmp_path / "tools").mkdir()
    _ = shutil.copy(_REPO / "cpp" / ".clang-format", tmp_path / "cpp")
    generated = tmp_path / "cpp" / "build" / "generated.cpp"
    _ = generated.write_text("int   generated( ){return 2;}\n", encoding="utf-8")
    sources = (RelPath("cpp/src/inside.cpp"), RelPath("tools/consumer.cpp"))
    _ = git(tmp_path, "init", "-q")

    def staged_with(mis_formatted: RelPath | None) -> CliRun:
        for source in sources:
            body = "int answer() {\n    return 1;\n}\n"
            if source == mis_formatted:
                body = "int   answer( ){return 1;}\n"
            _ = (tmp_path / source).write_text(body, encoding="utf-8")
        _ = git(tmp_path, "add", *sources)
        return _run_in(tmp_path, step)

    conforming = staged_with(None)
    assert conforming.returncode == 0, conforming
    for source in sources:
        assert staged_with(source).returncode != 0, f"{source} mis-formatted passes"


@pytest.mark.process("which C++ sources the repository tracks is git's own answer")
def test_the_tree_tracks_cpp_sources_outside_the_binding_and_none_it_ignores() -> None:
    """The format gate's listing has sources outside cpp/ to reach, and none where builds write.

    The step runs from the root, and names cpp/'s style, for the tracked C++
    sources outside the binding.  A tracked source the ignore rules match,
    the rules that keep the build trees out of the index, is one a listing of
    the index cannot leave out.
    """
    tracked = git_ls_files(_REPO, "*.cpp", "*.hpp")
    assert [rel for rel in tracked if not rel.startswith("cpp/")], "no C++ source outside cpp/"
    ignored = git(
        _REPO, "ls-files", "--cached", "--ignored", "--exclude-standard", "--", "*.cpp", "*.hpp"
    )
    assert not ignored, f"tracked C++ sources the ignore rules match:\n{ignored}"


def test_the_cgo_free_build_keeps_no_executable(tmp_path: Path) -> None:
    """The cgo-free build of every module sends what it links to ``/dev/null``.

    ``go build ./...`` over a module holding one main package, the command
    line, writes that executable into the module's directory, so a plain build
    leaves a binary in the tree on every sweep.  The command is read rather
    than run, since running it compiles the workspace; test_run_ci_runner.py
    runs its loop.
    """
    step = _registered_step(tmp_path, GateName("go build (no cgo)"))
    assert step.cmd == in_every_go_module(GO_BUILD_NO_CGO)
    words = shlex.split(GO_BUILD_NO_CGO)
    assert words[words.index("build") + 1 : words.index("./...")] == ["-o", "/dev/null"]


# Every opt-in lane, so the steps read are every step the sweep registers on
# this machine for a tree holding workflows; a step registered only where a tool
# this machine lacks is installed is outside what the test reads.
_EVERY_LANE = OptInLanes(repro=True, stability=True, mutation=True, coverage=True)

# The C++ trees the test build and the clang-tidy gate configure, under cpp/.
_TEST_BUILD, _LINT_TREE = RelPath("build"), RelPath(CPP_LINT_TREE)


class HeldStep(NamedTuple):
    """A step allowed to name either tree, held whole: its command, its directory and its lane."""

    command: ShellLine | list[CommandWord]
    cwd: Path
    lane: LaneName


def _held_steps(repo: Path) -> dict[GateName, HeldStep]:
    """Return the steps allowed to name either tree, each held whole.

    The two that configure the trees delete the tree's cache, then run one
    configure line, the same for both but for the tree, and go on to what each
    does with its tree.  A step that comes to need either tree is added here,
    whole, not let through the rule: every later change to it then fails the
    test first, so the rule relaxes one reviewed command at a time.  What a held
    step's own text does to a tree is read by that review, not by the test.
    """

    def configured(tree: RelPath) -> ShellLine:
        return ShellLine(
            f"rm -f {tree}/CMakeCache.txt && cmake -B {tree} {CPP_COMPILERS} > /dev/null"
        )

    lib = shlex.quote(str(repo / "build" / "libaletheia-ffi.so"))
    return {
        GateName("ctest"): HeldStep(
            ShellLine(
                f"{configured(_TEST_BUILD)} && cmake --build {_TEST_BUILD}"
                + f" && ALETHEIA_LIB={lib} ctest --test-dir {_TEST_BUILD}"
            ),
            repo / "cpp",
            LaneName("cpp"),
        ),
        GateName("clang-tidy"): HeldStep(
            ShellLine(
                f"{configured(_LINT_TREE)}"
                + f" && run-clang-tidy-23 -j {cpu_budget()} -quiet -p {_LINT_TREE}"
                + " cpp/src/ cpp/tests/ cpp/benchmarks/"
            ),
            repo / "cpp",
            LaneName(CPP_LINT_LANE),
        ),
    }


def _words(step: Step) -> list[CommandWord]:
    """Return a step's words: an argv as it is, a shell line split as the shell splits it."""
    if not isinstance(step.cmd, str):
        return [CommandWord(word) for word in step.cmd]
    lexer = shlex.shlex(step.cmd, posix=True, punctuation_chars=True)
    lexer.whitespace_split = True
    return [CommandWord(word) for word in lexer]


def _reaches(step: Step, tree: Path) -> bool:
    """Say whether ``step`` runs inside ``tree`` or names a path into it.

    A word is read whole, after its first ``=``, and past a short option joined
    to it, each against the step's directory, so ``build``, ``-Bbuild``,
    ``--test-dir=build``, ``../cpp/build/CMakeCache.txt`` and an absolute path
    all reach cpp/build from cpp/.  A tree reached through a variable, a
    command substitution, a glob, a ``cd`` or ``env -C`` inside the command, or
    a script the step runs is outside what this reads.
    """
    cwd = step.cwd or tree.parents[1]
    if cwd.is_relative_to(tree):
        return True
    for word in _words(step):
        readings = {word, word.partition("=")[2]}
        if word.startswith("-") and not word.startswith("--"):
            readings.add(CommandWord(word[2:]))
        for reading in readings - {""}:
            if Path(os.path.normpath(cwd / reading)).is_relative_to(tree):
                return True
    return False


def test_the_lint_tree_is_configured_as_the_test_build_is(tmp_path: Path) -> None:
    """The clang-tidy gate's tree and the test build's are configured by one line, the tree aside.

    The gate reads cpp/build-tidy's compile database, configured and never
    built, so that it need not wait for the test build, and that database names
    what the test build compiles only while the two trees are configured alike.
    The two steps that configure them are held whole, as text, so an option
    given one tree alone, another compiler for one, or a further command on
    either tree fails, and so does a rewording the shell would run alike; and
    no other step, in any lane, runs inside either tree or names a path into it
    as ``_reaches`` reads its command.  A step that comes to need either tree
    joins the held steps, whole.
    """
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    steps = _registered_steps(tmp_path, lanes=_EVERY_LANE)
    held = _held_steps(tmp_path)
    assert _TEST_BUILD != _LINT_TREE
    assert set(held) <= {step.name for step in steps}
    trees = [tmp_path / "cpp" / _TEST_BUILD, tmp_path / "cpp" / _LINT_TREE]
    for step in steps:
        whole = held.get(GateName(step.name))
        if whole is not None:
            assert (step.cmd, step.cwd, step.lane) == whole, (step.name, step.cmd, step.cwd)
            continue
        for tree in trees:
            assert not _reaches(step, tree), (step.name, tree, step.cmd)


def test_the_coverage_guard_runs_after_clang_tidy_in_its_lane(tmp_path: Path) -> None:
    """The guard reads the database the clang-tidy step configures, so it follows it in its lane.

    Steps run in registration order within a lane, so a guard registered
    before the step, or in another lane, could read the tree before it is
    configured.
    """
    steps = _registered_steps(tmp_path)
    names = [step.name for step in steps]
    tidy, guard = (names.index(name) for name in ("clang-tidy", "check-clang-tidy-coverage"))
    assert tidy < guard, names
    assert steps[tidy].lane == steps[guard].lane == CPP_LINT_LANE


# The doc-example command AGENTS/python.md prints, its continuation lines
# joined: run from the root, with the step's options, over the step's list and package.
_DOCUMENTED_DOC_EXAMPLE_COMMAND = re.compile(
    r'cd "\$\(git rev-parse --show-toplevel\)" && python3 -m pytest --markdown-docs '
    + r'--rootdir="\$\(pwd\)" -o pythonpath=python/tests '
    + r"""\$\(python3 -c 'from tools\._ci_steps import DOC_EXAMPLE_DOCS, DOC_EXAMPLE_PACKAGE; """
    + r"""print\(\*DOC_EXAMPLE_DOCS, DOC_EXAMPLE_PACKAGE, sep="\\n"\)'\)"""
)
_DOC_EXAMPLE_OPENING = 'cd "$(git rev-parse --show-toplevel)" && python3 -m pytest --markdown-docs'


def _documented_doc_example_command() -> ShellLine:
    """Return the doc-example command of AGENTS/python.md, its continuation lines joined."""
    text = Prose((_REPO / "AGENTS" / "python.md").read_text(encoding="utf-8"))
    (block,) = (code for code in code_blocks(text) if _DOC_EXAMPLE_OPENING in code)
    lines = block.splitlines()
    first = next(n for n, line in enumerate(lines) if line.startswith(_DOC_EXAMPLE_OPENING))
    parts: list[ShellLine] = []
    for line in lines[first:]:
        parts.append(ShellLine(line.strip().removesuffix("\\").strip()))
        if not line.endswith("\\"):
            break
    return ShellLine(" ".join(parts))


def test_the_documented_doc_example_command_runs_what_the_step_runs(tmp_path: Path) -> None:
    """AGENTS/python.md's doc-example command and the step run one command over the harness list.

    Both run pytest's Markdown collection from the root, with the root and the
    path the repository-root conftest needs, over the documents the list names
    and the package whose docstrings it reads, and nothing else, so the two
    collect the same fences.  A command naming a subset of the documents, an
    option one carries and the other does not, a directory given beside them,
    or no package runs other fences than the step runs and the structural tests
    read.
    """
    command = _documented_doc_example_command()
    assert _DOCUMENTED_DOC_EXAMPLE_COMMAND.fullmatch(command), command
    step = _registered_step(tmp_path, GateName("pytest --markdown-docs"))
    assert list(step.cmd)[1:] == [
        "-m",
        "pytest",
        "--markdown-docs",
        "--rootdir",
        str(tmp_path),
        "-o",
        "pythonpath=python/tests",
        *(str(doc) for doc in DOC_EXAMPLE_DOCS),
        str(DOC_EXAMPLE_PACKAGE),
    ]
    assert step.cwd == tmp_path

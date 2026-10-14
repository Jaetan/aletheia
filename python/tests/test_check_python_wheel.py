# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_python_wheel``, the gate that builds the binding's wheel afresh.

The binding is staged from the pathspecs the dist rule stages it with, as the
index holds the files; the wheel is built offline with this Python's
setuptools; it holds when its ``.dist-info`` carries ``licenses/LICENSE.md``
equal to the binding's ``LICENSE.md``.  The command line answers 0, 1 or 2 as
its docstring says.  Only the staging test starts a process, git's.
"""

from __future__ import annotations

import io
import subprocess
import sys
import zipfile
from pathlib import Path
from typing import Literal, NamedTuple, NewType

import pytest
from _processes import CommandWord

from tools._common import find_executable, read_shake_program
from tools.bundle_licences import LicenceText
from tools.check_python_wheel import (
    FOUND,
    HELD,
    UNCHECKED,
    Built,
    Pathspec,
    TrackedPath,
    WheelUncheckedError,
    binding_pathspecs,
    build_wheel,
    main,
    stage_binding,
    wheel_findings,
)

from aletheia.common_types import ExitStatus, Prose

# A wheel member's path, and what the member holds.
Member = NewType("Member", str)
MemberData = NewType("MemberData", bytes)
# A wheel's file name without its ``.whl``.
WheelStem = NewType("WheelStem", str)
type Members = dict[Member, MemberData]

_REPO = Path(__file__).resolve().parents[2]
_LICENCE = LicenceText(b"Copyright (c) 2025, Nicolas Pelletier\nBSD-2-Clause\n")
_INFO = "aletheia-5.0.0.dist-info"
_CARRIED: Members = {Member(f"{_INFO}/licenses/LICENSE.md"): MemberData(_LICENCE)}
_METADATA_ONLY: Members = {Member(f"{_INFO}/METADATA"): MemberData(b"x")}


class _Ran(NamedTuple):
    """What one run of the command line did: its status and what it wrote."""

    status: ExitStatus
    said: list[Prose]


def _wheel(
    out: Path, members: Members, stem: WheelStem = WheelStem("aletheia-5.0.0-py3-none-any")
) -> Path:
    """Write a wheel holding ``members`` into ``out``; return it."""
    out.mkdir(parents=True, exist_ok=True)
    path = out / f"{stem}.whl"
    with zipfile.ZipFile(path, "w") as wheel:
        for member, data in members.items():
            wheel.writestr(member, data)
    return path


# binding_pathspecs


def test_binding_pathspecs_are_the_dist_rules_for_the_python_binding() -> None:
    """The build program's ``stageBinding "python"`` names the binding's files and its licence."""
    pathspecs = binding_pathspecs(Prose(read_shake_program(_REPO)))
    assert Pathspec("python/LICENSE.md") in pathspecs
    assert Pathspec("python/pyproject.toml") in pathspecs
    assert all(spec.removeprefix(":(exclude)").startswith("python/") for spec in pathspecs)


# stage_binding


def _git(repo: Path, *words: CommandWord) -> None:
    """Run git in ``repo`` with a fixed identity, raising when it fails."""
    command = [find_executable("git"), "-c", "user.email=t@t", "-c", "user.name=t", *words]
    _ = subprocess.run(command, cwd=repo, check=True, capture_output=True)


@pytest.mark.process("git's own index decides which files are tracked and what they hold")
def test_stage_binding_writes_the_tracked_files_as_the_index_holds_them(tmp_path: Path) -> None:
    """A staged edit is written as staged; a later unstaged edit and an untracked file are not."""
    repo = tmp_path / "repo"
    (repo / "python" / "aletheia").mkdir(parents=True)
    _ = (repo / "python" / "pyproject.toml").write_text("staged\n", encoding="utf-8")
    _ = (repo / "python" / "aletheia" / "__init__.py").write_text("", encoding="utf-8")
    _git(repo, CommandWord("init"), CommandWord("-q"))
    _git(repo, CommandWord("add"), CommandWord("python"))
    _ = (repo / "python" / "pyproject.toml").write_text("unstaged\n", encoding="utf-8")
    _ = (repo / "python" / "LICENSE.md").write_text("untracked\n", encoding="utf-8")
    into = tmp_path / "into"
    pathspecs = [Pathspec("python/pyproject.toml"), Pathspec("python/aletheia")]
    assert stage_binding(repo, pathspecs, into) == [
        TrackedPath("python/aletheia/__init__.py"),
        TrackedPath("python/pyproject.toml"),
    ]
    assert (into / "python" / "pyproject.toml").read_text(encoding="utf-8") == "staged\n"
    assert not (into / "python" / "LICENSE.md").exists()


type Answer = subprocess.CompletedProcess[Prose]


def _answering(monkeypatch: pytest.MonkeyPatch, answers: list[Answer]) -> list[list[CommandWord]]:
    """Answer each command the module runs with the next of ``answers``; return the commands."""
    asked: list[list[CommandWord]] = []

    def answer(cmd: list[CommandWord], *, cwd: Path | None = None) -> Answer:
        """Record ``cmd`` and return the next answer."""
        del cwd
        asked.append(cmd)
        return answers[len(asked) - 1]

    monkeypatch.setattr("tools.check_python_wheel.run_capture", answer)
    return asked


_SILENT = Prose("")


def _done(status: ExitStatus, out: Prose = _SILENT, err: Prose = _SILENT) -> Answer:
    """Return a finished process with ``status`` and its two streams."""
    return subprocess.CompletedProcess([], status, out, err)


@pytest.mark.parametrize(
    ("answers", "reason"),
    [
        (
            [_done(ExitStatus(128), err=Prose("fatal: not a git repository\n"))],
            Prose("git ls-files cannot read the index: fatal: not a git repository"),
        ),
        (
            [_done(ExitStatus(0))],
            Prose("the binding's pathspecs ['python/x'] name no tracked file"),
        ),
        (
            [
                _done(ExitStatus(0), out=Prose("python/x\0")),
                _done(ExitStatus(128), err=Prose("fatal: broken index\n")),
            ],
            Prose("git checkout-index cannot write the binding: fatal: broken index"),
        ),
    ],
)
def test_stage_binding_refuses_what_it_cannot_stage(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, answers: list[Answer], reason: Prose
) -> None:
    """A git that fails, or pathspecs naming nothing, leaves the binding unstaged."""
    _ = _answering(monkeypatch, answers)
    with pytest.raises(WheelUncheckedError) as refused:
        _ = stage_binding(tmp_path, [Pathspec("python/x")], tmp_path / "into")
    assert str(refused.value) == reason


# build_wheel


def test_build_wheel_asks_pip_for_an_offline_build_with_this_python(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """No isolation, no dependencies, no index, no cache; pip's status and streams are kept."""
    answers = [
        _done(ExitStatus(0), out=Prose("built\n"), err=Prose("warned\n")),
        _done(ExitStatus(1), err=Prose("refused\n")),
    ]
    asked = _answering(monkeypatch, answers)
    source, out = tmp_path / "src", tmp_path / "out"
    assert build_wheel(source, out) == Built(ok=True, said=Prose("built\nwarned\n"))
    assert build_wheel(source, out) == Built(ok=False, said=Prose("refused\n"))
    command = asked[0]
    assert command[:4] == [sys.executable, "-m", "pip", "wheel"]
    assert sorted(command[4:-3]) == [
        "--check-build-dependencies",
        "--no-build-isolation",
        "--no-cache-dir",
        "--no-deps",
        "--no-index",
    ]
    assert command[-3:] == ["--wheel-dir", str(out), str(source)]


# wheel_findings


def test_wheel_findings_holds_a_wheel_carrying_the_licence(tmp_path: Path) -> None:
    """One wheel whose .dist-info carries licenses/LICENSE.md equal to the binding's holds."""
    _ = _wheel(tmp_path, _CARRIED | _METADATA_ONLY)
    assert not wheel_findings(tmp_path, _LICENCE)


@pytest.mark.parametrize(
    "members",
    [
        _METADATA_ONLY,
        {Member("aletheia/licenses/LICENSE.md"): MemberData(_LICENCE)},
        {Member(f"{_INFO}/licenses/sub/LICENSE.md"): MemberData(_LICENCE)},
        {Member(f"{_INFO}/LICENSE.md"): MemberData(_LICENCE)},
    ],
)
def test_wheel_findings_names_a_wheel_without_the_licence(tmp_path: Path, members: Members) -> None:
    """A licence elsewhere than .dist-info/licenses/LICENSE.md, or none, is not carried."""
    _ = _wheel(tmp_path, members)
    assert wheel_findings(tmp_path, _LICENCE) == [
        Prose("aletheia-5.0.0-py3-none-any.whl: its .dist-info carries no licenses/LICENSE.md")
    ]


@pytest.mark.parametrize("licence", [LicenceText(b"Copyright MIT\n"), None])
def test_wheel_findings_names_a_licence_not_the_bindings(
    tmp_path: Path, licence: LicenceText | None
) -> None:
    """A carried licence other than the binding's, or a binding without one, is a finding."""
    _ = _wheel(tmp_path, _CARRIED)
    assert wheel_findings(tmp_path, licence) == [
        Prose("aletheia-5.0.0-py3-none-any.whl: its licenses/LICENSE.md is not python/LICENSE.md")
    ]


@pytest.mark.parametrize("count", [0, 2])
def test_wheel_findings_needs_exactly_one_wheel(tmp_path: Path, count: Literal[0, 2]) -> None:
    """No wheel, or more than one, is a finding naming how many."""
    for index in range(count):
        _ = _wheel(tmp_path, _CARRIED, WheelStem(f"aletheia-{index}"))
    assert wheel_findings(tmp_path, _LICENCE) == [Prose(f"the build left {count} wheels, not one")]


# main


def _run(
    monkeypatch: pytest.MonkeyPatch, built: Built, members: Members, *, licence: bool = True
) -> _Ran:
    """Run the command line with staging and the build stood in; return what it did."""
    said: list[Prose] = []

    def stage(repo: Path, pathspecs: list[Pathspec], into: Path) -> list[TrackedPath]:
        """Write the binding's licence under ``into``, as staging the index would."""
        assert repo == _REPO
        assert Pathspec("python/LICENSE.md") in pathspecs
        (into / "python").mkdir(parents=True)
        if licence:
            _ = (into / "python" / "LICENSE.md").write_bytes(_LICENCE)
        return [TrackedPath("python/LICENSE.md")]

    def build(source: Path, out: Path) -> Built:
        """Leave a wheel holding ``members`` in ``out`` when the build succeeds."""
        assert source.name == "python"
        if built.ok:
            _ = _wheel(out, members)
        return built

    monkeypatch.setattr("tools.check_python_wheel.stage_binding", stage)
    monkeypatch.setattr("tools.check_python_wheel.build_wheel", build)
    monkeypatch.setattr("tools.check_python_wheel.emit", said.append)
    monkeypatch.setattr("sys.argv", ["check_python_wheel"])
    return _Ran(main(), said)


_BUILT = Built(ok=True, said=Prose(""))


def test_main_holds_a_binding_whose_wheel_carries_its_licence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A wheel that builds and carries the binding's licence exits 0, saying so."""
    assert _run(monkeypatch, _BUILT, _CARRIED) == _Ran(
        HELD,
        [Prose("python-wheel: the binding builds offline and its wheel carries python/LICENSE.md")],
    )


def test_main_reports_a_binding_that_does_not_build(monkeypatch: pytest.MonkeyPatch) -> None:
    """A build pip refuses exits 1 with every line pip said."""
    refused = Built(ok=False, said=Prose("error: invalid\nInvalidConfigError: classifiers\n"))
    assert _run(monkeypatch, refused, {}) == _Ran(
        FOUND,
        [
            Prose("python-wheel: the binding does not build; pip says:"),
            Prose("  error: invalid"),
            Prose("  InvalidConfigError: classifiers"),
        ],
    )


def test_main_reports_a_wheel_without_the_bindings_licence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A wheel built without the licence, or a binding staged without one, exits 1."""
    wheel = "aletheia-5.0.0-py3-none-any.whl"
    assert _run(monkeypatch, _BUILT, _METADATA_ONLY) == _Ran(
        FOUND,
        [Prose(f"python-wheel: {wheel}: its .dist-info carries no licenses/LICENSE.md")],
    )


def test_main_reports_a_binding_staged_without_its_licence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A binding whose pathspecs stage no LICENSE.md cannot have its wheel's licence equal it."""
    wheel = "aletheia-5.0.0-py3-none-any.whl"
    assert _run(monkeypatch, _BUILT, _CARRIED, licence=False) == _Ran(
        FOUND,
        [Prose(f"python-wheel: {wheel}: its licenses/LICENSE.md is not python/LICENSE.md")],
    )


def test_main_is_unchecked_without_setuptools(monkeypatch: pytest.MonkeyPatch) -> None:
    """A Python without setuptools cannot build the wheel offline: exit 2, naming the fix."""
    said: list[Prose] = []
    asked: list[Prose] = []

    def find_spec(name: Prose) -> None:
        """Answer that no module ``name`` is installed."""
        asked.append(name)

    monkeypatch.setattr("tools.check_python_wheel.importlib.util.find_spec", find_spec)
    monkeypatch.setattr("tools.check_python_wheel.emit", said.append)
    monkeypatch.setattr("sys.argv", ["check_python_wheel"])
    assert _Ran(main(), said) == _Ran(
        UNCHECKED,
        [
            Prose(
                "python-wheel: this Python has no setuptools (the venv's [dev] extras carry it); "
                + "the wheel is unbuilt"
            )
        ],
    )
    assert asked == [Prose("setuptools")]


def test_main_is_unchecked_when_the_binding_cannot_be_staged(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A staging git refuses exits 2 with its reason, never a pass."""
    said: list[Prose] = []

    def stage(repo: Path, pathspecs: list[Pathspec], into: Path) -> list[TrackedPath]:
        """Refuse, as a git that cannot read the index would."""
        del repo, pathspecs, into
        message = "git ls-files cannot read the index: fatal"
        raise WheelUncheckedError(message)

    monkeypatch.setattr("tools.check_python_wheel.stage_binding", stage)
    monkeypatch.setattr("tools.check_python_wheel.emit", said.append)
    monkeypatch.setattr("sys.argv", ["check_python_wheel"])
    assert _Ran(main(), said) == _Ran(
        UNCHECKED,
        [Prose("python-wheel: git ls-files cannot read the index: fatal; the wheel is unbuilt")],
    )


def test_main_refuses_an_argument(monkeypatch: pytest.MonkeyPatch) -> None:
    """The gate takes no argument; one given is refused."""
    monkeypatch.setattr("sys.argv", ["check_python_wheel", "--all"])
    monkeypatch.setattr("sys.stderr", io.StringIO())
    with pytest.raises(SystemExit) as refused:
        _ = main()
    assert refused.value.code == ExitStatus(2)


def test_the_exit_statuses_are_the_ones_the_usage_states() -> None:
    """Held, found and unchecked exit 0, 1 and 2, as the module's usage says."""
    assert (ExitStatus(0), ExitStatus(1), ExitStatus(2)) == (HELD, FOUND, UNCHECKED)

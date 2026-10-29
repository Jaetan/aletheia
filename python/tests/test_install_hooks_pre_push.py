# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the pre-push hook ``tools/install_hooks.py`` renders does with a push.

It allows a push once a sweep of each pushed tree passed, asking the evidence
tool first and sweeping only when none is on record.
"""

from __future__ import annotations

import importlib.util
import io
import subprocess
import sys
import types
from enum import Enum
from typing import TYPE_CHECKING, NamedTuple, NewType, cast

import pytest
from _hook_runs import GitDone, GitOutput, HookRun, ToolDone, ToolOutput, TopLevel, run_main

from tools.install_hooks import PRE_PUSH_BODY

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from _processes import CommandWord

    from aletheia.common_types import ExitStatus


class Evidence(Enum):
    """What the evidence tool answers when the hook asks about the pushed commits."""

    RECORDED = "a sweep of the pushed tree is on record before the push"
    AFTER_SWEEP = "the hook's own sweep records the pushed tree"
    NEVER = "no sweep ever records the pushed tree, as for a dirty working tree"


# The ref lines git hands a pre-push hook on stdin, a file the hook runs, and
# the commits one question to the evidence tool named.
RefLines = NewType("RefLines", str)
ToolFile = NewType("ToolFile", str)
Question = NewType("Question", str)


class PushedHook(NamedTuple):
    """A pre-push hook loaded with its tools faked, and what they were asked."""

    main: Callable[[], ExitStatus]
    asked: list[Question]
    sweeps: list[list[CommandWord]]


def _load_pre_push(tmp_path: Path) -> types.ModuleType:
    """Import the rendered pre-push body as a module and return it.

    The body guards ``main`` behind ``__main__``, so importing it runs nothing
    and yields a module whose names a test can patch.
    """
    script = tmp_path / "pre_push.py"
    script.write_text(PRE_PUSH_BODY, encoding="utf-8")
    spec = importlib.util.spec_from_file_location("aletheia_pre_push_under_test", script)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _faked_push(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, evidence: Evidence) -> PushedHook:
    """Load the pre-push hook with git and its two tools answered in-process.

    The hook's own ``subprocess`` name is patched: git names ``tmp_path`` as
    the work tree's root, the evidence tool answers as ``evidence`` says and
    writes down, one question per entry, the commits it was asked about, and
    the sweep passes and writes down that it ran. The tool files are planted
    empty because the hook looks for each before it runs anything.
    """
    hook = _load_pre_push(tmp_path)
    (tmp_path / "tools").mkdir()
    for tool in ("__init__.py", "run_ci.py", "sweep_evidence.py"):
        (tmp_path / "tools" / tool).write_text("", encoding="utf-8")
    asked: list[Question] = []
    sweeps: list[list[CommandWord]] = []

    def fake_run(
        args: list[CommandWord],
        *,
        cwd: TopLevel | None = None,
        capture_output: bool = False,
        text: bool = False,
        check: bool = False,
    ) -> GitDone | ToolDone:
        del cwd, capture_output, text, check
        if args == ["git", "rev-parse", "--show-toplevel"]:
            return subprocess.CompletedProcess(
                args, 0, GitOutput(str(tmp_path) + "\n"), GitOutput("")
            )
        if args[1:3] == ["-m", "tools.sweep_evidence"]:
            asked.append(Question(" ".join(args[3:])))
            recorded = evidence is Evidence.RECORDED or (
                evidence is Evidence.AFTER_SWEEP and bool(sweeps)
            )
            return subprocess.CompletedProcess(
                args, int(not recorded), ToolOutput(""), ToolOutput("")
            )
        assert args[1:4] == ["-m", "tools.run_ci", "--parallel"], args
        sweeps.append(args)
        return subprocess.CompletedProcess(args, 0, ToolOutput(""), ToolOutput(""))

    monkeypatch.setattr(hook, "subprocess", types.SimpleNamespace(run=fake_run))
    return PushedHook(cast("Callable[[], ExitStatus]", hook.main), asked, sweeps)


def _push(faked: PushedHook, refs: RefLines, monkeypatch: pytest.MonkeyPatch) -> HookRun:
    """Run the faked hook's ``main`` as git would, with ``refs`` on its stdin."""
    monkeypatch.setattr(sys, "stdin", io.StringIO(refs))
    return run_main(faked.main)


_PUSHED = "a" * 40
_OTHER = "b" * 40
_REFS = RefLines(
    "".join(
        [
            f"refs/heads/b {_PUSHED} refs/heads/b {'0' * 40}\n",
            f"refs/tags/t {_OTHER} refs/tags/t {'0' * 40}\n",
        ]
    )
)


def test_pre_push_allows_at_once_a_push_whose_trees_passed_a_recorded_sweep(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """With every pushed ref's tree on record, the push goes without a sweep."""
    faked = _faked_push(tmp_path, monkeypatch, Evidence.RECORDED)
    done = _push(faked, _REFS, monkeypatch)
    assert done.returncode == 0, done.stderr
    assert faked.asked == [f"{_PUSHED} {_OTHER}"]
    assert not faked.sweeps
    assert "push allowed" in done.stderr


def test_pre_push_sweeps_then_allows_once_its_sweep_records_the_pushed_tree(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tree no sweep covers makes the hook sweep, then ask again before it allows."""
    faked = _faked_push(tmp_path, monkeypatch, Evidence.AFTER_SWEEP)
    done = _push(faked, _REFS, monkeypatch)
    assert done.returncode == 0, done.stderr
    assert len(faked.sweeps) == 1
    assert faked.asked == [f"{_PUSHED} {_OTHER}"] * 2
    assert "push allowed" in done.stderr


def test_pre_push_refuses_when_its_sweep_passed_on_another_tree(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A passing sweep of a working tree that is not the pushed one allows nothing."""
    faked = _faked_push(tmp_path, monkeypatch, Evidence.NEVER)
    done = _push(faked, _REFS, monkeypatch)
    assert done.returncode == 1, done.stderr
    assert len(faked.sweeps) == 1
    assert len(faked.asked) == 2
    assert "push refused" in done.stderr


def test_pre_push_allows_a_deletion_which_pushes_no_commit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A ref line whose local id is all zeros deletes a remote ref and needs no sweep."""
    faked = _faked_push(tmp_path, monkeypatch, Evidence.NEVER)
    done = _push(faked, RefLines(f"(delete) {'0' * 40} refs/heads/b {_PUSHED}\n"), monkeypatch)
    assert done.returncode == 0, done.stderr
    assert not faked.asked
    assert not faked.sweeps


@pytest.mark.parametrize("tool", [ToolFile("run_ci.py"), ToolFile("sweep_evidence.py")])
def test_pre_push_refuses_when_a_tool_it_runs_is_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, tool: ToolFile
) -> None:
    """Without the sweep or its evidence the hook cannot vouch for the push, so it refuses."""
    faked = _faked_push(tmp_path, monkeypatch, Evidence.RECORDED)
    (tmp_path / "tools" / tool).unlink()
    done = _push(faked, _REFS, monkeypatch)
    assert done.returncode == 1, done.stderr
    assert f"{tool} not found" in done.stderr
    assert not faked.asked
    assert not faked.sweeps

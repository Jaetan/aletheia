# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go and Rust lanes' kept sweeps: what a lane's sweep is keyed on, and how it is kept.

A lane sweeps a scratch copy of the tracked tree, with the kernel library and
the stand-in kernels its tests load from the tree, under a toolchain found on
the search path and the variables the tools and the tests read.  Each of
those has to move the key, or a sweep of one tree is served for another; and
what the sweep cannot read, an untracked file or a variable no tool reads,
has to leave it, or no sweep is ever served.  The tools are stand-ins on a
search path that holds them alone, so no tool of the host decides a key.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NewType

import pytest
from _git_repo import git
from _sweep_cache_tree import LIBRARY, UNMUTATED, change_file, fake_tree

import tools.mutation_sweep_cache as sweep_cache

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools.mutation_sweep_cache import LaneKind

# What a stand-in tool says of itself, and its name; and what a test changes
# under a lane's key.
_ToolText = NewType("_ToolText", str)
_ToolName = NewType("_ToolName", str)
_Move = Literal[
    "a tracked file",
    "the library",
    "a stand-in appearing",
    "a tool's word",
    "a tool rebuilt saying the same",
    "a tool missing",
    "the locale",
    "a stage variable",
    "a toolchain variable",
]


@pytest.fixture(name="tree")
def _tree(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Fake the repository under a scratch root."""
    return fake_tree(tmp_path, monkeypatch)


# What each stand-in tool on the lane tests' search path says of itself.
_TOOL_SAYS = {
    "go": "go version go0.0 fake",
    "gremlins": "gremlins version 0.0.0",
    "rustc": "rustc 0.0.0 (fake)",
    "cargo": "cargo 0.0.0 (fake)",
}


def _tool(directory: Path, name: _ToolName, says: _ToolText) -> None:
    """Install a stand-in tool that says what the file beside it holds, as a toolchain proxy does.

    The word lives apart from the tool's bytes, so each can change alone: a
    proxy's bytes stay put while the toolchain it selects says another version.
    """
    word = directory / f"{name}.says"
    _ = word.write_text(f"{says}\n", encoding="utf-8")
    path = directory / name
    # Builtins only: the search path the tools run under holds the stand-ins alone.
    _ = path.write_text(f"#!/bin/sh\nread -r line < '{word}'\necho \"$line\"\n", encoding="utf-8")
    path.chmod(0o755)


@pytest.fixture(name="lane_tree")
def _lane_tree(tree: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Put the fake repository under git, every file of it tracked, its lanes' tools stand-ins.

    The search path holds the stand-ins and nothing else, so no tool of the
    host decides a key, and every variable a lane's key reads is cleared.
    """
    for kind in ("go", "rust"):
        (tree / kind).mkdir()
    _ = git(tree, "init", "-q")
    _ = git(tree, "add", "-A")
    tools = tree.parent / "bin"
    tools.mkdir()
    for name, says in _TOOL_SAYS.items():
        _tool(tools, _ToolName(name), _ToolText(says))
    monkeypatch.setenv("PATH", str(tools))
    for name in list(os.environ):
        if sweep_cache.LANE_VARIABLES.fullmatch(name):
            monkeypatch.delenv(name)
    return tree


_LANE_KINDS: tuple[LaneKind, ...] = ("go", "rust")


@pytest.mark.parametrize("kind", _LANE_KINDS)
@pytest.mark.parametrize(
    "move",
    [
        "a tracked file",
        "the library",
        "a stand-in appearing",
        "a tool's word",
        "a tool rebuilt saying the same",
        "a tool missing",
        "the locale",
        "a stage variable",
        "a toolchain variable",
    ],
)
def test_every_input_of_a_lane_sweep_moves_its_key(
    lane_tree: Path, kind: LaneKind, move: _Move, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The tracked tree, what the tests load, the tools and the variables they read each move it."""
    before = sweep_cache.lane_sweep_key(kind)
    tools = lane_tree.parent / "bin"
    tool = _ToolName("gremlins" if kind == "go" else "rustc")
    if move == "a tracked file":
        change_file(lane_tree / UNMUTATED, "rewritten")
    elif move == "the library":
        change_file(lane_tree / LIBRARY, "rewritten")
    elif move == "a stand-in appearing":
        change_file(lane_tree / sweep_cache.STAND_IN_DIR / "another_kernel.so", "created")
    elif move == "a tool's word":
        _ = (tools / f"{tool}.says").write_text("another version\n", encoding="utf-8")
    elif move == "a tool rebuilt saying the same":
        _ = (tools / tool).write_text(
            (tools / tool).read_text(encoding="utf-8") + "# rebuilt\n", encoding="utf-8"
        )
    elif move == "a tool missing":
        (tools / tool).unlink()
    elif move == "the locale":
        monkeypatch.setenv("LC_ALL", "C")
    elif move == "a stage variable":
        monkeypatch.setenv("ALETHEIA_MUTATION_GO_STAGE", "1")
    else:
        monkeypatch.setenv("GOFLAGS" if kind == "go" else "RUSTFLAGS", "-x")
    assert sweep_cache.lane_sweep_key(kind) != before


@pytest.mark.parametrize("kind", _LANE_KINDS)
def test_what_a_lane_sweep_does_not_read_leaves_its_key(
    lane_tree: Path, kind: LaneKind, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An untracked file is not in the scratch copy, and a variable no tool reads is not read."""
    before = sweep_cache.lane_sweep_key(kind)
    change_file(lane_tree / "notes" / "untracked.txt", "created")
    monkeypatch.setenv("EDITOR", "vi")
    assert sweep_cache.lane_sweep_key(kind) == before


def _lane_reporting(
    swept: list[Path],
) -> Callable[[LaneKind, Path], Prose | None]:
    """Stand in for a lane's sweep that leaves the report its probe reads, recording where."""

    def sweep(kind: LaneKind, directory: Path) -> Prose | None:
        swept.append(directory)
        report = directory / sweep_cache.LANE_REPORT[kind]
        report.parent.mkdir(parents=True, exist_ok=True)
        _ = report.write_text("report", encoding="utf-8")

    return sweep


@pytest.mark.parametrize("kind", _LANE_KINDS)
def test_a_lane_sweep_is_served_until_the_tree_moves(
    lane_tree: Path, kind: LaneKind, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Served again without a sweep; once a tracked file moves, swept anew and the old one gone."""
    swept: list[Path] = []
    monkeypatch.setattr(sweep_cache, "_lane_sweep_into", _lane_reporting(swept))
    first = sweep_cache.lane_sweep_directory(kind)
    assert sweep_cache.lane_sweep_directory(kind) == first
    change_file(lane_tree / UNMUTATED, "rewritten")
    second = sweep_cache.lane_sweep_directory(kind)
    assert isinstance(second, Path)
    assert len(swept) == 2
    assert sorted(sweep_cache.CACHE_ROOT.iterdir()) == [second]


@pytest.mark.usefixtures("lane_tree")
def test_a_lane_sweep_that_stopped_is_not_kept(monkeypatch: pytest.MonkeyPatch) -> None:
    """A sweep that says why it stopped leaves nothing a later reader would serve."""
    stopped = Prose("gremlins not in PATH")

    def stop(_kind: LaneKind, _directory: Path) -> Prose | None:
        return stopped

    monkeypatch.setattr(sweep_cache, "_lane_sweep_into", stop)
    assert sweep_cache.lane_sweep_directory("go") == stopped
    assert not list(sweep_cache.CACHE_ROOT.iterdir())


@pytest.mark.usefixtures("lane_tree")
def test_a_tree_git_cannot_name_is_refused_before_any_sweep(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Without the tree's id nothing says what a sweep read, so none is run."""
    swept: list[Path] = []
    monkeypatch.setattr(sweep_cache, "_lane_sweep_into", _lane_reporting(swept))

    def nameless(_repo: Path) -> None:
        return None

    monkeypatch.setattr(sweep_cache, "tracked_tree", nameless)
    result = sweep_cache.lane_sweep_directory("rust")
    assert isinstance(result, str)
    assert "could not name the tracked tree" in result
    assert not swept

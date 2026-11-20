# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.check_reproducible_build``: three builds make one library; a build stops with the gate.

The gate builds over what the tree holds, then cleans and builds twice from
scratch, a run long enough to be killed in.  A build that outlived it would
keep Shake's lock, so the next build would fail on it.  The three libraries
must be one: two clean builds that differ fail, and so does a tree's build that
differs from two equal clean ones, the same sources giving other bytes after
another history.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, NamedTuple, NewType

import pytest
from _processes import CommandWord
from _stand_in import ScriptSource, driving_a_held_build, stopped

from tools import check_reproducible_build as gate

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path


@pytest.mark.process(
    "SIGKILL ends the gate without running any of its code, and only the kernel closing"
    + " the killed gate's pipe end shows the build stopping"
)
@pytest.mark.parametrize("target", [CommandWord("clean"), CommandWord("build")])
def test_a_killed_gate_stops_its_build(tmp_path: Path, target: CommandWord) -> None:
    """The gate killed in either run of a clean build, SIGKILL included, stops that run.

    The stand-in blocks in the run ``target`` names and lets the clean run
    pass when the build is the one named, so each run is the one killed in turn.
    """
    work = tmp_path / "work"
    work.mkdir()
    source = ScriptSource(
        "from pathlib import Path; "
        + "from tools.check_reproducible_build import _run_clean_build; "
        + f"_run_clean_build(1, Path({str(work)!r}), Path({str(work)!r}) / 'lib1.so')"
    )
    with driving_a_held_build(tmp_path, source, blocks_on=target) as build:
        build.driver.kill()
        _ = build.driver.wait()
        stopped(build.lock)


# Which of the two clean builds a run is, and the digest of the library it built.
BuildLabel = NewType("BuildLabel", int)
Digest = NewType("Digest", str)


def test_each_build_is_reported_as_it_ends(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The tree's build and the two clean builds report before the first and as each ends."""
    seen: list[Prose] = []

    def tree_built(_work_dir: Path, _copy_to: Path) -> Digest:
        seen.append(Prose(capsys.readouterr().err))
        return Digest("sha-tree")

    def built(label: BuildLabel, _work_dir: Path, _copy_to: Path) -> Digest:
        seen.append(Prose(capsys.readouterr().err))
        return Digest(f"sha-{label}")

    monkeypatch.setattr(gate, "_run_tree_build", tree_built)
    monkeypatch.setattr(gate, "_run_clean_build", built)
    assert gate.run_builds(tmp_path) == ("sha-tree", "sha-1", "sha-2")
    assert seen == ["progress: 0/3 builds\n", "progress: 1/3 builds\n", "progress: 2/3 builds\n"]
    assert capsys.readouterr().err == "progress: 3/3 builds\n"


# A scratch library's bytes.
_Library = NewType("_Library", bytes)


class _Judged(NamedTuple):
    """Three libraries' bytes, the gate's status on them, and a line it prints."""

    tree: _Library
    first: _Library
    second: _Library
    status: Literal[0, 1]
    said: Prose


_SAME = _Library(b"same")
_OTHER = _Library(b"other")


@pytest.mark.parametrize(
    "case",
    [
        _Judged(_SAME, _SAME, _SAME, 0, Prose("check-reproducible-build: ok")),
        _Judged(_SAME, _SAME, _OTHER, 1, Prose("is not bit-identical across two clean builds")),
        _Judged(
            _OTHER,
            _SAME,
            _SAME,
            1,
            Prose("the library the tree's own build left is not the one a clean build makes"),
        ),
    ],
    ids=["one library", "clean builds differ", "tree's build differs"],
)
def test_the_three_libraries_are_judged_as_one(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose], case: _Judged
) -> None:
    """Two clean builds must agree, and the tree's build must agree with them."""
    for label, content in enumerate(case[:3]):
        _ = (tmp_path / f"lib{label}.so").write_bytes(content)
    tree, first, second = (gate.LibraryDigest(content.decode()) for content in case[:3])
    assert gate.judge(tmp_path, (tree, first, second), keep=False) == case.status
    out = capsys.readouterr()
    assert case.said in out.out + out.err

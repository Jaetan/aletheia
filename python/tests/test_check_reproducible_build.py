# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.check_reproducible_build``: a build the gate starts stops when the gate dies.

The gate cleans and builds twice from scratch, a run long enough to be killed
in.  A build that outlived it would keep Shake's lock, so the next build would
fail on it.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType

import pytest
from _processes import CommandWord
from _stand_in import ScriptSource, driving_a_held_build, stopped

from tools import check_reproducible_build as gate

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.common_types import Prose


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


def test_each_clean_build_is_reported_as_it_ends(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The two builds report on stderr before the first and as each one ends."""

    def built(label: BuildLabel, _work_dir: Path, _copy_to: Path) -> Digest:
        return Digest(f"sha-{label}")

    monkeypatch.setattr(gate, "_run_clean_build", built)
    assert gate.run_two_builds(tmp_path) == ("sha-1", "sha-2")
    reports = [line for line in capsys.readouterr().err.splitlines() if line.startswith("progress")]
    assert reports == [f"progress: {done}/2 clean builds" for done in range(3)]

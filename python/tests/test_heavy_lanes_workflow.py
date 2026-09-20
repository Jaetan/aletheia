# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The heavy-lanes workflow carries the C++ mutation lane as two legs and a merge.

``.github/workflows/pr-heavy-lanes.yml`` sweeps each tree ``CPP_LANES`` names
in a lane of its own, uploads every lane's reports under a name the merge
job's download pattern reaches, and the required check reports the lanes and
the merge together.  A tree with no leg, a leg whose artifact the merge
cannot see, or a required check that reads only one of the two jobs would each
pass silently on the runner, so the wiring is held here.
"""

from __future__ import annotations

import fnmatch
from pathlib import Path
from typing import cast

import yaml

from tools.mutation_cpp import CPP_LANES, CPP_LEGS_ENV, CPP_STAGE_ENV, CppStage, lane_name

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-heavy-lanes.yml"
_LANE_JOB = "mutation-lane"
_MERGE_JOB = "mutation-cpp"
_REQUIRED_JOB = "mutation"
_REQUIRED_CHECK = "mutation testing"

type Step = dict[str, object]
type Job = dict[str, object]
type MatrixEntry = dict[str, str | int]


def _jobs() -> dict[str, Job]:
    workflow = cast("dict[str, object]", yaml.safe_load(_WORKFLOW.read_text(encoding="utf-8")))
    return cast("dict[str, Job]", workflow["jobs"])


def _matrix() -> list[MatrixEntry]:
    strategy = cast("dict[str, object]", _jobs()[_LANE_JOB]["strategy"])
    matrix = cast("dict[str, object]", strategy["matrix"])
    return cast("list[MatrixEntry]", matrix["include"])


def _steps(job: str) -> list[Step]:
    return cast("list[Step]", _jobs()[job]["steps"])


def _with(step: Step) -> dict[str, str]:
    return cast("dict[str, str]", step.get("with", {}))


def _env(step: Step) -> dict[str, str]:
    return cast("dict[str, str]", step.get("env", {}))


def _artifact_name(lane: str) -> str:
    """Read the name a lane's upload step gives its artifact, with the lane substituted."""
    uploads = [
        _with(step)["name"]
        for step in _steps(_LANE_JOB)
        if str(step.get("uses", "")).startswith("actions/upload-artifact@")
    ]
    assert len(uploads) == 1
    return uploads[0].replace("${{ matrix.lane }}", lane)


def test_every_tree_is_one_leg_and_no_lane_runs_the_whole_cpp_lane() -> None:
    """One matrix entry per tree, named by its stage, and no entry sweeps both trees."""
    entries = _matrix()
    assert len({str(entry["lane"]) for entry in entries}) == len(entries)
    for sanitizer, _ in CPP_LANES:
        stage = lane_name(sanitizer)
        legs = [entry for entry in entries if entry["binding"] == "cpp" and entry["stage"] == stage]
        assert len(legs) == 1, stage
        assert legs[0]["lane"] == f"cpp-{stage}"
        assert legs[0]["skip_cpp"] == ""
    for entry in entries:
        assert isinstance(entry["timeout"], int)
        if entry["binding"] != "cpp":
            assert entry["stage"] == ""
        else:
            assert entry["stage"] != ""


def test_the_sweep_step_hands_each_lane_its_stage() -> None:
    """The runner reads the stage from the environment the sweep step sets."""
    sweeps = [step for step in _steps(_LANE_JOB) if "tools.mutation_run" in str(step.get("run"))]
    assert len(sweeps) == 1
    assert _env(sweeps[0])[CPP_STAGE_ENV] == "${{ matrix.stage }}"


def test_the_merge_reads_every_leg_and_no_other_lane() -> None:
    """The download pattern reaches each leg's artifact and none of the other lanes'."""
    downloads = [
        step
        for step in _steps(_MERGE_JOB)
        if str(step.get("uses", "")).startswith("actions/download-artifact@")
    ]
    assert len(downloads) == 1
    pattern = _with(downloads[0])["pattern"]
    legs_dir = _with(downloads[0])["path"]
    for entry in _matrix():
        name = _artifact_name(str(entry["lane"]))
        assert fnmatch.fnmatchcase(name, pattern) == (entry["binding"] == "cpp"), name
    merges = [step for step in _steps(_MERGE_JOB) if "tools.mutation_run" in str(step.get("run"))]
    assert len(merges) == 1
    env = _env(merges[0])
    assert env[CPP_STAGE_ENV] == CppStage.MERGE.value
    assert env[CPP_LEGS_ENV] == legs_dir
    assert env["ALETHEIA_MUTATION_SKIP_PYTHON"] == "1"
    assert env["ALETHEIA_MUTATION_SKIP_GO"] == "1"


def test_the_merge_runs_whatever_the_lanes_did() -> None:
    """A Python or Go failure must not erase the C++ verdict, so the merge always runs."""
    merge = _jobs()[_MERGE_JOB]
    assert merge["needs"] == [_LANE_JOB]
    assert merge["if"] == "${{ always() }}"


def test_the_required_check_reads_the_lanes_and_the_merge() -> None:
    """The required context keeps its name, needs both jobs, and refuses either's non-success."""
    required = _jobs()[_REQUIRED_JOB]
    assert required["name"] == _REQUIRED_CHECK
    assert sorted(cast("list[str]", required["needs"])) == sorted([_LANE_JOB, _MERGE_JOB])
    assert required["if"] == "${{ always() }}"
    steps = _steps(_REQUIRED_JOB)
    assert len(steps) == 1
    env = _env(steps[0])
    assert env["LANES_RESULT"] == f"${{{{ needs.{_LANE_JOB}.result }}}}"
    assert env["CPP_RESULT"] == f"${{{{ needs.{_MERGE_JOB}.result }}}}"
    script = str(steps[0]["run"])
    assert '"${LANES_RESULT}" != "success"' in script
    assert '"${CPP_RESULT}" != "success"' in script

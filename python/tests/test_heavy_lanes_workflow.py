# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The heavy-lanes workflow carries the C++ legs and the Go shards, and one merge of both.

``.github/workflows/pr-heavy-lanes.yml`` gives every leg ``sliced_legs`` names
and every Go shard a lane of its own, uploads each one's reports under a name
the merge job's download patterns reach, and the required check reports the
lanes and the merge together.  A slice or a shard with no lane, a part whose
artifact the merge cannot see, or a required check that reads only one of the
two jobs would each pass silently on the runner, so the wiring is held here.
"""

from __future__ import annotations

import fnmatch
from pathlib import Path
from typing import cast

import yaml

from tools.mutation_cpp_legs import (
    CPP_LEGS_ENV,
    CPP_MERGE_STAGE,
    CPP_SLICE_ENV,
    CPP_STAGE_ENV,
    sliced_legs,
)
from tools.mutation_go import (
    GO_MERGE_STAGE,
    GO_SHARDS,
    GO_SHARDS_ENV,
    GO_STAGE_ENV,
    ShardNumber,
    shard_binding,
)
from tools.mutation_rust import (
    RUST_JOBS,
    RUST_JOBS_ENV,
    RUST_MERGE_STAGE,
    RUST_STAGE_ENV,
    RustJob,
    job_binding,
)

_WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-heavy-lanes.yml"
_LANE_JOB = "mutation-lane"
_MERGE_JOB = "mutation-merge"
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


def _is_ccache_cache(step: Step) -> bool:
    """Say whether a step restores or saves the C++ legs' compiler cache."""
    return str(step.get("uses", "")).startswith("actions/cache/") and "ccache" in str(
        _with(step).get("key", "")
    )


def _artifact_name(lane: str) -> str:
    """Read the name a lane's upload step gives its artifact, with the lane substituted."""
    uploads = [
        _with(step)["name"]
        for step in _steps(_LANE_JOB)
        if str(step.get("uses", "")).startswith("actions/upload-artifact@")
    ]
    assert len(uploads) == 1
    return uploads[0].replace("${{ matrix.lane }}", lane)


def test_every_slice_of_every_tree_is_one_leg_and_no_lane_sweeps_a_whole_tree() -> None:
    """One matrix entry per leg, named by its tree and slice, and no entry sweeps more."""
    entries = _matrix()
    assert len({str(entry["lane"]) for entry in entries}) == len(entries)
    cpp = [entry for entry in entries if entry["binding"] == "cpp"]
    assert len(cpp) == len(sliced_legs())
    for leg in sliced_legs():
        legs = [
            entry
            for entry in cpp
            if entry["stage"] == leg.tree.value and entry["slice"] == str(leg.slice_no)
        ]
        assert len(legs) == 1, str(leg)
        assert legs[0]["lane"] == leg.binding
        assert legs[0]["skip_cpp"] == ""
    for entry in entries:
        assert isinstance(entry["timeout"], int)
        if entry["binding"] != "cpp":
            assert entry["stage"] == ""
            assert entry["slice"] == ""
        else:
            assert entry["stage"] != ""
            assert entry["slice"] != ""


def test_every_go_shard_is_one_lane_and_no_lane_sweeps_the_package_whole() -> None:
    """One matrix entry per shard, named as the shard reports, and only Go lanes carry one."""
    entries = _matrix()
    go = [entry for entry in entries if entry["binding"] == "go"]
    assert [(entry["lane"], entry["go_shard"]) for entry in go] == [
        (shard_binding(ShardNumber(n)), str(n)) for n in range(1, GO_SHARDS + 1)
    ]
    for entry in go:
        assert entry["skip_go"] == ""
    for entry in entries:
        if entry["binding"] != "go":
            assert entry["go_shard"] == ""


def test_every_rust_job_is_one_lane_and_no_lane_sweeps_the_crate_whole() -> None:
    """One matrix entry per job, named as the job reports, and only Rust lanes carry one."""
    entries = _matrix()
    rust = [entry for entry in entries if entry["binding"] == "rust"]
    assert [(entry["lane"], entry["rust_job"]) for entry in rust] == [
        (job_binding(RustJob(n)), str(n)) for n in range(1, RUST_JOBS + 1)
    ]
    for entry in rust:
        assert entry["skip_rust"] == ""
    for entry in entries:
        if entry["binding"] != "rust":
            assert entry["rust_job"] == ""


def test_the_sweep_step_hands_each_lane_its_tree_and_its_slice() -> None:
    """The runner reads both from the environment the sweep step sets.

    Either one alone is a leg that sweeps something nobody asked for: the tree
    without the slice is the whole tree, six times over.
    """
    sweeps = [step for step in _steps(_LANE_JOB) if "tools.mutation_run" in str(step.get("run"))]
    assert len(sweeps) == 1
    assert _env(sweeps[0])[CPP_STAGE_ENV] == "${{ matrix.stage }}"
    assert _env(sweeps[0])[CPP_SLICE_ENV] == "${{ matrix.slice }}"
    assert _env(sweeps[0])[GO_STAGE_ENV] == "${{ matrix.go_shard }}"
    assert _env(sweeps[0])[RUST_STAGE_ENV] == "${{ matrix.rust_job }}"


def test_the_cpp_legs_keep_a_compiler_cache_of_their_own() -> None:
    """Nine legs build nine slices, and the build is only affordable cached.

    The cache is what the launcher's extra-files hashing makes safe, and
    nothing else here would notice its absence: without a directory, a key and
    a save, every leg compiles into a cache thrown away when the job ends, and
    every lane stays green while paying the cold build every run.  Per lane,
    because a lane's objects are its own.
    """
    steps = _steps(_LANE_JOB)
    setup = [step for step in steps if "CCACHE_MAXSIZE" in str(step.get("run", ""))]
    assert len(setup) == 1
    # Containment, not equality: the step reads the lane's diff scope as well,
    # since a lane that sweeps nothing installs nothing (tools/mutation_scope.py).
    assert "matrix.binding == 'cpp'" in str(setup[0]["if"])
    caches = [step for step in steps if _is_ccache_cache(step)]
    # One restore and one save, both the C++ lanes' alone.
    assert len(caches) == 2
    assert {str(step["uses"]).split("@", maxsplit=1)[0] for step in caches} == {
        "actions/cache/restore",
        "actions/cache/save",
    }
    for step in caches:
        assert "matrix.binding == 'cpp'" in str(step["if"])
        key = str(_with(step)["key"])
        assert "${{ matrix.lane }}" in key
        # The toolchain deb key, verbatim: hashing the compiler by content
        # does not reach the LLVM runtime beside it, and that key pins it.
        assert "clang23-llvm23dev-libstdcxx15-noble-v1" in key


def test_the_cpp_legs_save_only_the_cache_their_run_used() -> None:
    """A leg's saved compiler cache is the working set of the run that built it.

    One step right after the restore zeroes the counters and takes the run's
    start, before the sweep builds; the eviction script runs with that start
    after the sweep and before the save, under the save's own condition once
    the start was taken.  ccache refreshes an entry on a hit, so an entry older
    than the start is one the run never read, and the script reads this run's
    counters to keep the cache whole for a run that compiled nothing or failed
    a compile.  Counters carried from earlier runs, an eviction after the save
    or under a narrower condition, each leave the saved cache other than the
    run's working set.
    """
    steps = _steps(_LANE_JOB)
    caches = [i for i, step in enumerate(steps) if _is_ccache_cache(step)]
    starts = [
        i for i, step in enumerate(steps) if "MUTATION_CACHE_START=" in str(step.get("run", ""))
    ]
    sweeps = [
        i
        for i, step in enumerate(steps)
        if str(step.get("name", "")).startswith("Mutation testing")
    ]
    evictions = [
        i
        for i, step in enumerate(steps)
        if "tools/mutation_ccache_evict.sh" in str(step.get("run", ""))
    ]
    assert len(caches) == 2
    assert len(starts) == len(sweeps) == len(evictions) == 1
    restore, save = caches
    assert str(steps[restore]["uses"]).startswith("actions/cache/restore@")
    assert restore + 1 == starts[0] < sweeps[0] < evictions[0] < save
    start = steps[starts[0]]
    assert start["run"] == (
        'ccache --zero-stats\necho "MUTATION_CACHE_START=$(date +%s)" >> "${GITHUB_ENV}"\n'
    )
    assert start["if"] == steps[restore]["if"]
    eviction = steps[evictions[0]]
    assert eviction["run"] == 'tools/mutation_ccache_evict.sh "${MUTATION_CACHE_START}"'
    # The save's condition and the start's presence: a leg that swept and then
    # failed saves, so it evicts first, and a leg whose counters were never
    # zeroed saves its cache as restored.
    save_if = str(steps[save]["if"])
    assert save_if.endswith(" }}")
    assert eviction["if"] == save_if.removesuffix(" }}") + " && env.MUTATION_CACHE_START != '' }}"


def test_the_merge_reads_every_part_and_no_other_lane() -> None:
    """One download per binding reaches each of its parts' artifacts and no other lane's."""
    downloads = [
        step
        for step in _steps(_MERGE_JOB)
        if str(step.get("uses", "")).startswith("actions/download-artifact@")
    ]
    assert len(downloads) == 3
    reaching = {
        binding: [
            _with(step)["path"]
            for step in downloads
            if all(
                fnmatch.fnmatchcase(_artifact_name(str(entry["lane"])), _with(step)["pattern"])
                == (entry["binding"] == binding)
                for entry in _matrix()
            )
        ]
        for binding in ("cpp", "go", "rust")
    }
    assert all(len(found) == 1 for found in reaching.values()), reaching
    merges = [step for step in _steps(_MERGE_JOB) if "tools.mutation_run" in str(step.get("run"))]
    assert len(merges) == 1
    env = _env(merges[0])
    assert env[CPP_STAGE_ENV] == CPP_MERGE_STAGE
    assert env[CPP_LEGS_ENV] == reaching["cpp"][0]
    assert env[GO_STAGE_ENV] == GO_MERGE_STAGE
    assert env[GO_SHARDS_ENV] == reaching["go"][0]
    assert env[RUST_STAGE_ENV] == RUST_MERGE_STAGE
    assert env[RUST_JOBS_ENV] == reaching["rust"][0]
    assert env["ALETHEIA_MUTATION_SKIP_PYTHON"] == "1"
    assert "ALETHEIA_MUTATION_SKIP_GO" not in env
    assert "ALETHEIA_MUTATION_SKIP_CPP" not in env
    assert "ALETHEIA_MUTATION_SKIP_RUST" not in env


def test_the_merge_runs_whatever_the_lanes_did() -> None:
    """A Python or Rust failure must not erase the merged verdicts, so the merge always runs."""
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
    assert env["MERGE_RESULT"] == f"${{{{ needs.{_MERGE_JOB}.result }}}}"
    script = str(steps[0]["run"])
    assert '"${LANES_RESULT}" != "success"' in script
    assert '"${MERGE_RESULT}" != "success"' in script

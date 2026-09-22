# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A build-tree cache entry is saved only where there is a build tree.

A run that fails before the build leaves no tree, and a save then writes a
near-empty archive under that run's key.  The restore keys match by prefix,
newest first, so every later run finds that entry ahead of a real one,
restores nothing and rebuilds the kernel from scratch: measured 2026-09-21 at
about 1.4 kB against a built tree's 35 MB, and a 308-second rebuild in the job
that restored one, where a hit no-ops in 0.03s.  The workflows ask whether the
artifact the tree is for is there before they save it, and this holds them to
it, because the failure is silent on the runner that causes it and lands on
the next one.
"""

from __future__ import annotations

from pathlib import Path
from typing import cast

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

# What the presence step is called and what it reads, named once here because
# the test asserts both halves: the save waits on the step, and the step looks
# at the artifact rather than at some directory a failed run also leaves.
PRESENCE_ID = "build-tree-present"
PRESENCE_CONDITION = f"steps.{PRESENCE_ID}.outputs.present == 'true'"
# The presence step tests this file, rather than a directory a failed run also
# leaves behind: `dist-newstyle` exists after any cabal invocation, and a tree
# saved on the strength of it is the near-empty archive this guards against.
THE_TEST = "[ -f build/libaletheia-ffi.so ]"

# The gate that must not have a tree handed to it: it builds twice from clean
# and compares the two, so a restored tree is not a clean build and a lane that
# restored one would compare a cached artifact with itself.  Named by what it
# runs rather than by its job's name, which is the thing an edit renames.
THE_CLEAN_BUILD_GATE = "tools.check_reproducible_build"

type Step = dict[str, object]


def _jobs(path: Path) -> dict[str, dict[str, object]]:
    """Read one workflow's jobs."""
    document = cast("dict[str, object]", yaml.safe_load(path.read_text(encoding="utf-8")))
    return cast("dict[str, dict[str, object]]", document.get("jobs", {}))


def _steps(job: dict[str, object]) -> list[Step]:
    """Read one job's steps."""
    return cast("list[Step]", job.get("steps", []))


def _saves_the_build_tree(step: Step) -> bool:
    """Say whether a step saves a build-tree cache entry, by its key rather than its name."""
    uses = str(step.get("uses", ""))
    key = str(cast("dict[str, object]", step.get("with", {})).get("key", ""))
    return "actions/cache/save" in uses and key.startswith("build-tree-")


def _build_tree_saves() -> list[tuple[Path, str, Step, list[Step]]]:
    """Every build-tree save in every workflow, with the job's steps beside it."""
    found: list[tuple[Path, str, Step, list[Step]]] = []
    for path in sorted(WORKFLOWS.glob("*.yml")):
        for name, job in _jobs(path).items():
            steps = _steps(job)
            found.extend((path, name, step, steps) for step in steps if _saves_the_build_tree(step))
    return found


def test_the_workflows_still_save_a_build_tree() -> None:
    """There is something to hold: a workflow set that saved none would pass vacuously."""
    assert _build_tree_saves(), "no workflow saves a build-tree cache entry"


def test_every_build_tree_save_waits_on_a_tree_being_there() -> None:
    """Each save is conditioned on the presence step, which reads the artifact itself."""
    for path, job, step, steps in _build_tree_saves():
        where = f"{path.name}:{job}"
        condition = str(step.get("if", ""))
        assert PRESENCE_CONDITION in condition, (
            f"{where} saves a build tree without asking whether there is one"
        )
        presence = [entry for entry in steps if entry.get("id") == PRESENCE_ID]
        assert len(presence) == 1, f"{where} has {len(presence)} steps with id {PRESENCE_ID}"
        script = str(presence[0].get("run", ""))
        assert THE_TEST in script, (
            f"{where}'s presence step does not test {THE_TEST}, "
            "so a run that failed before the build could still call the tree present"
        )


def _restores_the_build_tree(step: Step) -> bool:
    """Say whether a step restores a build-tree cache entry, by its key."""
    uses = str(step.get("uses", ""))
    key = str(cast("dict[str, object]", step.get("with", {})).get("key", ""))
    return "actions/cache" in uses and key.startswith("build-tree-")


def test_the_clean_build_gate_is_handed_no_tree() -> None:
    """The lane that compares two clean builds restores no build tree.

    Its claim is that two builds of one source tree produce one artifact, and
    it reads that from the builds it runs itself.  A restored tree would make
    the first of them incremental, so the gate would compare a cached artifact
    against a rebuild of nothing and pass on both.
    """
    lanes = [
        (path, name, steps)
        for path in sorted(WORKFLOWS.glob("*.yml"))
        for name, job in _jobs(path).items()
        for steps in [_steps(job)]
        if any(THE_CLEAN_BUILD_GATE in str(step.get("run", "")) for step in steps)
    ]
    assert lanes, f"no job runs {THE_CLEAN_BUILD_GATE}"
    for path, name, steps in lanes:
        restores = [step for step in steps if _restores_the_build_tree(step)]
        assert not restores, (
            f"{path.name}:{name} runs the clean-build gate and restores a build tree, "
            "so the gate would compare a restored artifact with itself"
        )


# Where Agda writes interface files: under the project root, never beside the
# MAlonzo output in `build/`.  A tree cached without this directory hands the
# proof gate a cold closure on every run, since the proof-only modules reach no
# other cached artifact: measured 2026-09-22 on a docs-only pull request whose
# run restored a 35 MB tree, 831 s for the proof gate against 26 s warm.
THE_INTERFACE_DIR = "_build"

# The sweep that type-checks every module of the tree, proof-only ones
# included, so the interface directory it leaves behind is complete.  A build
# lane checks the runtime closure at most, and a cache key is immutable: were
# such a lane to save first, that commit's entry would lack the proof
# interfaces for good, and every later prefix match would inherit the gap.
THE_WHOLE_TREE_SWEEP = "tools.run_ci --iwyu-all"


def _build_tree_cache_steps() -> list[tuple[Path, str, Step]]:
    """Every build-tree restore and save in every workflow."""
    return [
        (path, name, step)
        for path in sorted(WORKFLOWS.glob("*.yml"))
        for name, job in _jobs(path).items()
        for step in _steps(job)
        if _restores_the_build_tree(step) or _saves_the_build_tree(step)
    ]


def _cached_paths(step: Step) -> list[str]:
    """Read the path list a cache step names, one entry per line."""
    raw = str(cast("dict[str, object]", step.get("with", {})).get("path", ""))
    return [line.strip() for line in raw.splitlines() if line.strip()]


def test_every_build_tree_cache_step_names_one_path_set_holding_the_interfaces() -> None:
    """One path set everywhere, and the interface directory is in it.

    The platform hashes the path list into an entry's version, so a restore
    listing a different set than the save misses however the key matches;
    and the set carries the interface directory, or the gate the tree exists
    to warm runs cold.
    """
    steps = _build_tree_cache_steps()
    assert steps, "no workflow caches a build tree"
    sets = {tuple(_cached_paths(step)) for _, _, step in steps}
    assert len(sets) == 1, f"the build-tree cache steps name {len(sets)} path sets: {sorted(sets)}"
    (paths,) = sets
    assert THE_INTERFACE_DIR in paths, (
        f"the build-tree cache omits {THE_INTERFACE_DIR}, where Agda writes its interfaces"
    )


def test_only_the_whole_tree_sweep_saves_the_build_tree() -> None:
    """Each saver's job runs the sweep that type-checks every module first."""
    for path, job, _, steps in _build_tree_saves():
        assert any(THE_WHOLE_TREE_SWEEP in str(step.get("run", "")) for step in steps), (
            f"{path.name}:{job} saves a build tree without running {THE_WHOLE_TREE_SWEEP}, "
            "so the interfaces it saves are at most the runtime closure's"
        )

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""GHC, the cabal store, pip and Mull are set up one way, keyed on what decides them.

A job that installs Agda sets up GHC and the cabal store, a job that installs
into the dev venv sets up Python, and a C++ mutation leg builds Mull; each
restores what an earlier run built.  A compiler restored anywhere but where
ghcup installs it leaves a restored kernel library unable to load its runtime,
a store saved without shake's dependencies is compiled into again by the next
job, a venv installed without pip's cache fetches every wheel, and a Mull key
that misses a patch replays binaries the tree no longer describes.  None of
these fails the job that causes it, so the tests hold the steps.
"""

from __future__ import annotations

import re
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, Literal, NamedTuple

from _workflows import (
    REPO_ROOT,
    CacheKey,
    CachePaths,
    DependencyPaths,
    GlobPattern,
    JobName,
    ShellText,
    StepIndex,
    ToolCache,
    TreePath,
    every_job,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable

    from _workflows import JobSteps, Step

# A job is one that installs Agda by what it runs, not by its name.
AGDA_INSTALL = ShellText('cabal install "Agda-${AGDA_VERSION}"')

# GHC's directory is ghcup's own, read from ghcup, exported for the cache steps
# and put on PATH: a kernel library restored from the build-tree cache names
# GHC's library directory in its RUNPATH.  Every job's setup ends with these
# lines and its install is this script, so both are held as text rather than
# read as shell: a branch around a line or an edit to one copy departs from it.
GHC_SETUP_TAIL = ShellText(
    'ghc_dir="$(ghcup whereis basedir)/ghc/${GHC_VERSION}"\n'
    + 'echo "GHC_DIR=${ghc_dir}" >> "${GITHUB_ENV}"\n'
    + "{\n"
    + '  echo "${HOME}/.cabal/bin"\n'
    + '  echo "${HOME}/.ghcup/bin"\n'
    + '  echo "${ghc_dir}/bin"\n'
    + '} >> "${GITHUB_PATH}"\n'
)
GHC_INSTALL_STEP = ShellText("ghcup install ghc")
GHC_INSTALL = ShellText(
    "set -euo pipefail\n"
    + 'ghcup install ghc "${GHC_VERSION}" --set\n'
    + 'installed="$(ghcup whereis --directory ghc "${GHC_VERSION}")"\n'
    + '[ "${installed}" = "${GHC_DIR}/bin" ] || {\n'
    + '  echo "::error::ghcup installed GHC at ${installed}, not under ${GHC_DIR},'
    + ' which the cache holds"\n'
    + "  exit 1\n"
    + "}\n"
)
GHC_DIR = CachePaths("${{ env.GHC_DIR }}")
GHC_KEY = CacheKey("ghc${{ env.GHC_VERSION }}-noble-v2")

# The store's key hashes shake.cabal, since the store is saved holding the
# shake executable's dependencies, and a restore falls back to the newest
# store under the key's prefix.
STORE_PREFIX = CacheKey(
    "cabal-${{ runner.os }}-ghc${{ env.GHC_VERSION }}-agda${{ env.AGDA_VERSION }}-"
)
STORE_KEY = CacheKey(STORE_PREFIX + "${{ hashFiles('shake.cabal') }}-v3")
SHAKE_DEPS = ShellText("cabal build --only-dependencies aletheia-build:exe:shake")
INDEX_REFRESH = ShellText("cabal update")

VENV_INSTALL = ShellText("python/.venv/bin/pip install")
PIP = ToolCache("pip")
PIP_DEPENDENCY_PATH = DependencyPaths("python/pyproject.toml")

MULL_BUILD = TreePath("tools/build_mull.sh")
# A patch the build script names, as its path under tools/.
MULL_PATCH = re.compile(r"mull/[A-Za-z0-9._-]+\.patch")
# A pattern hashFiles and PurePosixPath.full_match read alike: a plain relative
# path, a ``*`` matching within one segment.  An exclusion, a class, a brace, a
# space, a dot segment or a trailing separator, each read by @actions/glob its
# own way, falls outside it.
_SEGMENT = "[A-Za-z0-9_*-][A-Za-z0-9._*-]*"
_PLAIN_PATTERN = "'" + _SEGMENT + "(?:/" + _SEGMENT + ")*'"
# The Mull key: a literal prefix, then one hashFiles call of plain patterns.
MULL_KEY = re.compile(
    r"[A-Za-z0-9._-]+-\$\{\{\s*hashFiles\(\s*(?P<patterns>"
    + _PLAIN_PATTERN
    + r"(?:\s*,\s*"
    + _PLAIN_PATTERN
    + r")*)\s*\)\s*\}\}"
)
QUOTED = re.compile(r"'([^']+)'")
CACHE_MISSED = re.compile(r"steps\.([A-Za-z0-9_-]+)\.outputs\.cache-hit != 'true'")

type CacheAction = Literal["restore", "save"]


def _runs(text: ShellText) -> Callable[[Step], bool]:
    """Whether a step's script holds ``text``."""
    return lambda step: text in step.get("run", "")


def _where(steps: list[Step], found: Callable[[Step], bool]) -> list[StepIndex]:
    """Return the positions of the steps ``found`` holds for, in order."""
    return [StepIndex(i) for i, step in enumerate(steps) if found(step)]


def _one(positions: list[StepIndex], job: JobName, what: Prose) -> StepIndex:
    assert len(positions) == 1, f"{job} has {len(positions)} steps that {what}, where one is wanted"
    return positions[0]


def _jobs_running(text: ShellText) -> list[JobSteps]:
    """Every job with a step whose script holds ``text``."""
    return [job for job in every_job() if _where(job.steps, _runs(text))]


def _caches(kind: CacheAction, key_start: CacheKey) -> Callable[[Step], bool]:
    """Whether a step is an ``actions/cache/<kind>`` step whose key starts with ``key_start``."""

    def found(step: Step) -> bool:
        key = step.get("with", {}).get("key", "")
        return f"actions/cache/{kind}@" in step.get("uses", "") and key.startswith(key_start)

    return found


def _lines(run: ShellText) -> list[ShellText]:
    """Return a script's lines, stripped."""
    return [ShellText(line.strip()) for line in run.splitlines()]


def _ghc_setup(step: Step) -> bool:
    return step.get("run", "").endswith(GHC_SETUP_TAIL)


def _refreshes_index(step: Step) -> bool:
    return step.get("run", "").strip() == INDEX_REFRESH


def test_some_job_installs_agda() -> None:
    """There is something to hold: a workflow set with no such job would pass vacuously."""
    assert _jobs_running(AGDA_INSTALL), "no job installs Agda"


def test_every_agda_job_names_ghcs_directory_from_ghcup_once() -> None:
    """One step ends by reading GHC_DIR from ghcup, exporting it and putting its bin/ on PATH."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        what = Prose("name GHC's directory and put its bin/ on PATH")
        _ = _one(_where(steps, _ghc_setup), job, what)


def test_every_agda_job_restores_installs_and_saves_ghc_once_into_ghcups_layout() -> None:
    """GHC is restored, installed and saved once each, the install stopping off GHC_DIR.

    The install is the one script every job runs, which fails unless ghcup put
    GHC under GHC_DIR, and the step lets nothing continue past that failure.
    """
    for job, steps in _jobs_running(AGDA_INSTALL):
        install = steps[_one(_where(steps, _runs(GHC_INSTALL_STEP)), job, Prose("install GHC"))]
        assert install.get("run") == GHC_INSTALL, (
            f"{job}'s GHC install departs from the script every job runs"
        )
        assert "continue-on-error" not in install, f"{job} lets its GHC install fail and go on"
        _ = _one(_where(steps, _caches("restore", CacheKey("ghc"))), job, Prose("restore GHC"))
        _ = _one(_where(steps, _caches("save", CacheKey("ghc"))), job, Prose("save GHC"))


def test_every_ghc_cache_step_holds_ghcs_directory_under_one_key() -> None:
    """Restore and save name GHC_DIR and one key, the same in every job."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        for kind in ("restore", "save"):
            found = _where(steps, _caches(kind, CacheKey("ghc")))
            given = steps[_one(found, job, Prose(f"{kind} GHC"))].get("with", {})
            assert given.get("path") == GHC_DIR, f"{job} caches GHC at {given.get('path')}"
            assert given.get("key") == GHC_KEY, f"{job} keys its GHC {kind} as {given.get('key')}"


def test_every_ghc_install_and_save_runs_only_where_the_restore_missed() -> None:
    """Both wait on the restore's cache-hit, so a hit installs and saves nothing."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        found = _where(steps, _caches("restore", CacheKey("ghc")))
        restore = steps[_one(found, job, Prose("restore GHC"))]
        missed = f"steps.{restore.get('id')}.outputs.cache-hit != 'true'"
        waiting = (
            (_runs(GHC_INSTALL_STEP), Prose("install GHC")),
            (_caches("save", CacheKey("ghc")), Prose("save GHC")),
        )
        for waits, what in waiting:
            step = steps[_one(_where(steps, waits), job, what)]
            assert missed in step.get("if", ""), (
                f"{job}: step {step.get('name')!r} runs whatever the GHC restore found"
            )


def test_every_agda_job_sets_ghc_up_in_order_before_installing_agda() -> None:
    """GHC is named, restored, installed and saved, in that order, ahead of the Agda install."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        setup = _one(_where(steps, _ghc_setup), job, Prose("name GHC's directory"))
        restore = _one(
            _where(steps, _caches("restore", CacheKey("ghc"))), job, Prose("restore GHC")
        )
        install = _one(_where(steps, _runs(GHC_INSTALL_STEP)), job, Prose("install GHC"))
        save = _one(_where(steps, _caches("save", CacheKey("ghc"))), job, Prose("save GHC"))
        agda = _where(steps, _runs(AGDA_INSTALL))[0]
        assert setup < restore < install < save < agda, (
            f"{job} does not name, restore, install and save GHC in order before installing Agda"
        )


def _store_step(steps: list[Step], job: JobName, kind: CacheAction) -> StepIndex:
    return _one(_where(steps, _caches(kind, CacheKey("cabal-"))), job, Prose(f"{kind} the store"))


def test_every_store_cache_step_is_keyed_on_shake_cabal_and_restores_by_its_prefix() -> None:
    """One key in every job's restore and save, and the restore falls back to the key's prefix."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        restore = steps[_store_step(steps, job, "restore")].get("with", {})
        save = steps[_store_step(steps, job, "save")].get("with", {})
        for kind, given in (("restore", restore), ("save", save)):
            assert given.get("key") == STORE_KEY, (
                f"{job} keys its store {kind} as {given.get('key')}"
            )
        assert restore.get("restore-keys", "").strip() == STORE_PREFIX, (
            f"{job} restores no store under the key's prefix"
        )


def test_every_agda_job_saves_a_store_holding_shakes_dependencies() -> None:
    """The dependencies are built once, between the Agda install and the store's save."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        restore = _store_step(steps, job, "restore")
        save = _store_step(steps, job, "save")
        deps = _one(_where(steps, _runs(SHAKE_DEPS)), job, Prose("build shake's dependencies"))
        agda = _where(steps, _runs(AGDA_INSTALL))[0]
        assert restore < agda < deps < save, (
            f"{job} does not build shake's dependencies between the Agda install and the store save"
        )


def test_every_agda_job_refreshes_the_package_index_only_where_no_store_was_restored() -> None:
    """A restored store keeps the index its packages were resolved against."""
    for job, steps in _jobs_running(AGDA_INSTALL):
        restore = steps[_store_step(steps, job, "restore")]
        unmatched = f"steps.{restore.get('id')}.outputs.cache-matched-key == ''"
        refresh = steps[_one(_where(steps, _refreshes_index), job, Prose("refresh the index"))]
        assert unmatched in refresh.get("if", ""), (
            f"{job} refreshes the package index where a store was restored"
        )


def _python_with_pip_cache(step: Step) -> bool:
    given = step.get("with", {})
    return (
        "actions/setup-python@" in step.get("uses", "")
        and given.get("cache") == PIP
        and given.get("cache-dependency-path") == PIP_DEPENDENCY_PATH
    )


def test_some_job_installs_into_the_dev_venv() -> None:
    """There is something to hold: a workflow set with no such job would pass vacuously."""
    assert _jobs_running(VENV_INSTALL), "no job installs into the dev venv"


def test_every_dev_venv_install_has_pips_cache_set_up_ahead_of_it() -> None:
    """Python is set up with pip's cache, keyed on the package's pyproject, before any install."""
    for job, steps in _jobs_running(VENV_INSTALL):
        setups = _where(steps, _python_with_pip_cache)
        assert setups, f"{job} never sets Python up with pip's cache keyed on {PIP_DEPENDENCY_PATH}"
        assert setups[0] < _where(steps, _runs(VENV_INSTALL))[0], (
            f"{job} installs into the dev venv before setting Python up with pip's cache"
        )


class _MullBuild(NamedTuple):
    """A step that builds Mull, with its job's label and steps."""

    label: JobName
    build: Step
    steps: list[Step]


def _mull_builds() -> list[_MullBuild]:
    return [
        _MullBuild(job.label, step, job.steps)
        for job in every_job()
        for step in job.steps
        if MULL_BUILD in step.get("run", "")
    ]


def test_some_job_builds_mull() -> None:
    """There is something to hold: a workflow set with no Mull build would pass vacuously."""
    assert _mull_builds(), f"no job runs {MULL_BUILD}"


def _applied_patches(script: ShellText) -> list[TreePath]:
    """Return the patches under tools/mull/ the build script names outside its comments."""
    code = "\n".join(line for line in _lines(script) if not line.startswith("#"))
    return sorted({TreePath(f"tools/{name}") for name in MULL_PATCH.findall(code)})


def _hashed(path: TreePath, patterns: list[GlobPattern]) -> bool:
    """Whether ``hashFiles`` over ``patterns``, plain paths and ``*`` globs, hashes ``path``."""
    return any(PurePosixPath(path).full_match(pattern) for pattern in patterns)


def test_every_mull_build_runs_on_a_miss_of_a_key_hashing_the_script_and_its_patches() -> None:
    """An edited patch or script misses the cache, so the binaries are the tree's.

    The cache is the one whose miss the build waits on, and its key is one
    ``hashFiles`` call of plain patterns after a literal prefix: an expression
    around the call could carry a value the patterns do not decide, and a
    pattern past plain paths and ``*`` globs is one @actions/glob reads its own
    way.
    """
    patches = _applied_patches(ShellText((REPO_ROOT / MULL_BUILD).read_text(encoding="utf-8")))
    assert patches, f"{MULL_BUILD} applies no patch under tools/mull/"
    for patch in patches:
        assert (REPO_ROOT / patch).is_file(), (
            f"{MULL_BUILD} applies {patch}, which is not in the tree"
        )
    for job, build, steps in _mull_builds():
        gate = CACHE_MISSED.search(build.get("if", ""))
        assert gate, f"{job} builds Mull other than on a miss of a cache"
        caches = [step for step in steps if step.get("id") == gate.group(1)]
        assert len(caches) == 1, f"{job} has {len(caches)} steps with id {gate.group(1)}"
        key = caches[0].get("with", {}).get("key", "")
        shape = MULL_KEY.fullmatch(key)
        assert shape, (
            f"{job} keys the Mull cache other than as <prefix>-${{{{ hashFiles(<plain>, ...) }}}}"
            f": {key}"
        )
        patterns = [GlobPattern(pattern) for pattern in QUOTED.findall(shape.group("patterns"))]
        for path in (MULL_BUILD, *patches):
            assert _hashed(path, patterns), f"{job}'s Mull key does not hash {path}"

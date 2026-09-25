# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""One sweep of the C++ mutation trees, kept for every probe that reads it.

Several probes each state a claim about one sweep: that the recorded census is
what a sweep produces, that the recorded routes are, that every survivor and
every unobserved kill is a recorded one.  Written to sweep for themselves they
re-measure one run once per claim, which on three trees is over an hour of the
same work.  This runs the sweep once and keys it on what could change its
outcome, so the second reader pays nothing and each probe still runs alone.

The key is the content of every tree's test binary and the argv the lane
sweeps with.  A rebuild of any tree changes its binary and so the key; so does
a change to the runner's arguments, the pinned order among them.  Nothing else
decides what a sweep reads, the order being pinned and the cap explicit, which
is why the same key may be served rather than swept again.

The reports land under a directory named by that key, and a sweep writes into
a temporary neighbour that is renamed into place when every report is there:
a run interrupted halfway leaves no directory a later reader would trust.
"""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from tools._common import emit
from tools.mutation_cpp import CPP_LEG_REPORT_SUFFIXES, REPO_ROOT, cpp_lane_command, leg_config
from tools.mutation_cpp_legs import CppLeg, CppTree

# Where the sweeps are kept: inside the tree, beside the build trees the
# .gitignore already holds out, because a probe reads no path outside it.
CACHE_ROOT = REPO_ROOT / "cpp" / "mutation-sweeps"

# The runner the lane names. Read here rather than searched for, so a reader
# without it is told what is missing instead of sweeping with another one.
MULL_RUNNER = "mull-runner-23"

# Below this many cores there is no core to leave, so the sweep takes what
# there is.
_CORES_TO_SHARE = 2


def _polite(argv: list[str]) -> list[str]:
    """Run the sweep on every core but one, so the machine stays usable while it does.

    Mull decides its own worker count from the machine, and a sweep that takes
    every core makes the desktop it runs on unusable for the minutes it lasts.
    The affinity is set outside the runner rather than by an argument, because
    the argument is part of what the lane sweeps with and this is not: it
    changes when the mutants run, never which of them run or what each reads.
    A machine with one core, or without the tool, is left alone.
    """
    cores = os.cpu_count() or 1
    if cores < _CORES_TO_SHARE or shutil.which("taskset") is None:
        return argv
    return ["taskset", "-c", f"0-{cores - 2}", *argv]


def _binary(tree: CppTree) -> Path:
    """Name the test binary of one tree, which is what a sweep reads."""
    return REPO_ROOT / "cpp" / tree.directory / "unit_tests"


def _digest(path: Path) -> str:
    """Digest a file, read in blocks so a 100 MB binary costs no memory."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sweep_key() -> str:
    """Name what a sweep of today's trees would read: every binary, and the argv."""
    parts: list[str] = []
    for tree in CppTree:
        leg = CppLeg(tree)
        parts.append(f"{tree.value}:{_digest(_binary(tree))}")
        parts.append(" ".join(cpp_lane_command(MULL_RUNNER, Path(tree.directory), Path(), leg)))
    return hashlib.sha256("\n".join(parts).encode("utf-8")).hexdigest()[:16]


def _reports_present(directory: Path) -> bool:
    """Say whether the directory holds every report every tree's sweep writes."""
    return all(
        (directory / f"{CppLeg(tree).report_name}{suffix}").is_file()
        for tree in CppTree
        for suffix in CPP_LEG_REPORT_SUFFIXES
    )


def _sweep_into(directory: Path) -> str | None:
    """Sweep every tree into the directory, or say what stopped it.

    The environment is the lane's: the repository root, which the folded
    integration tests read, and the configuration each tree was built under,
    which the runner reads its own cap from.  ALETHEIA_LIB is dropped, since
    with it set the library lookup returns before it reads the root and the
    mutants of that read go uncovered.
    """
    for tree in CppTree:
        leg = CppLeg(tree)
        build_dir = REPO_ROOT / "cpp" / tree.directory
        env = os.environ | {
            "ALETHEIA_REPO_ROOT": str(REPO_ROOT),
            "MULL_CONFIG": str(leg_config(leg, build_dir)),
        }
        env.pop("ALETHEIA_LIB", None)
        # The runner exits non-zero whenever a mutant survives, which is a
        # property of the surface rather than of the sweep, so the reports are
        # what says whether it ran.
        _ = subprocess.run(
            _polite(cpp_lane_command(MULL_RUNNER, build_dir, directory, leg)),
            cwd=REPO_ROOT / "cpp",
            env=env,
            check=False,
            capture_output=True,
        )
        missing = [
            suffix
            for suffix in CPP_LEG_REPORT_SUFFIXES
            if not (directory / f"{leg.report_name}{suffix}").is_file()
        ]
        if missing:
            return f"the sweep of the {tree.value} tree wrote no {leg.report_name}{missing[0]}"
    return None


def sweep_directory(*, refresh: bool = False) -> Path | str:
    """Return the directory holding a sweep of today's trees, sweeping where there is none."""
    for tree in CppTree:
        if not os.access(_binary(tree), os.X_OK):
            return f"the {tree.value} mutation tree is not built"
    if shutil.which(MULL_RUNNER) is None:
        return f"{MULL_RUNNER} is not installed"
    wanted = CACHE_ROOT / sweep_key()
    if refresh and wanted.is_dir():
        shutil.rmtree(wanted)
    if _reports_present(wanted):
        return wanted
    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(dir=CACHE_ROOT, prefix="sweeping-"))
    failure = _sweep_into(staging)
    if failure is not None:
        shutil.rmtree(staging, ignore_errors=True)
        return failure
    if wanted.is_dir():
        shutil.rmtree(wanted)
    staging.rename(wanted)
    return wanted


def main(argv: list[str]) -> int:
    """Print the directory of a sweep of today's trees, or the reason there is none."""
    result = sweep_directory(refresh="--refresh" in argv)
    if isinstance(result, str):
        emit(result)
        return 1
    emit(str(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

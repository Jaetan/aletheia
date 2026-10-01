# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the C++ sweep spends on each file, counted in runs of the unmutated suite.

A tree's slices are cut on these.  A mutant's run, as Mull's SQLite report
records it, is divided by the leg's unmutated run, which Mull prints as its
baseline, so the figure counts suites' worth of work rather than the speed of
the runner the leg drew: one CI run's address legs ran the unmutated suite in
6.9 s on one runner and 13.9 s on another.  Each leg writes its own figures
beside its reports; the merge sums each tree's legs into ``cpp-runs.json``,
the file the recorded weights are re-taken from, and prints how far the
recorded weights have drifted from it.
"""

from __future__ import annotations

import contextlib
import json
import re
import sqlite3
from typing import TYPE_CHECKING, NewType, cast

from tools._common import RelPath
from tools.mutation_cpp_config import recorded_runs
from tools.mutation_cpp_legs import CppTree
from tools.mutation_cpp_slices import SuiteRuns, TreeRuns, partition, slice_domain
from tools.mutation_report import REPO_ROOT

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools.mutation_cpp_legs import CppLeg, CppTreeName

# What mull-runner-23 printed while it swept one leg, and a duration as it
# prints one: 6ms, 10.71s or 12m23.3s.
MullLog = NewType("MullLog", str)
MullDuration = NewType("MullDuration", str)

# Seconds one run of the test binary took, as Mull reports it.
RunSeconds = NewType("RunSeconds", float)

# Beside a leg's three Mull reports, the suite runs its mutants cost by file,
# which the leg writes and the merge copies with the reports.
CPP_LEG_RUNS_SUFFIX = ".runs.json"

# The merge's sum of the legs' figures by tree, beside ``cpp.json``: what the
# recorded weights are re-taken from (docs/operations/MUTATION.md).
CPP_RUNS_REPORT = "cpp-runs.json"

# The unmutated run Mull times before it runs a mutant, and the bar that ends
# it, which may follow other progress lines.
_BASELINE = re.compile(
    r"\[info\] Baseline run \(threads: \d+\)\n[\s\S]*?\] 1/1\. Finished in (\S+)"
)
_DURATION = re.compile(r"(?:(\d+)m(?=\d))?(\d+(?:\.\d+)?)(ms|s)")


def mull_seconds(text: MullDuration) -> RunSeconds | None:
    """Read a duration Mull printed, or None where it is not one of Mull's three shapes."""
    shape = _DURATION.fullmatch(text)
    if shape is None:
        return None
    minutes, value, unit = shape.groups()
    return RunSeconds(int(minutes or 0) * 60 + float(value) / (1000 if unit == "ms" else 1))


def baseline_seconds(log: MullLog) -> RunSeconds | None:
    """Read how long the leg's unmutated run took, or None where the log has no baseline."""
    found = _BASELINE.search(log)
    return None if found is None else mull_seconds(MullDuration(found.group(1)))


def leg_runs(sqlite_path: Path, log: MullLog) -> TreeRuns | Prose:
    """Count the suite runs a leg's mutants cost by file, or say why they cannot be counted.

    A path is made repository-relative at its ``cpp/`` component, as the
    survivor rows are.
    """
    if not sqlite_path.is_file():
        return Prose(f"mull-runner-23 wrote no {sqlite_path.name}, so its mutants have no weight")
    baseline = baseline_seconds(log)
    if not baseline:
        return Prose("mull-runner-23 printed no baseline run, so the leg's mutants have no weight")
    runs: TreeRuns = {}
    with contextlib.closing(sqlite3.connect(sqlite_path)) as conn:
        for site, duration_ms in conn.execute("SELECT filename, duration FROM mutant"):
            path = str(site)
            file = RelPath("cpp/" + path.split("/cpp/", 1)[1] if "/cpp/" in path else path)
            _add(runs, file, SuiteRuns(int(duration_ms) / 1000 / baseline))
    return dict(sorted(runs.items()))


def _add(into: TreeRuns, path: RelPath, runs: SuiteRuns) -> None:
    """Add a file's runs to a tree's figures."""
    into[path] = SuiteRuns(into.get(path, 0.0) + runs)


def tree_runs(artifact_dir: Path, legs: Sequence[CppLeg]) -> dict[CppTreeName, TreeRuns]:
    """Sum the legs' figures by tree, to the tenth of a run the record keeps."""
    sums: dict[CppTreeName, TreeRuns] = {}
    for leg in legs:
        path = artifact_dir / f"{leg.report_name}{CPP_LEG_RUNS_SUFFIX}"
        figures = cast("TreeRuns", json.loads(path.read_text(encoding="utf-8")))
        tree = sums.setdefault(leg.tree.key, {})
        for file, runs in figures.items():
            _add(tree, file, runs)
    return {
        tree: {path: SuiteRuns(round(value, 1)) for path, value in sorted(runs.items())}
        for tree, runs in sums.items()
    }


def weight_drift(observed: Mapping[CppTreeName, TreeRuns]) -> Prose:
    """Say, per tree, how far the recorded weights have drifted from the surface they balance.

    The slices are cut on the recorded figures, and the surface grows without
    anything refusing, so the cut goes stale quietly.  This is the number the
    scheduled review of the weights reads: what the heaviest slice would cost
    today, against an equal share, if the partition were cut on the recorded
    figures and run over the sweep just measured.
    """
    domain = slice_domain(REPO_ROOT, REPO_ROOT / "cpp" / "mull.yml")
    drift = ""
    for tree in CppTree:
        recorded = recorded_runs(tree)
        if not recorded:
            drift += f"weights ({tree.value}): none recorded, so its slices are cut on nothing\n"
            continue
        measured = observed.get(tree.key, {})
        loads = [
            sum(measured.get(path, 0.0) for path in claimed)
            for claimed in partition(domain, recorded)
        ]
        share = sum(loads) / len(loads)
        over = 100 * (max(loads) / share - 1) if share else 0.0
        drift += f"weights ({tree.value}): the heaviest slice costs {max(loads):.1f} of"
        drift += f" {sum(loads):.1f} suite runs, {over:.1f}% over an equal share of {share:.1f}\n"
        unrecorded = sorted(set(measured) - set(recorded))
        if unrecorded:
            drift += f"weights ({tree.value}): {len(unrecorded)} file(s) cost runs the record"
            drift += " does not count: " + ", ".join(unrecorded) + "\n"
    return Prose(drift)

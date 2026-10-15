# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that the C++ mutation lane's slices union to the census of the tree swept whole.

The lane spreads its sweep over slices (``tools/mutation_cpp_slices.py``),
each a build carrying the mutants of its own files alone, and the merge unions
their reports into the lane's census.  That rests on slicing changing which
mutants a build carries and nothing about their identity: Mull names a mutant
partly by an ordinal among its function's mutants, so a hold-out that reached
inside a file would renumber what it kept, and the patterns holding files out
are written by Python and read by the plugin's own regular-expression engine,
so an escape the two spell differently is a file not held out at all.  What
decides both is pinned: the plugin's release and patches, the configuration
and the slicing, so the gate runs when the branch moves one of them
(``tools/pin_scope.py``) and costs nothing otherwise.

The gate has two faces, since the whole tree's census needs a compiler and the
merge has none.  ``--census`` builds the whole tree in the lane's own
directory, dry-runs it and writes the census as ``cpp-mull-whole.json`` beside
the lane's reports under ``benchmarks/mutation/<short sha>/``, so the first
leg's artifact carries it.  ``--compare DIR`` finds every slice's sweep report
and the census under ``DIR``, each exactly once, unions the slices as the
merge does and holds the union's identifiers to the census's.  It reads
``DIR`` whole, so ``DIR`` holds the legs' reports and nothing else that
spells their names: the merge job downloads the legs' artifacts alone there.

Exits 0 when the union is the census or nothing the fact rests on moved, 1
when a slice repeats an identifier or the union and the census differ, and 2
when the claim cannot be reached: a tool is missing, the whole tree does not
build, the dry run writes no report, or a report is missing or repeated under
``DIR``.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import TYPE_CHECKING, NewType, TypedDict, cast

from tools._common import emit, git_toplevel, short_sha
from tools.mutation_cpp import (
    REPO_ROOT,
    LegPaths,
    build_cpp_mutation_tree,
    check_cpp_tools,
    cpp_sweep_directory,
    union_slices,
)
from tools.mutation_cpp_config import leg_config
from tools.mutation_cpp_dry_run import dry_run_report, leg_build_dir
from tools.mutation_cpp_legs import CPP_WHOLE_CENSUS, CppLeg, sliced_legs
from tools.mutation_report import MutationReport
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

    from tools.mutation_cpp_elements import MullPath

GATE = "check-cpp-slices-census"

# Where the lane archives a run's reports, by the commit's short hash.
ARTIFACT_BASE = REPO_ROOT / "benchmarks" / "mutation"

# A mutant as Mull names it in an Elements report: mutator, site and ordinal.
MutantId = NewType("MutantId", str)

# The file name of one report the comparison reads, as it lies under the legs directory.
ReportName = NewType("ReportName", str)

# How many of each difference a refusal names.
NAMED_DIFFERENCES = 3


class CensusMutant(TypedDict):
    """The field of a mutant in an Elements report that a census is made of."""

    id: MutantId


class CensusFile(TypedDict):
    """One file's entry in an Elements report: the mutants made in it."""

    mutants: list[CensusMutant]


class CensusReport(TypedDict):
    """An Elements report as a census reads it: each mutated file with its mutants."""

    files: Mapping[MullPath, CensusFile]


def _identifiers(report: CensusReport) -> list[MutantId]:
    """List every mutant an Elements report carries, in the report's order."""
    return [mutant["id"] for entry in report["files"].values() for mutant in entry["mutants"]]


def census_difference(whole_ids: Sequence[MutantId], union_ids: Sequence[MutantId]) -> Prose | None:
    """Say how the slices' union differs from the whole tree's census, or None where it does not.

    Every identifier of the census has to be in the union and every one of the
    union in the census; the refusal names up to three of each kind and both
    sizes.
    """
    whole = set(whole_ids)
    union = set(union_ids)
    if whole == union:
        return None
    lines = [f"the whole tree carries {len(whole)} mutants and the slices' union {len(union)}"]
    lines.extend(
        f"the whole tree carries {missing} and no slice does"
        for missing in sorted(whole - union)[:NAMED_DIFFERENCES]
    )
    lines.extend(
        f"a slice carries {extra} and the whole tree does not"
        for extra in sorted(union - whole)[:NAMED_DIFFERENCES]
    )
    return Prose("\n".join(lines))


def _wanted_reports() -> dict[ReportName, Prose]:
    """Name every report the comparison reads, each with where it comes from."""
    wanted = {
        ReportName(f"{leg.report_name}.json"): Prose(f"run the lane at stage {leg.slice_no}")
        for leg in sliced_legs()
    }
    wanted[ReportName(CPP_WHOLE_CENSUS)] = Prose("run --census in the first leg")
    return wanted


def find_reports(legs_dir: Path) -> Mapping[ReportName, Path] | Prose:
    """Find each slice's sweep report and the census under ``legs_dir``, exactly once each.

    A report missing or present twice is named with where to get it.
    """
    found: dict[ReportName, Path] = {}
    for name, source in _wanted_reports().items():
        copies = sorted(legs_dir.rglob(name))
        if len(copies) != 1:
            return Prose(f"{len(copies)} copies of {name} under {legs_dir}, wanted one: {source}")
        found[name] = copies[0]
    return found


def _load(report: Path) -> CensusReport:
    """Read one Elements report."""
    return cast("CensusReport", json.loads(report.read_text(encoding="utf-8")))


def compare(legs_dir: Path) -> ExitStatus:
    """Union the slices' reports under ``legs_dir`` and hold the union to the census there."""
    reports = find_reports(legs_dir)
    if isinstance(reports, str):
        emit(f"{GATE}: {reports}")
        return ExitStatus(2)
    slices = [_load(reports[ReportName(f"{leg.report_name}.json")]) for leg in sliced_legs()]
    whole = _load(reports[ReportName(CPP_WHOLE_CENSUS)])
    unioned = union_slices(slices)
    if isinstance(unioned, str):
        emit(f"{GATE}: {unioned}")
        return ExitStatus(1)
    whole_ids = _identifiers(whole)
    difference = census_difference(whole_ids, _identifiers(cast("CensusReport", unioned)))
    if difference is not None:
        emit(f"{GATE}: {difference}")
        return ExitStatus(1)
    sizes = ", ".join(str(len(_identifiers(part))) for part in slices)
    emit(f"{GATE}: slices of {sizes} union to the whole tree's {len(whole_ids)} mutants")
    return ExitStatus(0)


def census() -> ExitStatus:
    """Build the whole tree as the lane does, dry-run it and record its census beside the reports.

    The build's log and the dry run's reports go to a directory of the gate's
    own: a local sweep of the whole tree keeps its own log and Elements report
    in the artifact directory, under the names the build and the dry run would
    write, and the census must replace neither.
    """
    tools = check_cpp_tools()
    if isinstance(tools, str):
        emit(f"{GATE}: {tools}")
        return ExitStatus(2)
    cmake, _ = tools
    artifact_dir = ARTIFACT_BASE / short_sha(REPO_ROOT)
    artifact_dir.mkdir(parents=True, exist_ok=True)
    leg = CppLeg()
    build_dir = leg_build_dir(leg)
    recorded = artifact_dir / CPP_WHOLE_CENSUS
    with tempfile.TemporaryDirectory(prefix="cpp-census-") as scratch:
        work = Path(scratch)
        paths = LegPaths(cpp_sweep_directory(), build_dir, work, leg_config(leg, build_dir))
        built = build_cpp_mutation_tree(cmake, paths)
        if isinstance(built, MutationReport):
            emit(f"{GATE}: {built.error or 'the whole tree did not build'}")
            emit(_last_lines(Prose(built.raw_log)))
            return ExitStatus(2)
        report = dry_run_report(leg, work)
        if isinstance(report, str):
            emit(f"{GATE}: {report}")
            return ExitStatus(2)
        count = len(_identifiers(_load(report)))
        _ = shutil.move(report, recorded)
    emit(f"{GATE}: the whole tree carries {count} mutants, recorded in {recorded}")
    return ExitStatus(0)


# How much of a failed build's log the gate prints, since the log itself goes with the scratch.
LOG_TAIL_LINES = 20


def _last_lines(log: Prose) -> Prose:
    """Return the last ``LOG_TAIL_LINES`` lines of ``log``."""
    return Prose("\n".join(log.splitlines()[-LOG_TAIL_LINES:]))


def main() -> ExitStatus:
    """Record the whole tree's census, or hold the slices to it, when the branch moves a pin."""
    parser = argparse.ArgumentParser(description=__doc__)
    face = parser.add_mutually_exclusive_group(required=True)
    _ = face.add_argument(
        "--census",
        action="store_true",
        help="build the whole tree, dry-run it and record its census beside the lane's reports",
    )
    _ = face.add_argument(
        "--compare",
        type=Path,
        metavar="DIR",
        help="union the slices' reports under DIR and hold the union to the census there",
    )
    args = parser.parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.CPP_SLICES_CENSUS, repo_root):
        return ExitStatus(0)
    if args.census:
        return census()
    return compare(cast("Path", args.compare))


if __name__ == "__main__":
    sys.exit(main())

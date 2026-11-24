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

The gate has three faces, since the whole tree's census needs a compiler, the
merge has none, and a local run sweeps the tree whole and writes no slice's
report.  ``--census`` builds the whole tree in the lane's own directory,
dry-runs it and writes the census as ``cpp-mull-whole.json`` beside the lane's
reports under ``benchmarks/mutation/<short sha>/``, so the first leg's
artifact carries it.  ``--compare DIR`` finds every slice's sweep report and
the census under ``DIR``, each exactly once, unions the slices as the merge
does and holds the union's identifiers to the census's.  It reads ``DIR``
whole, so ``DIR`` holds the legs' reports and nothing else that spells their
names: the merge job downloads the legs' artifacts alone there.  ``--slices``
is the comparison a local run makes: it builds each slice in its leg's own
tree under its leg's configuration, as a leg does, dry-runs it into a
directory of the gate's own beside a copy of the census ``--census``
recorded, and compares that directory as ``--compare`` does.

The local face reads dry runs where the merge reads sweeps, so ``--census``
also holds the sweep report beside it, the whole tree's in a local run or a
slice's in a CI leg, to a dry run of the build it swept: the two list one set.

Exits 0 when the union is the census or nothing the fact rests on moved, 1
when a slice repeats an identifier, the union and the census differ or a sweep
and a dry run of its build list different mutants, and 2 when the claim
cannot be reached: a tool is missing, a tree does not build, a dry run writes
no report, no census is recorded, or a report is missing or repeated under
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

from tools._common import CommandWord, emit, git_toplevel, short_sha
from tools._progress import reporting
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


def _difference(
    first_ids: Sequence[MutantId],
    second_ids: Sequence[MutantId],
    sizes: Prose,
    only_first: Prose,
    only_second: Prose,
) -> Prose | None:
    """Say how two sets of mutants differ, or None where they do not.

    ``sizes`` is spelled with the two sizes, each ``only_`` line with one
    identifier only that side holds, up to three of each kind.
    """
    first = set(first_ids)
    second = set(second_ids)
    if first == second:
        return None
    lines = [sizes.format(len(first), len(second))]
    lines.extend(only_first.format(m) for m in sorted(first - second)[:NAMED_DIFFERENCES])
    lines.extend(only_second.format(m) for m in sorted(second - first)[:NAMED_DIFFERENCES])
    return Prose("\n".join(lines))


def census_difference(whole_ids: Sequence[MutantId], union_ids: Sequence[MutantId]) -> Prose | None:
    """Say how the slices' union differs from the whole tree's census, or None where it does not."""
    return _difference(
        whole_ids,
        union_ids,
        Prose("the whole tree carries {} mutants and the slices' union {}"),
        Prose("the whole tree carries {} and no slice does"),
        Prose("a slice carries {} and the whole tree does not"),
    )


def sweep_difference(
    leg: CppLeg, dry_ids: Sequence[MutantId], swept_ids: Sequence[MutantId]
) -> Prose | None:
    """Say how a leg's sweep report differs from a dry run of its build, or None if it does not."""
    return _difference(
        dry_ids,
        swept_ids,
        Prose(f"a dry run of the {leg} leg's build lists {{}} mutants and its sweep reports {{}}"),
        Prose("a dry run lists {} and the sweep does not"),
        Prose("the sweep reports {} and a dry run does not"),
    )


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


def _cmake() -> CommandWord | None:
    """Name the CMake the lane builds with, or say what is missing and return None."""
    tools = check_cpp_tools()
    if isinstance(tools, str):
        emit(f"{GATE}: {tools}")
        return None
    cmake, _ = tools
    return CommandWord(cmake)


def _dry_run(cmake: CommandWord, leg: CppLeg, work: Path) -> Path | None:
    """Build one leg's tree as the lane does, dry-run it into ``work`` and name its report.

    The build logs into ``work`` too.  A tree that does not build is reported
    with its error and its log's tail, a dry run writing no report with its
    reason, and either returns None.
    """
    build_dir = leg_build_dir(leg)
    paths = LegPaths(cpp_sweep_directory(), build_dir, work, leg_config(leg, build_dir))
    built = build_cpp_mutation_tree(cmake, paths)
    if isinstance(built, MutationReport):
        emit(f"{GATE}: {built.error or f'the {leg} leg did not build'}")
        emit(_last_lines(Prose(built.raw_log)))
        return None
    report = dry_run_report(leg, work)
    if isinstance(report, str):
        emit(f"{GATE}: {report}")
        return None
    return report


def _recorded_census() -> Path:
    """Name where the whole tree's census lies, beside this commit's reports."""
    return ARTIFACT_BASE / short_sha(REPO_ROOT) / CPP_WHOLE_CENSUS


def _sweeps_held(artifact_dir: Path, whole: Sequence[MutantId], work: Path) -> ExitStatus:
    """Hold each sweep report in ``artifact_dir`` to a dry run of the build it swept.

    The whole tree's dry run is the census; a slice's is run into ``work`` over
    the tree its sweep built, which is not rebuilt.
    """
    status = ExitStatus(0)
    for leg in (CppLeg(), *sliced_legs()):
        swept = artifact_dir / f"{leg.report_name}.json"
        if not swept.is_file():
            continue
        dry = whole
        if leg.slice_no is not None:
            leg_dir = work / leg.report_name
            leg_dir.mkdir()
            report = dry_run_report(leg, leg_dir)
            if isinstance(report, str):
                emit(f"{GATE}: {report}")
                return ExitStatus(2)
            dry = _identifiers(_load(report))
        difference = sweep_difference(leg, dry, _identifiers(_load(swept)))
        if difference is not None:
            emit(f"{GATE}: {difference}")
            status = ExitStatus(1)
            continue
        emit(f"{GATE}: the {leg} leg's sweep reports the {len(set(dry))} mutants its dry run lists")
    return status


def census() -> ExitStatus:
    """Record the whole tree's census beside the reports, and hold each sweep there to a dry run.

    The whole tree is built as the lane builds it and dry-run.  The build's
    log and the dry run's reports go to a directory of the gate's own: a local
    sweep of the whole tree keeps its own log and Elements report in the
    artifact directory, under the names the build and the dry run would write,
    and the census must replace neither.
    """
    cmake = _cmake()
    if cmake is None:
        return ExitStatus(2)
    recorded = _recorded_census()
    recorded.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cpp-census-") as scratch:
        work = Path(scratch)
        report = _dry_run(cmake, CppLeg(), work)
        if report is None:
            return ExitStatus(2)
        whole = _identifiers(_load(report))
        _ = shutil.move(report, recorded)
        emit(f"{GATE}: the whole tree carries {len(whole)} mutants, recorded in {recorded}")
        return _sweeps_held(recorded.parent, whole, work)


def dry_run_slices() -> ExitStatus:
    """Build and dry-run each slice as its leg does, and hold their union to the recorded census.

    Each slice's report goes to a directory of its own under the gate's, named
    as the leg's artifact is, beside a copy of the census, so the comparison
    reads them as the merge job's download lays the legs' reports out.  The
    first slice that does not build or writes no report ends the face, the
    later ones left unbuilt.
    """
    recorded = _recorded_census()
    if not recorded.is_file():
        emit(f"{GATE}: no census at {recorded}: run --census first")
        return ExitStatus(2)
    cmake = _cmake()
    if cmake is None:
        return ExitStatus(2)
    with tempfile.TemporaryDirectory(prefix="cpp-slices-") as scratch:
        legs_dir = Path(scratch)
        for leg in sliced_legs():
            work = legs_dir / leg.report_name
            work.mkdir()
            if _dry_run(cmake, leg, work) is None:
                return ExitStatus(2)
        _ = shutil.copy(recorded, legs_dir / CPP_WHOLE_CENSUS)
        return compare(legs_dir)


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
    _ = face.add_argument(
        "--slices",
        action="store_true",
        help="build and dry-run each slice as its leg does, and hold their union to the census",
    )
    args = parser.parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.CPP_SLICES_CENSUS, repo_root):
        return ExitStatus(0)
    if args.census:
        return census()
    if args.slices:
        return dry_run_slices()
    return compare(cast("Path", args.compare))


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("check-cpp-slices-census")))

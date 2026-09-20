# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ mutation lane: Mull over the two mutation trees, merged into one verdict.

Driven by ``tools/mutation_run.py`` as the ``cpp`` binding.  The lane builds
each tree ``CPP_LANES`` names, sweeps it under ``mull-runner-23``, and merges
the trees' Elements reports so a mutant is a survivor only where every tree
let it live; the SQLite report of each tree feeds the kill-route census in
``tools/mutation_routes.py``.

``ALETHEIA_MUTATION_CPP_STAGE`` splits the lane across processes (see
``CppStage``): a leg sweeps one tree and is its own binding, ``cpp-leak`` or
``cpp-plain``, whose survivors nobody judges; the merge stage reads the legs'
reports from the directory ``ALETHEIA_MUTATION_CPP_LEGS`` names and is gated
as the whole lane is.
"""

from __future__ import annotations

import collections
import copy
import json
import os
import re
import shutil
from enum import StrEnum
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, cast

from tools._common import run_streaming, short_sha
from tools.cpp_scratch import reap_dead_scratch_dirs
from tools.mutation_report import MutationReport, SurvivorKey
from tools.mutation_routes import lane_routes, merge_routes

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parent.parent

# A mutation score of 100% leaves the killed-from-score formula undefined
# (division by ``100 - score``); the C++ parser special-cases it.
FULL_SCORE_PCT = 100


def elements_survivor_rows(
    report: Mapping[str, object], read_line: Callable[[str, int], str]
) -> dict[SurvivorKey, int]:
    """Collect the survivors of a Mull Elements report into rows.

    ``report`` is the parsed ``mutation-testing-elements`` JSON: ``files``
    maps an absolute path to its mutants, each with a ``status``, a
    ``mutatorName`` and a start line.  A path is made repository-relative at
    its ``cpp/`` component; ``read_line(file, line)`` supplies the source line,
    which is stripped before it keys the row.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    files = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
    for path, entry in files.items():
        mutants = cast("list[Mapping[str, object]]", entry.get("mutants", []))
        for mutant in mutants:
            if mutant.get("status") != "Survived":
                continue
            file = "cpp/" + path.split("/cpp/", 1)[1] if "/cpp/" in path else path
            location = cast("Mapping[str, Mapping[str, int]]", mutant["location"])
            line = location["start"]["line"]
            rows[(str(mutant["mutatorName"]), file, read_line(file, line).strip())] += 1
    return rows


def _repo_line(file: str, line: int) -> str:
    """Read the ``line``-th line (1-based) of ``file`` under the repository root."""
    with (REPO_ROOT / file).open(encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


# The Elements report the C++ runner asks Mull for, beside ``cpp.json``.
CPP_ELEMENTS_REPORT = "cpp-mull.json"


def cpp_survivor_rows(artifact_dir: Path) -> dict[SurvivorKey, int] | None:
    """Read the C++ sweep's survivor rows from its Elements report, if it wrote one."""
    path = artifact_dir / CPP_ELEMENTS_REPORT
    if not path.is_file():
        return None
    elements = cast("Mapping[str, object]", json.loads(path.read_text(encoding="utf-8")))
    return elements_survivor_rows(elements, _repo_line)


def _check_cpp_tools() -> tuple[str, str] | str:
    """Return ``(cmake, mull_runner)`` paths when C++ can run, else an error string."""
    cmake = shutil.which("cmake")
    if cmake is None:
        return "cmake not in PATH; install CMake 3.25+ to run the C++ mutation lane"
    mull_runner = shutil.which("mull-runner-23")
    if mull_runner is None:
        return (
            "mull-runner-23 not in PATH; build it with tools/build_mull.sh "
            "(see docs/operations/MUTATION.md § Installation)"
        )
    if shutil.which("clang++-23") is None:
        return "clang++-23 not in PATH; install clang-23 (apt.llvm.org, or Debian apt)"
    plugin = Path.home() / ".local" / "bin" / "mull-ir-frontend-23"
    if not plugin.is_file():
        return (
            f"mull-ir-frontend-23 plugin not found at {plugin}; "
            "see docs/operations/MUTATION.md § Installation"
        )
    return (cmake, mull_runner)


def _killed_from_mull(raw: str, survived: int) -> int:
    """Derive the killed count from a Mull summary, falling back through its shapes."""
    killed_m = re.search(r"Killed[^:\n]*:\s*(\d+)", raw)
    if killed_m:
        return int(killed_m.group(1))
    score_m = re.search(r"Mutation score:\s*(\d+)\s*%", raw)
    if score_m:
        score_pct_in = int(score_m.group(1))
        if score_pct_in >= FULL_SCORE_PCT:
            return survived  # impossible to compute exactly; pick a reasonable proxy
        return round(survived * score_pct_in / (FULL_SCORE_PCT - score_pct_in))
    # Score not parsed either; fall back to "everything killed" guess.
    return 0


def _build_cpp_mutation_tree(
    cmake: str,
    cpp_root: Path,
    build_dir: Path,
    artifact_dir: Path,
    sanitizer: str,
) -> str | MutationReport:
    """Configure + build one mutation build tree, returning the raw log or a failure report."""
    cmake_proc = run_streaming(
        [
            cmake,
            "-B",
            str(build_dir),
            "-DALETHEIA_MUTATION=ON",
            f"-DALETHEIA_SANITIZER={sanitizer}",
            "-DCMAKE_C_COMPILER=clang-23",
            "-DCMAKE_CXX_COMPILER=clang++-23",
        ],
        cwd=cpp_root,
    )
    raw = "=== cmake configure ===\n" + cmake_proc.stdout + "\n"
    if cmake_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=f"cmake configure failed (exit {cmake_proc.returncode}; see cpp.raw.txt)",
        )

    build_proc = run_streaming(cpp_build_command(cmake, build_dir), cwd=cpp_root)
    raw += "=== cmake build ===\n" + build_proc.stdout + "\n"
    if build_proc.returncode != 0:
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=f"cmake build failed (exit {build_proc.returncode}; see cpp.raw.txt)",
        )
    return raw


# Compiles in flight at once during a mutation build.  The plugin compile of
# one unit held up to 492 MB of memory when measured, so eight is under 4 GB
# on any host, and the CI runner has four cores; a build with no such count
# compiled one unit at a time and took 8 minutes of a leg on the runner.
CPP_BUILD_JOBS_CAP = 8


def cpp_build_command(cmake: str, build_dir: Path) -> list[str]:
    """Build the mutation tree's test binary, several units at a time."""
    jobs = min(os.cpu_count() or 1, CPP_BUILD_JOBS_CAP)
    return [cmake, "--build", str(build_dir), "--target", "unit_tests", "--parallel", str(jobs)]


# The two trees the C++ sweep runs, by the sanitizer each is built with and
# the directory it lives in. Under LeakSanitizer a mutant that removes a
# destructor leaks the object and fails, where a plain build cannot tell it
# from the original. The plain tree carries the allocation-fault sweeps, which
# replace the program's allocation functions to reach the cleanup a container
# runs while it throws; a sanitizer runtime defines those same functions, so
# the two cannot be linked together. A mutant survives the sweep only where it
# survived both.
CPP_LANES: tuple[tuple[str, str], ...] = (("leak", "build-mutation"), ("", "build-mutation-plain"))


def lane_name(sanitizer: str) -> str:
    """Name a tree by the sanitizer it is built with; the unsanitized tree is ``plain``."""
    return sanitizer or "plain"


def _lane_report_name(sanitizer: str) -> str:
    """Name the reports one lane writes, beside the merged Elements report."""
    return f"{Path(CPP_ELEMENTS_REPORT).stem}-{lane_name(sanitizer)}"


# The three reports Mull writes per tree, by suffix: Elements (what the merge
# reads), SQLite (what the kill-route census reads) and the IDE summary.
CPP_LANE_REPORT_SUFFIXES: tuple[str, ...] = (".json", ".sqlite", ".txt")


class CppStage(StrEnum):
    """What one process of the C++ lane does.

    A leg, ``LEAK`` or ``PLAIN``, builds and sweeps that one tree; ``MERGE``
    sweeps nothing and combines the legs' reports.  Unset, the lane runs
    both trees in one process and merges them itself.
    """

    LEAK = "leak"
    PLAIN = "plain"
    MERGE = "merge"


CPP_STAGE_ENV = "ALETHEIA_MUTATION_CPP_STAGE"
CPP_LEGS_ENV = "ALETHEIA_MUTATION_CPP_LEGS"

# The merge stage's record of each leg's wall clock, beside ``cpp.json``, so
# the budget a CI job gives a leg is read off the run that measured it.
CPP_LEGS_REPORT = "cpp-legs.json"


def leg_binding(stage: CppStage) -> str:
    """Name the binding a leg reports as: ``cpp-leak`` or ``cpp-plain``.

    A leg is its own binding so its census lands in its own ``cpp-leak.json``
    and never reads as the lane's ``cpp.json``; the drift gate records a leg
    and judges only the merge.
    """
    return f"cpp-{stage.value}"


def is_cpp_leg(binding: str) -> bool:
    """Whether a report's binding name is one leg of the C++ lane."""
    return any(binding == leg_binding(stage) for stage in CppStage if stage is not CppStage.MERGE)


def cpp_stage() -> CppStage | None:
    """Read the C++ stage from the environment; unset or empty is the whole lane.

    Raises ``ValueError`` naming the variable on a value that is no stage, so
    a misspelt stage in a CI job fails that job rather than sweeping nothing.
    """
    value = os.environ.get(CPP_STAGE_ENV, "")
    if not value:
        return None
    try:
        return CppStage(value)
    except ValueError:
        stages = ", ".join(stage.value for stage in CppStage)
        msg = f"{CPP_STAGE_ENV}={value!r} is not one of {stages}"
        raise ValueError(msg) from None


class ElementsCounts(NamedTuple):
    """How many mutants an Elements report holds, and how many of them survived."""

    total: int
    survived: int


def elements_counts(report: Mapping[str, object]) -> ElementsCounts:
    """Count an Elements report's mutants by status."""
    files = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
    statuses = [
        str(mutant.get("status"))
        for entry in files.values()
        for mutant in cast("list[Mapping[str, object]]", entry.get("mutants", []))
    ]
    return ElementsCounts(len(statuses), statuses.count("Survived"))


# The kill-route census of the C++ sweep, beside the merged Elements report.
CPP_ROUTES_REPORT = "cpp-routes.json"


def cpp_kill_routes(artifact_dir: Path) -> dict[str, int] | None:
    """Count the C++ sweep's mutants by kill route, or None where a lane wrote no SQLite report."""
    paths = [artifact_dir / f"{_lane_report_name(sanitizer)}.sqlite" for sanitizer, _ in CPP_LANES]
    if not all(path.is_file() for path in paths):
        return None
    return merge_routes([lane_routes(path) for path in paths])


def merge_elements(reports: list[Mapping[str, object]]) -> dict[str, object]:
    """Merge Elements reports, keeping a mutant a survivor only where every lane let it survive.

    The lanes compile the same sources with the same plugin, so they carry the
    same mutants under the same identifiers; a mutant one lane killed is
    killed, whichever instrument read it.
    """
    survived_everywhere: set[str] | None = None
    for report in reports:
        files = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
        survivors = {
            str(mutant["id"])
            for entry in files.values()
            for mutant in cast("list[Mapping[str, object]]", entry.get("mutants", []))
            if mutant.get("status") == "Survived"
        }
        survived_everywhere = (
            survivors if survived_everywhere is None else survived_everywhere & survivors
        )
    merged = copy.deepcopy(dict(reports[0]))
    files = cast("dict[str, dict[str, object]]", merged.get("files", {}))
    for entry in files.values():
        for mutant in cast("list[dict[str, object]]", entry.get("mutants", [])):
            if mutant.get("status") != "Survived":
                continue
            if str(mutant["id"]) not in (survived_everywhere or set()):
                mutant["status"] = "Killed"
    return merged


def cpp_lane_command(
    mull_runner: str, build_dir: Path, artifact_dir: Path, sanitizer: str
) -> list[str]:
    """Build the runner's argv for one lane, the test binary's own argv behind ``--``."""
    return [
        mull_runner,
        str(build_dir / "unit_tests"),
        "--reporters=IDE",
        "--reporters=Elements",
        # The SQLite report keeps each mutant's exit status and the test
        # binary's own output, which is what tells a kill by a test's
        # assertion from one by a fault.
        "--reporters=SQLite",
        f"--report-dir={artifact_dir}",
        f"--report-name={_lane_report_name(sanitizer)}",
        # Everything past this marker is the test binary's own argv.
        # Catch2 shuffles its cases by default under a seed that changes
        # every run, and mull runs the binary once per mutant, so an
        # unpinned lane reads a different census each sweep: two pinned
        # sweeps of one tree agreed on every mutant, where two shuffled
        # ones read the fault route at 98 and 99 against the pinned 93.
        # A fault ends the process, so the order decides which test
        # reports before the run stops. Pinning makes the recorded census
        # a measurement rather than a sample; that the verdict holds under
        # every order is a separate property, and a probe sweeps several
        # orders to hold it.
        "--",
        "--order",
        "decl",
    ]


def _run_cpp_lane(
    mull_runner: str,
    cpp_root: Path,
    build_dir: Path,
    artifact_dir: Path,
    sanitizer: str,
) -> tuple[str, tuple[int, int] | None]:
    """Run one built tree under mull-runner, returning its log and its (killed, survived)."""
    # The mutation binary folds in the real-FFI integration tests, which read
    # the repository root from the environment the way ctest passes it.  Mull
    # runs the binary directly, so nothing would set it and every mutant would
    # read killed because the test died at setup.
    #
    # ALETHEIA_LIB is dropped for the same reason in reverse: with it set the
    # library lookup returns before it reads the repository root, leaving that
    # read's mutants uncovered, so the same tree would score differently for a
    # caller who had sourced the environment script.
    mull_env = os.environ | {"ALETHEIA_REPO_ROOT": str(REPO_ROOT)}
    mull_env.pop("ALETHEIA_LIB", None)
    # The IDE reporter prints the summary the counts are read from; the
    # Elements reporter writes every mutant with its status and site, which
    # is what the ledger is checked against.
    runner_proc = run_streaming(
        cpp_lane_command(mull_runner, build_dir, artifact_dir, sanitizer),
        cwd=cpp_root,
        env=mull_env,
    )
    lane = lane_name(sanitizer)
    raw = f"=== mull-runner-23 ({lane}) ===\n" + runner_proc.stdout + "\n"
    reaped = reap_dead_scratch_dirs()
    raw += f"scratch directories left by killed runs and removed: {reaped}\n"
    # Mull's own summary goes to the IDE report, and its stdout carries the
    # survivor count only when there is one: a lane that killed everything
    # says so in the report alone, so the report is part of the lane's log.
    ide_report = artifact_dir / f"{_lane_report_name(sanitizer)}.txt"
    if ide_report.is_file():
        raw += ide_report.read_text(encoding="utf-8") + "\n"
    return raw, mull_counts(raw)


def _sweep_cpp_lane(
    cmake: str,
    mull_runner: str,
    build_dir: Path,
    artifact_dir: Path,
    sanitizer: str,
) -> tuple[str, Mapping[str, object] | str]:
    """Build and sweep one lane, returning its log and its report or the reason it has none."""
    lane = lane_name(sanitizer)
    cpp_root = build_dir.parent
    raw = f"=== {lane} lane ===\n"
    built = _build_cpp_mutation_tree(cmake, cpp_root, build_dir, artifact_dir, sanitizer)
    if isinstance(built, MutationReport):
        return raw + built.raw_log, built.error or f"the {lane} lane did not build"
    raw += built
    lane_raw, counts = _run_cpp_lane(mull_runner, cpp_root, build_dir, artifact_dir, sanitizer)
    raw += lane_raw
    if counts is None:
        return raw, f"could not parse the {lane} lane's mull-runner-23 summary (see cpp.raw.txt)"
    report_path = artifact_dir / f"{_lane_report_name(sanitizer)}.json"
    if not report_path.is_file():
        return raw, f"the {lane} lane wrote no {report_path.name}"
    return raw, cast("Mapping[str, object]", json.loads(report_path.read_text(encoding="utf-8")))


def run_cpp(artifact_dir: Path) -> MutationReport:
    """Mull pass over the mutation trees; a mutant survives only where every lane let it.

    The stage (``cpp_stage``) selects the whole lane, one leg or the merge.
    """
    try:
        stage = cpp_stage()
    except ValueError as exc:
        return MutationReport("cpp", "mull", 0, 0, "", error=str(exc))
    if stage is CppStage.MERGE:
        return _merge_cpp_legs(artifact_dir)
    checked = _check_cpp_tools()
    if isinstance(checked, str):
        return MutationReport("cpp", "mull", 0, 0, "", error=checked)
    cmake, mull_runner = checked

    cpp_root = REPO_ROOT / "cpp"
    raw = ""
    reports: list[Mapping[str, object]] = []
    for sanitizer, directory in CPP_LANES:
        if stage is not None and lane_name(sanitizer) != stage.value:
            continue
        lane_raw, outcome = _sweep_cpp_lane(
            cmake, mull_runner, cpp_root / directory, artifact_dir, sanitizer
        )
        raw += lane_raw
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        if isinstance(outcome, str):
            return MutationReport("cpp", "mull", 0, 0, raw, error=outcome)
        reports.append(outcome)

    if stage is not None:
        # One leg: its result is the tree's own census, judged by nobody until
        # the merge reads every tree.
        total, survived = elements_counts(reports[0])
        raw += f"=== {stage.value} leg ===\nkilled {total - survived}, survived {survived}"
        raw += f" of {total}\n"
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(leg_binding(stage), "mull", total - survived, survived, raw)
    return _finish_cpp(artifact_dir, raw, reports)


def _merge_cpp_legs(artifact_dir: Path) -> MutationReport:
    """Merge the legs' reports found under the directory ``CPP_LEGS_ENV`` names.

    Each tree's three reports are wanted exactly once under that directory,
    wherever the download put them; a tree with a report missing is a leg
    that did not finish, and the lane has no verdict without it.
    """
    legs = os.environ.get(CPP_LEGS_ENV, "")
    if not legs:
        msg = f"{CPP_STAGE_ENV}=merge reads the legs' reports from {CPP_LEGS_ENV}, which is unset"
        return MutationReport("cpp", "mull", 0, 0, "", error=msg)
    legs_dir = Path(legs)
    raw = f"=== merge of the legs under {legs_dir} ===\n"
    reports: list[Mapping[str, object]] = []
    for sanitizer, _ in CPP_LANES:
        copied = _copy_leg_reports(legs_dir, artifact_dir, sanitizer)
        if isinstance(copied, str):
            return MutationReport("cpp", "mull", 0, 0, raw + copied + "\n", error=copied)
        raw += copied.log
        reports.append(copied.elements)
    elapsed = _legs_elapsed(legs_dir)
    if isinstance(elapsed, str):
        return MutationReport("cpp", "mull", 0, 0, raw + elapsed + "\n", error=elapsed)
    (artifact_dir / CPP_LEGS_REPORT).write_text(
        json.dumps({leg.value: secs for leg, secs in elapsed.items()}, indent=2)
    )
    for leg, secs in elapsed.items():
        raw += f"{leg.value} leg swept in {secs}s\n"
    return _finish_cpp(artifact_dir, raw, reports)


class LegReports(NamedTuple):
    """What one leg contributed to the merge: the log lines and its Elements report."""

    log: str
    elements: Mapping[str, object]


def _copy_leg_reports(legs_dir: Path, artifact_dir: Path, sanitizer: str) -> LegReports | str:
    """Copy one tree's three reports beside the merge, or say which is not there once."""
    log = ""
    for suffix in CPP_LANE_REPORT_SUFFIXES:
        name = _lane_report_name(sanitizer) + suffix
        found = sorted(legs_dir.rglob(name))
        if len(found) != 1:
            lane = lane_name(sanitizer)
            return f"the {lane} leg: {len(found)} copies of {name} under {legs_dir}, wanted one"
        _ = shutil.copyfile(found[0], artifact_dir / name)
        log += f"{lane_name(sanitizer)} leg: {found[0]}\n"
    report_path = artifact_dir / (_lane_report_name(sanitizer) + ".json")
    elements = cast("Mapping[str, object]", json.loads(report_path.read_text(encoding="utf-8")))
    return LegReports(log, elements)


def _legs_elapsed(legs_dir: Path) -> dict[CppStage, float] | str:
    """Read each leg's wall clock from the summary its run wrote, or say what is wrong.

    Every leg's summary must be there, once, and must record the commit this
    merge runs at: the legs of another commit merge into a verdict about
    nothing.
    """
    commit = short_sha(REPO_ROOT)
    elapsed: dict[CppStage, float] = {}
    for summary_path in sorted(legs_dir.rglob("summary.json")):
        summary = cast("Mapping[str, object]", json.loads(summary_path.read_text(encoding="utf-8")))
        runs = cast("list[Mapping[str, object]]", summary.get("runs", []))
        secs = cast("Mapping[str, float]", summary.get("elapsed_s", {})).get("cpp")
        legs = [str(run.get("binding")) for run in runs if is_cpp_leg(str(run.get("binding")))]
        if not legs or secs is None:
            continue
        if summary.get("commit") != commit:
            return f"{summary_path} is a run at {summary.get('commit')}, this merge is at {commit}"
        stage = CppStage(legs[0].removeprefix("cpp-"))
        if stage in elapsed:
            return f"{summary_path} is a second {stage.value} leg"
        elapsed[stage] = secs
    missing = [
        lane_name(sanitizer)
        for sanitizer, _ in CPP_LANES
        if CppStage(lane_name(sanitizer)) not in elapsed
    ]
    if missing:
        return f"no summary of the {', '.join(missing)} leg under {legs_dir}"
    return elapsed


def _finish_cpp(
    artifact_dir: Path, raw: str, reports: list[Mapping[str, object]]
) -> MutationReport:
    """Merge the trees' reports, count the kill routes, and write the lane's log."""
    total, survived = _merge_cpp_lanes(artifact_dir, reports)
    routes = cpp_kill_routes(artifact_dir)
    raw += f"=== merged ===\nkilled {total - survived}, survived {survived} of {total}\n"
    if routes is not None:
        (artifact_dir / CPP_ROUTES_REPORT).write_text(json.dumps(routes, indent=2))
        raw += "routes: " + ", ".join(f"{route} {count}" for route, count in routes.items()) + "\n"
    (artifact_dir / "cpp.raw.txt").write_text(raw)
    return MutationReport("cpp", "mull", total - survived, survived, raw)


def _merge_cpp_lanes(artifact_dir: Path, reports: list[Mapping[str, object]]) -> ElementsCounts:
    """Write the merged Elements report and return its counts."""
    merged = merge_elements(reports)
    (artifact_dir / CPP_ELEMENTS_REPORT).write_text(json.dumps(merged))
    return elements_counts(merged)


def mull_counts(raw: str) -> tuple[int, int] | None:
    """Read ``(killed, survived)`` from a lane's log, or None if it carries no summary.

    The log is mull-runner's stdout followed by its IDE report.

    Mull-19 tail summary lines (the actual format observed empirically)::

        [info] Mutation score: 56%
        [info] Surviving mutants: 17
        [info] Total execution time: 273ms

    When NOTHING survives, Mull omits the "Surviving mutants:" line entirely
    and prints "All mutations have been killed" with a 100% score instead, so
    a missing survivor line is the 0-survivor case, not a parse failure.  The
    exact total comes from Mull's "<n>/<n>. Finished" progress tail (killed =
    total - survived); the score-based estimate is the fallback when the
    progress line is absent (older Mull / piped output).
    """
    survived_m = re.search(r"Surviving mutants:\s*(\d+)", raw) or re.search(
        r"Survived[^:\n]*:\s*(\d+)", raw
    )
    all_killed = bool(
        re.search(r"All mutations have been killed", raw)
        or re.search(r"Mutation score:\s*100\s*%", raw)
    )
    if survived_m:
        survived = int(survived_m.group(1))
    elif all_killed:
        survived = 0
    else:
        return None
    finished = re.findall(r"\d+/(\d+)\.\s*Finished", raw)
    killed = int(finished[-1]) - survived if finished else _killed_from_mull(raw, survived)
    return killed, survived

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ mutation lane: Mull over the mutation tree, one verdict.

Driven by ``tools/mutation_run.py`` as the ``cpp`` binding.  The lane builds
the mutation tree, sweeps it under ``mull-runner-23`` and reads the verdict
off its Elements report; the SQLite report feeds the kill-route census in
``tools/mutation_routes.py``.

``ALETHEIA_MUTATION_CPP_STAGE`` splits the lane across processes (see
``CppLeg`` in ``tools/mutation_cpp_legs.py``): a leg builds the tree carrying
the mutants of one slice of the surface and is its own binding, ``cpp-1`` and
its siblings, whose survivors nobody judges; the merge stage reads the legs'
reports from the directory ``ALETHEIA_MUTATION_CPP_LEGS`` names, unions the
slices, and is gated as the whole lane is.

A slice is how the work is spread over CI jobs and not a unit of meaning: the
tree is what an instrument reads and what a verdict is about.  With the stage
unset the lane sweeps the tree whole in one process, which is what a local run
does and what the recorded census was taken with, so the sliced union has
something to be equal to.
"""

from __future__ import annotations

import collections
import copy
import json
import os
import re
import shutil
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, cast

from tools._common import run_streaming, short_sha
from tools._resources import detect_cpus
from tools.cpp_scratch import reap_dead_scratch_dirs, scratch_root
from tools.mutation_cpp_config import leg_config, leg_config_path
from tools.mutation_cpp_legs import (
    CPP_ELEMENTS_REPORT,
    CPP_LEGS_ENV,
    CPP_MERGE_STAGE,
    CPP_STAGE_ENV,
    CppLeg,
    cpp_stage,
    leg_of_binding,
    sliced_legs,
)
from tools.mutation_cpp_runs import (
    CPP_LEG_RUNS_SUFFIX,
    CPP_RUNS_REPORT,
    MullLog,
    lane_runs,
    leg_runs,
    weight_drift,
)
from tools.mutation_cpp_slices import CPP_SLICES
from tools.mutation_report import (
    KillRoute,
    MutantCount,
    MutationReport,
    Observed,
    SurvivorKey,
    UnobservedKey,
    UnobservedRow,
    load_spec,
    unobserved_ledger_to_rows,
    unobserved_rows_to_ledger,
)
from tools.mutation_routes import KILL_ROUTES, Ending, lane_endings, merge_endings

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping, Sequence

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


# The routes a kill takes when no test observed it: the standard library's own
# check and a bare signal.
_UNOBSERVED_ROUTES: frozenset[str] = frozenset({"check", "fault"})


def unobserved_kill_rows(
    legs: Sequence[Mapping[str, Ending]], read_line: Callable[[str, int], str]
) -> dict[UnobservedKey, int]:
    """Collect the kills no test observes by behaviour into rows.

    ``legs`` holds each leg's endings by mutant; the legs are disjoint, so a
    mutant has one ending.  A mutant is here when it ended by a check the
    standard library runs in the mutation build or by a bare signal: what it
    changes, a guard for most of them and the value an index is computed from
    for the rest, leads straight to an operation the language does not define,
    and the suite reports nothing before the process stops.  A row is keyed as
    a survivor's is, by mutator, repository-relative file and the stripped text
    of the source line rather than its number, plus the route and what the
    check refused; ``read_line(file, line)`` supplies the text.  The
    instantiations of one template share a line and are one row with their
    count.
    """
    rows: dict[UnobservedKey, int] = collections.Counter()
    for mutant in {mutant for leg in legs for mutant in leg}:
        endings = [leg[mutant] for leg in legs if mutant in leg]
        route = next(r for r in KILL_ROUTES if r in {ending.route for ending in endings})
        if route not in _UNOBSERVED_ROUTES:
            continue
        mutator, location = mutant.split(":", 1)
        path, line = location.split(":")[:2]
        file = "cpp/" + path.split("/cpp/", 1)[1] if "/cpp/" in path else path
        refused = next((ending.refused for ending in endings if ending.refused), "")
        rows[(mutator, file, read_line(file, int(line)).strip(), route, refused)] += 1
    return rows


def _repo_line(file: str, line: int) -> str:
    """Read the ``line``-th line (1-based) of ``file`` under the repository root."""
    with (REPO_ROOT / file).open(encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


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


class LegPaths(NamedTuple):
    """Where one leg works: the tree it builds in, what it writes, what it reads.

    One value rather than four parameters, because they travel together from
    the sweep into the build and the run, and a build directory paired with
    another leg's configuration is the one mistake here that reads as a clean
    sweep of the wrong mutants.
    """

    cpp_root: Path
    build_dir: Path
    artifact_dir: Path
    config: Path


def build_cpp_mutation_tree(cmake: str, paths: LegPaths) -> str | MutationReport:
    """Configure + build one leg's mutation build tree, returning the raw log or a failure report.

    The configuration is named to the configure, which hands it both to the
    plugin and to the compiler cache: a build's objects carry the mutants that
    configuration asks for, so it is what tells one slice's objects from
    another's, and caching them under anything less would serve one slice the
    other's.
    """
    cmake_proc = run_streaming(
        [
            cmake,
            "-B",
            str(paths.build_dir),
            "-DALETHEIA_MUTATION=ON",
            f"-DALETHEIA_MULL_CONFIG={paths.config}",
            "-DCMAKE_C_COMPILER=clang-23",
            "-DCMAKE_CXX_COMPILER=clang++-23",
        ],
        cwd=paths.cpp_root,
    )
    raw = "=== cmake configure ===\n" + cmake_proc.stdout + "\n"
    if cmake_proc.returncode != 0:
        (paths.artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(
            "cpp",
            "mull",
            0,
            0,
            raw,
            error=f"cmake configure failed (exit {cmake_proc.returncode}; see cpp.raw.txt)",
        )

    build_proc = run_streaming(cpp_build_command(cmake, paths.build_dir), cwd=paths.cpp_root)
    raw += "=== cmake build ===\n" + build_proc.stdout + "\n"
    if build_proc.returncode != 0:
        (paths.artifact_dir / "cpp.raw.txt").write_text(raw)
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

# The test binary the tree is built for and the runner runs once per mutant:
# the unit suite, with the integration and loader suites folded in by the
# mutation build (cpp/CMakeLists.txt).
CPP_TEST_TARGET = "unit_tests"


def cpp_build_command(cmake: str, build_dir: Path) -> list[str]:
    """Build the mutation tree's test binary, several units at a time."""
    jobs = min(detect_cpus(), CPP_BUILD_JOBS_CAP)
    return [cmake, "--build", str(build_dir), "--target", CPP_TEST_TARGET, "--parallel", str(jobs)]


# The three reports Mull writes per leg, by suffix: Elements (what the union
# reads), SQLite (what the kill-route census reads) and the IDE summary.
CPP_LEG_REPORT_SUFFIXES: tuple[str, ...] = (".json", ".sqlite", ".txt")


# The merge stage's record of each leg's wall clock, beside ``cpp.json``, so
# the budget a CI job gives a leg is read off the run that measured it.
CPP_LEGS_REPORT = "cpp-legs.json"

# Milliseconds a mutant's run may take before the runner ends it. The cap is
# a backstop and never a verdict: a mutant it ends is neither killed nor
# survived, and the lane refuses a sweep in which it fired. Mull's own cap is
# ten times the unmutated run, which moves with the tree's speed and not with
# the mutants': under debug mode the four mutants that let an oversized input
# through to a parser run 65 to 79 seconds against baselines of 2 and 5, and
# the default ended them where the tests would have. ``--minimum-timeout`` is
# the knob that raises it. Ten minutes is seven times the slowest run measured,
# so it ends only a run that would not end; a mutant that hangs costs this
# once, and none does today.
CPP_MUTANT_CAP_MS = 600_000


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


# The kill-route census of the C++ sweep, beside the Elements report.
CPP_ROUTES_REPORT = "cpp-routes.json"
# The lane's list of the mutants no test observes by behaviour, beside
# ``cpp.json``: each killed by a check the standard library runs in the
# mutation build or by a signal, with its site, so that the changes running
# straight into an operation the language does not define are named and not
# only counted.
CPP_UNOBSERVED_REPORT = "cpp-unobserved.json"


def cpp_endings(artifact_dir: Path, legs: Sequence[CppLeg]) -> list[dict[str, Ending]] | None:
    """Read each leg's endings, or None where a leg wrote no SQLite report."""
    paths = [artifact_dir / f"{leg.report_name}.sqlite" for leg in legs]
    if not all(path.is_file() for path in paths):
        return None
    return [lane_endings(path) for path in paths]


def cpp_unobserved_rows(artifact_dir: Path) -> dict[UnobservedKey, int] | None:
    """Read the run's unobserved kills by identity, or None where the run wrote none.

    From the artifact the lane wrote rather than from the reports again, so
    what the record is compared against is exactly what the run published and a
    re-take is a copy.
    """
    report = artifact_dir / CPP_UNOBSERVED_REPORT
    if not report.is_file():
        return None
    ledger = cast("list[UnobservedRow]", json.loads(report.read_text(encoding="utf-8")))
    return unobserved_ledger_to_rows(ledger)


def recorded_total_mutants() -> int | None:
    """Read the mutants the recorded census counted, or None where none is recorded."""
    baseline = cast(
        "Mapping[str, object]",
        load_spec().get("bindings", {}).get("cpp", {}).get("baseline", {}),
    )
    return cast("int | None", baseline.get("total_mutants"))


def _off_record(total: int) -> str | None:
    """Refuse a union of the slices off the recorded census, either way.

    Short of the record is what a hole in the slices reads as, a slice that
    carried fewer files than the partition gave it.  Past it, or short by a
    deliberate removal, is a surface that moved, and the change that moved it
    records the new census in the same commit, as it does the survivors.
    """
    recorded = recorded_total_mutants()
    if recorded is None or total == recorded:
        return None
    return (
        f"the slices union to {total} mutants, where the record holds "
        f"{recorded}: either a slice carried fewer files than the partition gave it, or the "
        "surface moved and docs/MUTATION_BENCH.yaml records the new census in the same commit"
    )


def _scored(report: dict[str, object]) -> dict[str, object]:
    """Give a unioned report the score its own mutants carry.

    Mull writes the score of the sweep that produced a report, and a union
    produces a report no sweep did: each slice scored its own share of the
    surface.  Left alone the field keeps the first input's score, which is
    what the Elements viewer renders and what a reader of the artifact
    believes.
    """
    total, survived = elements_counts(report)
    report["mutationScore"] = round(100.0 * (total - survived) / total, 2) if total else 0.0
    return report


def union_slices(reports: Sequence[Mapping[str, object]]) -> dict[str, object] | str:
    """Union the slices into the lane's census, or name a mutant two of them carry.

    The slices partition the files, so their mutants are disjoint by
    construction, and an identifier arriving twice is a file no slice held
    out: mutated by all of them, and so mutated under identifiers that arrive
    once per slice.  That is the shape a file missing from the partition takes
    here, and refusing it is why the slices state what they hold out rather
    than what they claim.
    """
    merged: dict[str, object] = copy.deepcopy(dict(reports[0]))
    files: dict[str, dict[str, object]] = {}
    carried: dict[str, int] = {}
    for number, report in enumerate(reports, 1):
        entries = cast("Mapping[str, Mapping[str, object]]", report.get("files", {}))
        for path, entry in entries.items():
            mutants = cast("list[Mapping[str, object]]", entry.get("mutants", []))
            for mutant in mutants:
                identifier = str(mutant["id"])
                first = carried.get(identifier)
                if first == number:
                    return f"slice {number} carries {identifier} twice in {path}"
                if first is not None:
                    return (
                        f"slices {first} and {number} both carry {identifier} in {path}: "
                        "no slice held that file out, so the partition never claimed it, "
                        "which is what a file the tree does not track looks like from here"
                    )
                carried[identifier] = number
            if path not in files:
                files[path] = {**copy.deepcopy(dict(entry)), "mutants": []}
            cast("list[object]", files[path]["mutants"]).extend(copy.deepcopy(mutants))
    merged["files"] = files
    return _scored(merged)


def cpp_lane_command(
    mull_runner: str, build_dir: Path, artifact_dir: Path, leg: CppLeg, *, dry_run: bool = False
) -> list[str]:
    """Build the runner's argv for one leg, the test binary's own argv behind ``--``.

    A dry run runs the unmutated binary once and reports every mutant the
    binary carries without running one.
    """
    return [
        mull_runner,
        str(build_dir / CPP_TEST_TARGET),
        *(["--dry-run"] if dry_run else []),
        "--reporters=IDE",
        "--reporters=Elements",
        # The SQLite report keeps each mutant's exit status and the test
        # binary's own output, which is what tells a kill by a test's
        # assertion from one by a fault.
        "--reporters=SQLite",
        f"--report-dir={artifact_dir}",
        f"--report-name={leg.report_name}",
        f"--minimum-timeout={CPP_MUTANT_CAP_MS}",
        # Everything past this marker is the test binary's own argv.
        # Catch2 shuffles its cases by default under a seed that changes
        # every run, and mull runs the binary once per mutant, so an
        # unpinned lane reads a different census each sweep: two pinned
        # sweeps of one tree agreed on every mutant, where two shuffled
        # ones read the fault route at 98 and 99 against the pinned 93.
        # A fault ends the process, so the order decides which test
        # reports before the run stops. Pinning makes the recorded census
        # a measurement rather than a sample.
        "--",
        "--order",
        "decl",
        # A run ends at its first failing assertion. The kill-route census
        # reads a run with any failing assertion as the test's kill,
        # whatever ended the process after it, and a run with none goes
        # through the whole suite either way, so no mutant's route moves.
        "--abort",
    ]


def _run_cpp_lane(
    mull_runner: str,
    paths: LegPaths,
    leg: CppLeg,
) -> tuple[str, tuple[int, int] | None]:
    """Run one leg's built tree under mull-runner, returning its log and its (killed, survived)."""
    # The runner is given the sweep's own environment, nothing of the caller's
    # but its search path and temp directory; SweepEnvironment says what it
    # holds and why. The IDE reporter
    # prints the summary the counts are read from; the Elements reporter
    # writes every mutant with its status and site, which is what the ledger
    # is checked against.
    runner_proc = run_streaming(
        cpp_lane_command(mull_runner, paths.build_dir, paths.artifact_dir, leg),
        cwd=paths.cpp_root,
        env=cpp_sweep_environment(leg, paths.build_dir).variables(),
    )
    raw = f"=== mull-runner-23 ({leg}) ===\n" + runner_proc.stdout + "\n"
    reaped = reap_dead_scratch_dirs()
    raw += f"scratch directories left by killed runs and removed: {reaped}\n"
    # Mull's own summary goes to the IDE report, and its stdout carries the
    # survivor count only when there is one: a leg that killed everything
    # says so in the report alone, so the report is part of the leg's log.
    ide_report = paths.artifact_dir / f"{leg.report_name}.txt"
    if ide_report.is_file():
        raw += ide_report.read_text(encoding="utf-8") + "\n"
    return raw, mull_counts(raw)


# A search path, as PATH holds it.
SearchPath = NewType("SearchPath", str)

# The locale every sweep runs under, a UTF-8 one whatever the caller's. The
# kernel's FFI decodes the text it is handed with the process's locale, and
# under C or POSIX a test of non-ASCII input reads another verdict.
CPP_SWEEP_LOCALE: Literal["C.UTF-8"] = "C.UTF-8"


class SweepEnvironment(NamedTuple):
    """The whole environment a leg's runner is given: of the caller's, its search path and temp dir.

    The search path finds the runner, and taskset where a sweep is pinned, and
    the locale is pinned.  The temp directory is the one the scratch reaper sweeps, so
    what a run a fault ended leaves behind is where the reaper looks.  The
    repository root is where the folded integration tests read their fixtures
    and the kernel library: Mull runs the binary directly, where ctest would
    pass the root, and without it every mutant would read killed, the tests
    dying at setup.  The configuration is the one the tree
    was built under, named because the runner reads the cap on its unmutated
    runs from it and, left to find one from its working directory upward, a
    sliced leg would run under the tree's own; the cap per mutant is on the
    command line, for the reason at CPP_MUTANT_CAP_MS.  Anything else the
    caller had set would change what a sweep reports with nothing in the sweep
    saying so: with ALETHEIA_LIB the library lookup returns before it reads
    the repository root, leaving that read's mutants uncovered, and the GHC
    runtime's options change how a run ends.
    PYTHONUNBUFFERED is the one variable that says nothing of the sweep:
    run_streaming gives it to every child it starts, the lane's runner
    included, and it is spelled here so every runner gets the same.
    """

    search_path: SearchPath
    locale: Literal["C.UTF-8"]
    temp_dir: Path
    repo_root: Path
    config: Path

    def variables(self) -> dict[str, str]:
        """Spell the environment as subprocess takes it, which is the one place it is spelled so."""
        return {
            "PATH": self.search_path,
            "LC_ALL": self.locale,
            "TMPDIR": str(self.temp_dir),
            "ALETHEIA_REPO_ROOT": str(self.repo_root),
            "MULL_CONFIG": str(self.config),
            "PYTHONUNBUFFERED": "1",
        }


def cpp_sweep_directory() -> Path:
    """Name the directory every leg's runner is started in."""
    return REPO_ROOT / "cpp"


def cpp_sweep_environment(leg: CppLeg, build_dir: Path) -> SweepEnvironment:
    """Build a leg's sweep environment from the caller's search path and temp directory."""
    search_path = SearchPath(os.environ.get("PATH") or os.defpath)
    config = leg_config_path(leg, build_dir)
    return SweepEnvironment(search_path, CPP_SWEEP_LOCALE, scratch_root(), REPO_ROOT, config)


def _sweep_cpp_lane(
    cmake: str,
    mull_runner: str,
    build_dir: Path,
    artifact_dir: Path,
    leg: CppLeg,
) -> tuple[str, Mapping[str, object] | str]:
    """Build and sweep one leg, returning its log and its report or the reason it has none.

    Beside Mull's reports the leg writes the suite runs its mutants cost by
    file, which only its own log can say, since the unmutated run they are
    counted in is printed there and nowhere else.
    """
    raw = f"=== {leg} leg ===\n"
    config = leg_config(leg, build_dir)
    raw += f"configuration: {config}\n"
    paths = LegPaths(cpp_sweep_directory(), build_dir, artifact_dir, config)
    built = build_cpp_mutation_tree(cmake, paths)
    if isinstance(built, MutationReport):
        return raw + built.raw_log, built.error or f"the {leg} leg did not build"
    raw += built
    lane_raw, counts = _run_cpp_lane(mull_runner, paths, leg)
    raw += lane_raw
    if counts is None:
        return raw, f"could not parse the {leg} leg's mull-runner-23 summary (see cpp.raw.txt)"
    report_path = artifact_dir / f"{leg.report_name}.json"
    if not report_path.is_file():
        return raw, f"the {leg} leg wrote no {report_path.name}"
    runs = leg_runs(artifact_dir / f"{leg.report_name}.sqlite", MullLog(lane_raw))
    if not isinstance(runs, dict):
        return raw, f"the {leg} leg: {runs}"
    runs_path = artifact_dir / f"{leg.report_name}{CPP_LEG_RUNS_SUFFIX}"
    _ = runs_path.write_text(json.dumps(runs, indent=2), encoding="utf-8")
    return raw, cast("Mapping[str, object]", json.loads(report_path.read_text(encoding="utf-8")))


def run_cpp(artifact_dir: Path) -> MutationReport:
    """Mull pass over the mutation tree, whole or as the stage names it.

    The stage (``cpp_stage``) selects the whole lane, one leg or the merge.
    """
    try:
        stage = cpp_stage()
    except ValueError as exc:
        return MutationReport("cpp", "mull", 0, 0, "", error=str(exc))
    if stage == CPP_MERGE_STAGE:
        return _merge_cpp_legs(artifact_dir)
    # A leg reports under its own binding whatever becomes of it, so a leg that
    # never reached its sweep says which leg it was.
    legs = [CppLeg()] if stage is None else [stage]
    binding = "cpp" if stage is None else stage.binding
    checked = _check_cpp_tools()
    if isinstance(checked, str):
        return MutationReport(binding, "mull", 0, 0, "", error=checked)
    raw, swept = _sweep_legs(checked, artifact_dir, legs)
    if isinstance(swept, str):
        return MutationReport(binding, "mull", 0, 0, raw, error=swept)

    if stage is not None:
        # One leg: its result is its own slice of the tree, judged by nobody
        # until the merge has read every slice.
        total, survived = elements_counts(swept[0])
        raw += f"=== {stage} leg ===\nkilled {total - survived}, survived {survived}"
        raw += f" of {total}\n"
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        return MutationReport(binding, "mull", total - survived, survived, raw)
    return _finish_cpp(artifact_dir, raw, dict(swept[0]), legs)


def _sweep_legs(
    cpp_tools: tuple[str, str], artifact_dir: Path, legs: Sequence[CppLeg]
) -> tuple[str, list[Mapping[str, object]] | str]:
    """Sweep the legs given, returning the log and their reports or the reason there are none.

    The whole lane is the tree swept whole; a CI leg is one slice of it.
    The log is written out after each leg, so a run its clock kills leaves
    what it reached.
    """
    cmake, mull_runner = cpp_tools
    raw = ""
    reports: list[Mapping[str, object]] = []
    for leg in legs:
        lane_raw, outcome = _sweep_cpp_lane(
            cmake, mull_runner, cpp_sweep_directory() / leg.directory, artifact_dir, leg
        )
        raw += lane_raw
        (artifact_dir / "cpp.raw.txt").write_text(raw)
        if isinstance(outcome, str):
            return raw, outcome
        reports.append(outcome)
    return raw, reports


def _merge_cpp_legs(artifact_dir: Path) -> MutationReport:
    """Merge the legs' reports found under the directory ``CPP_LEGS_ENV`` names.

    Each leg's three reports and its runs are wanted exactly once under that
    directory, wherever the download put them; a leg with one missing did not
    finish, and the lane has no verdict without it.
    """
    legs = os.environ.get(CPP_LEGS_ENV, "")
    if not legs:
        msg = f"{CPP_STAGE_ENV}=merge reads the legs' reports from {CPP_LEGS_ENV}, which is unset"
        return MutationReport("cpp", "mull", 0, 0, "", error=msg)
    legs_dir = Path(legs)
    raw = f"=== merge of the legs under {legs_dir} ===\n"
    slices: list[Mapping[str, object]] = []
    for leg in sliced_legs():
        copied = _copy_leg_reports(legs_dir, artifact_dir, leg)
        if isinstance(copied, str):
            return MutationReport("cpp", "mull", 0, 0, raw + copied + "\n", error=copied)
        raw += copied.log
        slices.append(copied.elements)
    unioned = union_slices(slices)
    if isinstance(unioned, str):
        return MutationReport("cpp", "mull", 0, 0, raw + unioned + "\n", error=unioned)
    counts = elements_counts(unioned)
    off = _off_record(counts.total)
    if off is not None:
        return MutationReport("cpp", "mull", 0, 0, raw + off + "\n", error=off)
    raw += f"the {CPP_SLICES} slices union to {counts.total} mutants\n"
    elapsed = _legs_elapsed(legs_dir)
    if isinstance(elapsed, str):
        return MutationReport("cpp", "mull", 0, 0, raw + elapsed + "\n", error=elapsed)
    (artifact_dir / CPP_LEGS_REPORT).write_text(
        json.dumps({str(leg): secs for leg, secs in elapsed.items()}, indent=2)
    )
    for leg, secs in elapsed.items():
        raw += f"{leg} leg swept in {secs}s\n"
    return _finish_cpp(artifact_dir, raw, unioned, sliced_legs())


class LegReports(NamedTuple):
    """What one leg contributed to the merge: the log lines and its Elements report."""

    log: str
    elements: Mapping[str, object]


def _copy_leg_reports(legs_dir: Path, artifact_dir: Path, leg: CppLeg) -> LegReports | str:
    """Copy one leg's reports and its runs beside the merge, or say which is not there once."""
    log = ""
    for suffix in (*CPP_LEG_REPORT_SUFFIXES, CPP_LEG_RUNS_SUFFIX):
        name = leg.report_name + suffix
        found = sorted(legs_dir.rglob(name))
        if len(found) != 1:
            return f"the {leg} leg: {len(found)} copies of {name} under {legs_dir}, wanted one"
        _ = shutil.copyfile(found[0], artifact_dir / name)
        log += f"{leg} leg: {found[0]}\n"
    report_path = artifact_dir / (leg.report_name + ".json")
    elements = cast("Mapping[str, object]", json.loads(report_path.read_text(encoding="utf-8")))
    return LegReports(log, elements)


def _legs_elapsed(legs_dir: Path) -> dict[CppLeg, float] | str:
    """Read each leg's wall clock from the summary its run wrote, or say what is wrong.

    Every leg's summary must be there, once, and must record the commit this
    merge runs at: the legs of another commit merge into a verdict about
    nothing.
    """
    commit = short_sha(REPO_ROOT)
    elapsed: dict[CppLeg, float] = {}
    for summary_path in sorted(legs_dir.rglob("summary.json")):
        summary = cast("Mapping[str, object]", json.loads(summary_path.read_text(encoding="utf-8")))
        runs = cast("list[Mapping[str, object]]", summary.get("runs", []))
        secs = cast("Mapping[str, float]", summary.get("elapsed_s", {})).get("cpp")
        legs = [leg for run in runs if (leg := leg_of_binding(str(run.get("binding")))) is not None]
        if not legs or secs is None:
            continue
        if summary.get("commit") != commit:
            return f"{summary_path} is a run at {summary.get('commit')}, this merge is at {commit}"
        if legs[0] in elapsed:
            return f"{summary_path} is a second {legs[0]} leg"
        elapsed[legs[0]] = secs
    missing = [str(leg) for leg in sliced_legs() if leg not in elapsed]
    if missing:
        return f"no summary of the {', '.join(missing)} leg under {legs_dir}"
    return elapsed


def _finish_cpp(
    artifact_dir: Path, raw: str, report: dict[str, object], legs: Sequence[CppLeg]
) -> MutationReport:
    """Write the lane's report, count the kill routes and the surface, and write the lane's log.

    The report is written scored over its own mutants, here as well as at the
    union, so the whole tree's report and the merged slices' carry the one
    score computed one way.
    """
    scored = _scored(copy.deepcopy(report))
    (artifact_dir / CPP_ELEMENTS_REPORT).write_text(json.dumps(scored))
    total, survived = elements_counts(scored)
    endings = cpp_endings(artifact_dir, legs)
    routes = merge_endings(endings) if endings is not None else None
    # A mutant the runner ended at its cap is neither killed nor survived: the
    # census names it, and the drift gate refuses the sweep.
    timeouts = routes["timeout"] if routes is not None else None
    killed = total - survived - (timeouts or 0)
    raw += "=== merged ===\n"
    raw += f"killed {killed}, survived {survived}, timed out {timeouts} of {total}\n"
    if endings is not None and routes is not None:
        (artifact_dir / CPP_ROUTES_REPORT).write_text(json.dumps(routes, indent=2))
        raw += "routes: " + ", ".join(f"{route} {count}" for route, count in routes.items()) + "\n"
        unobserved = unobserved_rows_to_ledger(unobserved_kill_rows(endings, _repo_line))
        (artifact_dir / CPP_UNOBSERVED_REPORT).write_text(json.dumps(unobserved, indent=2))
        raw += unobserved_summary(unobserved)
    runs = lane_runs(artifact_dir, legs)
    (artifact_dir / CPP_RUNS_REPORT).write_text(json.dumps(runs, indent=2))
    raw += weight_drift(runs)
    (artifact_dir / "cpp.raw.txt").write_text(raw)
    # Every mutant the runner made has a row, so a file with runs is a file
    # holding a mutant, whatever became of it.
    mutated = frozenset(runs)
    census = None if routes is None else {KillRoute(r): MutantCount(c) for r, c in routes.items()}
    return MutationReport(
        "cpp",
        "mull",
        killed,
        survived,
        raw,
        observed=Observed(timeouts, routes=census, mutated_files=mutated),
    )


def unobserved_summary(unobserved: Sequence[UnobservedRow]) -> str:
    """Say which mutants no test observes by behaviour, and what ended each.

    The count is the census's ``check`` and ``fault`` routes together; the rows
    are what the count cannot say, and each names a line the suite reports
    nothing about before the process stops.
    """
    total = sum(row["count"] for row in unobserved)
    checks = sum(row["count"] for row in unobserved if row["route"] == "check")
    lines = [
        (
            f"no test observes {total} mutants by behaviour: "
            f"{checks} end at a library check, {total - checks} by a signal"
        )
    ]
    lines.extend(
        f"  {row['file']} {row['mutator']}"
        + (f" x{row['count']}" if row["count"] > 1 else "")
        + f": {row['refused'] or row['route']} | {row['text']}"
        for row in unobserved
    )
    return "\n".join(lines) + "\n"


def mull_counts(raw: str) -> tuple[int, int] | None:
    """Read ``(killed, survived)`` from a leg's log, or None if it carries no summary.

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

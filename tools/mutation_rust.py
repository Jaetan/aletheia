# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust lane: cargo-mutants over the crate's hot path, in shards over copies of the tree.

cargo-mutants rewrites one function at a time, builds the crate's tests and
runs them, and writes each mutant's verdict to ``mutants.out/outcomes.json``
under the directory ``--output`` names; the lane reads that file rather than
the console, which prints only what was missed.  Which files it mutates and
which features it turns on are ``rust/.cargo/mutants.toml``, read from the
crate, so every sweep makes one set.

The sweep mutates scratch copies of the whole tree, ``HEAD`` with the
uncommitted diff applied (``scratch_worktree``), and runs ``--in-place``
within each, one mutant at a time per copy: the sweep is cut into shards
that run side by side, one copy each (``rust_shards``), and their outcomes
are merged into the one ``outcomes.json`` the survivor ledger reads.  The
copy cargo-mutants would make itself
holds the crate alone, and the suite includes the DBC corpus and the parity
snapshots under ``python/`` at compile time and reads the documents under
``docs/`` at run time, so a copy of the crate alone does not build.  The
tree itself never holds a mutant: a hook, a probe run or a build reading it
while a sweep runs sees the sources as they stand.  The suite loads the
tree's own ``build/libaletheia-ffi.so``, which the copy does not carry, so
the kernel is not rebuilt while a sweep runs.

The tool is pinned to the version ``docs/MUTATION_BENCH.yaml`` records and
refused at any other, because two releases generate different mutant sets
and a baseline is a count of one set.

A survivor is keyed as the C++ ledger keys one: the mutation cargo-mutants
names, less its position, the repository-relative file, and the text of the
line the mutation starts on.
"""

from __future__ import annotations

import collections
import contextlib
import json
import os
import re
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict, cast

from tools._common import WorkerCount, find_executable, run_capture, run_streaming, short_sha
from tools._resources import detect_cpus
from tools.mutation_go import ShortSha
from tools.mutation_report import (
    MutantCount,
    MutationReport,
    Observed,
    load_spec,
    scratch_tree_or_report,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

    from tools._common import ExecutorFactory
    from tools.mutation_report import SurvivorKey

REPO_ROOT = Path(__file__).resolve().parent.parent
# The crate, relative to the root of a tree: the sweep's is the scratch copy's.
CRATE = Path("rust")

# Where the sweep's own report directory lands under the run's artifact
# directory: ``<artifact_dir>/rust/mutants.out/``.
RUST_OUTPUT_DIR = "rust"
OUTCOMES = Path(RUST_OUTPUT_DIR) / "mutants.out" / "outcomes.json"

# Shards a sweep runs side by side, each in a scratch copy of its own.  A copy
# holds one mutant at a time, and a mutant's cost is the incremental build of
# the crate's test binary, 2.02 s of its 2.24 s on the runner, which leaves the
# runner's other cores idle; cargo-mutants deals its mutants to the shards
# round-robin, so the shards partition the list it would sweep whole.
RUST_SHARDS_CAP = 4

# The profile setting the sweep builds under: no debug information
# (``run_rust``).
SWEEP_DEBUG_VAR = "CARGO_PROFILE_DEV_DEBUG"
SWEEP_DEBUG = "0"

# The stage a Rust lane runs at: unset sweeps the crate whole in one process;
# a job number sweeps that job's part of a sweep spread over CI jobs; `merge`
# merges the jobs' sweeps, read from the directory the second variable names.
RUST_STAGE_ENV = "ALETHEIA_MUTATION_RUST_STAGE"
RUST_JOBS_ENV = "ALETHEIA_MUTATION_RUST_JOBS"
RUST_MERGE_STAGE = "merge"

# Jobs a CI sweep is spread over, and the shards each runs side by side.  Both
# are fixed, whatever CPUs a job is given: every job deals the same number of
# shards, which is what makes the jobs' shards partition the listing.
RUST_JOBS = 2
RUST_JOB_SHARDS = 4

# Beside a job's reports, the listing it swept its part of, which the merge
# holds the jobs to.
RUST_LISTING = "rust-listing.json"

# A job of a sweep spread over CI jobs, numbered from one, and the binding a
# report carries: the lane's, ``rust``, or one job's, ``rust-1``.
RustJob = NewType("RustJob", int)
RustBinding = NewType("RustBinding", str)
RUST_LANE = RustBinding("rust")

# One shard of a sweep, numbered from zero as cargo-mutants numbers them, and how many a sweep runs.
RustShard = NewType("RustShard", int)
ShardCount = NewType("ShardCount", int)

# What ``cargo mutants --list --json`` printed.
CargoListing = NewType("CargoListing", str)

# A mutant's identity, as the listing and an outcome both spell it.
MutantKey = NewType("MutantKey", str)

# A file of the crate, a mutation's name, and a position in the file, as
# cargo-mutants reports them.
CrateFile = NewType("CrateFile", str)
MutationName = NewType("MutationName", str)
SourceIndex = NewType("SourceIndex", int)

# An outcome's bucket: caught, missed, unviable, timed out, or the baseline's success.
OutcomeSummary = NewType("OutcomeSummary", str)


class SourcePosition(TypedDict):
    """A line and a column of a crate file, from one."""

    line: SourceIndex
    column: SourceIndex


class SourceSpan(TypedDict):
    """The text a mutation replaces, from its first position to its last."""

    start: SourcePosition
    end: SourcePosition


class ListedMutant(TypedDict):
    """A mutant as ``cargo mutants --list --json`` and an outcome's scenario both spell it."""

    file: CrateFile
    name: MutationName
    span: SourceSpan


class MutantScenario(TypedDict):
    """An outcome's scenario where it is a mutant rather than the baseline."""

    Mutant: ListedMutant


class MutantOutcome(TypedDict):
    """One outcome: the scenario it ran, and the bucket it landed in."""

    scenario: MutantScenario | Literal["Baseline"]
    summary: OutcomeSummary


class SweepOutcomes(TypedDict):
    """The part of ``outcomes.json`` the lane reads and the merge writes."""

    outcomes: list[MutantOutcome]
    total_mutants: MutantCount
    caught: MutantCount
    missed: MutantCount
    timeout: MutantCount
    unviable: MutantCount
    success: MutantCount


_OUTCOME_COUNTS: tuple[
    Literal["total_mutants", "caught", "missed", "timeout", "unviable", "success"], ...
] = (
    "total_mutants",
    "caught",
    "missed",
    "timeout",
    "unviable",
    "success",
)


# ``cargo mutants --version`` prints the tool's name and its version.
_VERSION_RE = re.compile(r"cargo-mutants\s+(\d+\.\d+\.\d+)")
# A mutant's name opens on its position, ``src/file.rs:LINE:COL: ``, and the
# rest names the mutation; the ledger keys on the rest.
_POSITION_RE = re.compile(r"^[^:]+:\d+:\d+:\s*")


def cargo_mutants_version(text: str) -> str | None:
    """Read the version out of ``cargo mutants --version``, or None where it is not one."""
    match = _VERSION_RE.search(text)
    return match.group(1) if match else None


def _check_rust_tools(pinned: str | None) -> tuple[str, Path] | str:
    """Return ``(cargo, lib)`` when the Rust lane can run, else an error string."""
    try:
        cargo = find_executable("cargo")
    except RuntimeError as exc:
        return str(exc)
    version = run_capture([cargo, "mutants", "--version"])
    found = cargo_mutants_version(version.stdout) if version.returncode == 0 else None
    if found is None:
        return "cargo-mutants is not installed: cargo install cargo-mutants --locked"
    if pinned is not None and found != pinned:
        return f"cargo-mutants {found} is installed where the record pins {pinned}"
    lib = REPO_ROOT / "build" / "libaletheia-ffi.so"
    if not lib.is_file():
        return f"libaletheia-ffi.so not found at {lib}; run `cabal run shake -- build` first"
    return (cargo, lib)


def _pinned_version() -> str | None:
    """Read the cargo-mutants version the record pins, or None where it pins none."""
    spec = load_spec().get("bindings", {}).get("rust", {})
    version = cast("Mapping[str, object]", spec).get("version")
    return version if isinstance(version, str) else None


def rust_shards() -> ShardCount:
    """Return how many shards a sweep runs: one per CPU the process was given, up to the cap."""
    return ShardCount(max(1, min(detect_cpus(), RUST_SHARDS_CAP)))


def rust_stage() -> RustJob | Literal["merge"] | None:
    """Read the stage this process runs at, or raise ValueError naming what it was given."""
    stage = os.environ.get(RUST_STAGE_ENV, "")
    if not stage:
        return None
    if stage == RUST_MERGE_STAGE:
        return RUST_MERGE_STAGE
    if stage.isdigit() and 1 <= int(stage) <= RUST_JOBS:
        return RustJob(int(stage))
    msg = f"{RUST_STAGE_ENV}={stage!r} is not a job of 1 to {RUST_JOBS} or {RUST_MERGE_STAGE!r}"
    raise ValueError(msg)


def job_binding(job: RustJob) -> RustBinding:
    """Name the binding one job reports under: ``rust-1`` and its sibling."""
    return RustBinding(f"rust-{job}")


def is_rust_job(binding: RustBinding) -> bool:
    """Say whether a report is one job's part of a sweep, which the merge judges."""
    return binding in {job_binding(RustJob(n)) for n in range(1, RUST_JOBS + 1)}


class JobRun(TypedDict):
    """The part of a run's entry in ``summary.json`` the merge reads: its binding."""

    binding: RustBinding


class JobSummary(TypedDict):
    """The part of a job's ``summary.json`` the merge reads: the commit and the runs."""

    commit: ShortSha
    runs: list[JobRun]


class ShardPlan(NamedTuple):
    """The shards a process sweeps, and how many the whole sweep deals."""

    numbers: tuple[RustShard, ...]
    total: ShardCount


def shard_plan(job: RustJob | None) -> ShardPlan:
    """Give a process its shards: all of a whole sweep, or a job's run of the jobs' total."""
    if job is None:
        shards = rust_shards()
        return ShardPlan(tuple(RustShard(n) for n in range(shards)), shards)
    first = (job - 1) * RUST_JOB_SHARDS
    numbers = tuple(RustShard(n) for n in range(first, first + RUST_JOB_SHARDS))
    return ShardPlan(numbers, ShardCount(RUST_JOBS * RUST_JOB_SHARDS))


def shard_log(artifact_dir: Path, number: RustShard) -> Path:
    """Name the log one shard's sweep streams to."""
    return artifact_dir / f"rust-shard-{number}.raw.txt"


def shard_output(artifact_dir: Path, number: RustShard) -> Path:
    """Name the directory one shard's cargo-mutants writes its ``mutants.out`` under."""
    return artifact_dir / RUST_OUTPUT_DIR / f"shard-{number}"


def run_rust(
    artifact_dir: Path, *, executor: ExecutorFactory = ThreadPoolExecutor
) -> MutationReport:
    """Sweep the crate's hot path with cargo-mutants, in shards side by side in scratch copies.

    The stage (``rust_stage``) selects the whole sweep, one job's part of it,
    or the merge of the jobs' parts, which needs no cargo.  ``executor`` builds
    what the shards run on: a thread pool by default, and in a test an executor
    that runs each shard on the test's own thread.
    """
    try:
        stage = rust_stage()
    except ValueError as exc:
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, "", error=str(exc))
    if stage == RUST_MERGE_STAGE:
        return merge_rust_jobs(artifact_dir)
    binding = RUST_LANE if stage is None else job_binding(stage)
    checked = _check_rust_tools(_pinned_version())
    if isinstance(checked, str):
        return MutationReport(binding, "cargo-mutants", 0, 0, "", error=checked)
    cargo, lib = checked
    # The suite loads the kernel through ALETHEIA_LIB, as every other run of it
    # does; the path is absolute because cargo-mutants runs the tests from
    # the scratch copy's crate, and the copy carries no build.
    env = dict(os.environ)
    env["ALETHEIA_LIB"] = str(lib)
    # The sweep's builds carry no debug information: a mutant's cost is the
    # incremental build of the crate's tests, and swept in four shards on four
    # CPUs the lane took 360.8 s without it against 479.4 s with it, to the
    # same verdict.  Set for the sweep alone, so every other build of the
    # crate keeps its profile.
    env[SWEEP_DEBUG_VAR] = SWEEP_DEBUG
    plan = shard_plan(stage)
    with contextlib.ExitStack() as stack:
        trees = _scratch_trees(stack, plan)
        if isinstance(trees, MutationReport):
            return trees
        listing = run_capture(
            [cargo, "mutants", "--list", "--json"], cwd=trees[plan.numbers[0]] / CRATE, env=env
        )
        (artifact_dir / RUST_OUTPUT_DIR).mkdir(parents=True, exist_ok=True)
        _ = (artifact_dir / RUST_LISTING).write_text(listing.stdout, encoding="utf-8")

        def sweep(number: RustShard) -> ExitStatus:
            # Streams to the shard's own log, so a sweep killed by a wall clock
            # still leaves how far each shard got.  Colours off, so the log is
            # the text it printed.
            with shard_log(artifact_dir, number).open("w", encoding="utf-8", buffering=1) as log:
                proc = run_streaming(
                    [
                        cargo,
                        "mutants",
                        "--in-place",
                        "--colors",
                        "never",
                        "--shard",
                        f"{number}/{plan.total}",
                        "--output",
                        str(shard_output(artifact_dir, number)),
                    ],
                    cwd=trees[number] / CRATE,
                    env=env,
                    sink=log.write,
                )
            return ExitStatus(proc.returncode)

        exits = _sweep_shards(executor, plan, sweep)
    return _finish_rust(artifact_dir, binding, plan, CargoListing(listing.stdout), exits)


def _sweep_shards(
    executor: ExecutorFactory, plan: ShardPlan, sweep: Callable[[RustShard], ExitStatus]
) -> list[ExitStatus]:
    """Run every shard of the plan side by side on what ``executor`` builds; return their exits."""
    with executor(WorkerCount(len(plan.numbers))) as pool:
        return list(pool.map(sweep, plan.numbers))


def _scratch_trees(
    stack: contextlib.ExitStack[bool | None], plan: ShardPlan
) -> dict[RustShard, Path] | MutationReport:
    """Make one scratch copy of the tree per shard, each removed when the stack closes."""
    trees: dict[RustShard, Path] = {}
    for number in plan.numbers:
        tree = stack.enter_context(scratch_tree_or_report(REPO_ROOT, "rust", "cargo-mutants"))
        if isinstance(tree, MutationReport):
            return tree
        trees[number] = tree
    return trees


def _finish_rust(
    artifact_dir: Path,
    binding: RustBinding,
    plan: ShardPlan,
    listing: CargoListing,
    exits: list[ExitStatus],
) -> MutationReport:
    """Join the shards' logs, merge their outcomes, and read the report.

    A whole sweep's merge is the lane's ``outcomes.json``, held to the whole
    listing.  A job's part is held only to what the listing names, every
    listed mutant being the merge's to account for, and is recorded and not
    judged.
    """
    raw = "".join(shard_log(artifact_dir, n).read_text(encoding="utf-8") for n in plan.numbers)
    (artifact_dir / f"{binding}.raw.txt").write_text(raw)
    whole = binding == RUST_LANE
    merged = _merge_shards(artifact_dir, plan.numbers, listing, whole=whole)
    if not isinstance(merged, dict):
        return MutationReport(binding, "cargo-mutants", 0, 0, raw, error=merged)
    if whole:
        outcomes_path = artifact_dir / OUTCOMES
        outcomes_path.parent.mkdir(parents=True, exist_ok=True)
        _ = outcomes_path.write_text(json.dumps(merged, indent=2), encoding="utf-8")
    exit_list = ", ".join(str(code) for code in exits)
    return parse_outcomes(merged, raw, f"exits {exit_list}", binding)


def mutant_key(mutant: ListedMutant) -> MutantKey:
    """Spell a mutant's identity: its file, its mutation and the span it replaces."""
    return MutantKey(json.dumps([mutant["file"], mutant["name"], mutant["span"]], sort_keys=True))


def merge_shard_outcomes(
    listed: list[ListedMutant], shards: list[SweepOutcomes], *, whole: bool = True
) -> SweepOutcomes | Prose:
    """Merge the shards' outcomes into one, or say why they are not the listed sweep.

    Every listed mutant must have one outcome across the shards, and no
    outcome may name a mutant the listing does not: a shard that swept the
    wrong part, or swept a part twice, is refused rather than counted.  A part
    of a sweep (``whole`` false) is held to the second and to no mutant twice,
    the rest of the listing being other jobs'.  The merged file keeps the
    first shard's baseline and every shard's mutants, and sums the buckets, so
    it reads as one whole sweep's would.
    """
    seen: collections.Counter[MutantKey] = collections.Counter()
    for shard in shards:
        for outcome in shard["outcomes"]:
            scenario = outcome["scenario"]
            if scenario != "Baseline":
                seen[mutant_key(scenario["Mutant"])] += 1
    twice = sorted(key for key, count in seen.items() if count > 1)
    if twice:
        return Prose(
            f"{len(twice)} mutants have an outcome in more than one shard, first {twice[0]}"
        )
    wanted = {mutant_key(mutant) for mutant in listed}
    if set(seen) != wanted and (whole or not set(seen) <= wanted):
        return Prose(
            f"the shards swept {len(seen)} mutants where the listing has {len(wanted)}: "
            + f"{len(wanted - set(seen))} unswept, {len(set(seen) - wanted)} not listed"
        )
    baseline = [outcome for outcome in shards[0]["outcomes"] if outcome["scenario"] == "Baseline"]
    mutants = [
        outcome
        for shard in shards
        for outcome in shard["outcomes"]
        if outcome["scenario"] != "Baseline"
    ]
    merged: SweepOutcomes = {
        "outcomes": baseline + mutants,
        "total_mutants": MutantCount(0),
        "caught": MutantCount(0),
        "missed": MutantCount(0),
        "timeout": MutantCount(0),
        "unviable": MutantCount(0),
        "success": MutantCount(0),
    }
    for name in _OUTCOME_COUNTS:
        merged[name] = MutantCount(sum(shard[name] for shard in shards))
    return merged


def _merge_shards(
    artifact_dir: Path, numbers: tuple[RustShard, ...], listing: CargoListing, *, whole: bool
) -> SweepOutcomes | Prose:
    """Read the shards' ``outcomes.json`` files and the listing, and merge them."""
    try:
        listed = cast("list[ListedMutant]", json.loads(listing))
    except json.JSONDecodeError:
        return Prose("cargo mutants --list --json printed no listing (see the lane's log)")
    read: list[SweepOutcomes] = []
    for number in numbers:
        path = shard_output(artifact_dir, number) / "mutants.out" / "outcomes.json"
        if not path.is_file():
            return Prose(f"shard {number} wrote no outcomes (see rust-shard-{number}.raw.txt)")
        read.append(cast("SweepOutcomes", json.loads(path.read_text(encoding="utf-8"))))
    return merge_shard_outcomes(listed, read, whole=whole)


def _job_commits(jobs_dir: Path) -> dict[RustBinding, ShortSha]:
    """Read the commit each job's summary records, by the job's binding."""
    commits: dict[RustBinding, ShortSha] = {}
    for summary_path in sorted(jobs_dir.rglob("summary.json")):
        summary = cast("JobSummary", json.loads(summary_path.read_text(encoding="utf-8")))
        for run in summary.get("runs", []):
            binding = run.get("binding", RustBinding(""))
            if is_rust_job(binding):
                commits[binding] = summary.get("commit", ShortSha(""))
    return commits


def _jobs_refusal(jobs_dir: Path) -> Prose | None:
    """Say why the jobs under the directory are not one sweep of this commit, or None."""
    commit = ShortSha(short_sha(REPO_ROOT))
    commits = _job_commits(jobs_dir)
    for job in (RustJob(n) for n in range(1, RUST_JOBS + 1)):
        binding = job_binding(job)
        if binding not in commits:
            return Prose(f"no summary of the {binding} job under {jobs_dir}")
        if commits[binding] != commit:
            return Prose(f"the {binding} job swept {commits[binding]}, this merge is at {commit}")
    listings = sorted(jobs_dir.rglob(RUST_LISTING))
    if len(listings) != RUST_JOBS:
        return Prose(
            f"{len(listings)} copies of {RUST_LISTING} under {jobs_dir}, wanted {RUST_JOBS}"
        )
    if len({path.read_bytes() for path in listings}) != 1:
        return Prose("the jobs listed different mutants, so their shards are not one sweep's")
    return None


def _jobs_shards(jobs_dir: Path) -> list[SweepOutcomes] | Prose:
    """Read every shard the jobs deal, each wanted once under the directory, or say which not."""
    read: list[SweepOutcomes] = []
    for number in range(RUST_JOBS * RUST_JOB_SHARDS):
        pattern = f"{RUST_OUTPUT_DIR}/shard-{number}/mutants.out/outcomes.json"
        found = sorted(jobs_dir.rglob(pattern))
        if len(found) != 1:
            return Prose(
                f"{len(found)} copies of shard {number}'s outcomes under {jobs_dir}, wanted one"
            )
        read.append(cast("SweepOutcomes", json.loads(found[0].read_text(encoding="utf-8"))))
    return read


def merge_rust_jobs(artifact_dir: Path) -> MutationReport:
    """Merge the jobs' sweeps found under the directory ``RUST_JOBS_ENV`` names.

    The jobs must be of this commit and have listed the same mutants, and
    every shard of the jobs' total is wanted exactly once, wherever the
    download put it; the shards are then merged against the listing as one
    whole sweep's are, and the merged ``outcomes.json`` is the lane's, which
    the drift gate and the survivor ledger read.
    """
    jobs_env = os.environ.get(RUST_JOBS_ENV, "")
    if not jobs_env:
        msg = f"{RUST_STAGE_ENV}={RUST_MERGE_STAGE} reads the jobs from {RUST_JOBS_ENV}: unset"
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, "", error=msg)
    jobs_dir = Path(jobs_env)
    refusal = _jobs_refusal(jobs_dir)
    if refusal is not None:
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, "", error=refusal)
    listing = CargoListing(min(jobs_dir.rglob(RUST_LISTING)).read_text(encoding="utf-8"))
    raw = f"=== merge of the Rust jobs under {jobs_dir} ===\n"
    for job in range(1, RUST_JOBS + 1):
        logs = sorted(jobs_dir.rglob(f"rust-{job}.raw.txt"))
        raw += "".join(path.read_text(encoding="utf-8") for path in logs)
    read = _jobs_shards(jobs_dir)
    if not isinstance(read, list):
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, raw, error=read)
    try:
        listed = cast("list[ListedMutant]", json.loads(listing))
    except json.JSONDecodeError:
        msg = f"the jobs' {RUST_LISTING} holds no listing"
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, raw, error=msg)
    merged = merge_shard_outcomes(listed, read)
    if not isinstance(merged, dict):
        return MutationReport(RUST_LANE, "cargo-mutants", 0, 0, raw, error=merged)
    outcomes_path = artifact_dir / OUTCOMES
    outcomes_path.parent.mkdir(parents=True, exist_ok=True)
    _ = outcomes_path.write_text(json.dumps(merged, indent=2), encoding="utf-8")
    (artifact_dir / f"{RUST_LANE}.raw.txt").write_text(raw)
    return parse_outcomes(merged, raw, "the jobs' merge")


def parse_outcomes(
    outcomes: Mapping[str, object], raw: str, where: str, binding: RustBinding | None = None
) -> MutationReport:
    """Read a sweep's ``outcomes.json`` into a report.

    The file carries the four buckets every mutant lands in exactly one of:
    caught, missed, timed out and unviable.  Caught is killed and missed is
    survived; a timed-out mutant is neither, and the drift gate reads that
    count against the record's ceiling; an unviable mutant did not build, a
    property of the source the record carries in the count of every mutant
    the tool made, the four buckets together.  A sweep that
    reached no mutant, because the unmutated baseline failed, is an error
    rather than a clean run of nothing.
    """
    lane = RUST_LANE if binding is None else binding
    counts = {name: outcomes.get(name) for name in ("caught", "missed", "timeout", "unviable")}
    if not all(isinstance(value, int) for value in counts.values()):
        return MutationReport(
            lane,
            "cargo-mutants",
            0,
            0,
            raw,
            error=f"outcomes.json carries no counts (see rust.raw.txt; {where})",
        )
    caught, missed, timeout, unviable = (cast("int", counts[k]) for k in counts)
    if caught + missed + timeout + unviable == 0:
        return MutationReport(
            lane,
            "cargo-mutants",
            0,
            0,
            raw,
            error=f"the sweep tested no mutant (see rust.raw.txt; {where})",
        )
    generated = MutantCount(caught + missed + timeout + unviable)
    return MutationReport(
        lane,
        "cargo-mutants",
        caught,
        missed,
        raw,
        observed=Observed(timeouts=timeout, generated=generated),
    )


def outcomes_survivor_rows(
    outcomes: Mapping[str, object], read_line: Callable[[str, int], str]
) -> dict[SurvivorKey, int]:
    """Collect the survivors of an ``outcomes.json`` into rows.

    Each outcome's ``scenario`` is the mutant, with its ``name``, its file
    relative to the crate and the span it replaces; ``summary`` is its
    bucket.  ``read_line(file, line)`` supplies the source line, stripped
    before it keys the row.
    """
    rows: dict[SurvivorKey, int] = collections.Counter()
    for outcome in cast("list[Mapping[str, object]]", outcomes.get("outcomes", [])):
        if outcome.get("summary") != "MissedMutant":
            continue
        scenario = cast("Mapping[str, Mapping[str, object]]", outcome["scenario"])
        mutant = scenario["Mutant"]
        file = f"rust/{mutant['file']}"
        span = cast("Mapping[str, Mapping[str, int]]", mutant["span"])
        line = span["start"]["line"]
        mutator = _POSITION_RE.sub("", str(mutant["name"]))
        rows[(mutator, file, read_line(file, line).strip())] += 1
    return rows


def repo_line(file: str, line: int) -> str:
    """Read the ``line``-th line (1-based) of ``file`` under the repository root."""
    with (REPO_ROOT / file).open(encoding="utf-8") as src:
        return src.read().split("\n")[line - 1]


def rust_survivor_rows(artifact_dir: Path) -> dict[SurvivorKey, int] | None:
    """Read the Rust sweep's survivor rows from its outcomes, if it wrote them."""
    path = artifact_dir / OUTCOMES
    if not path.is_file():
        return None
    outcomes = cast("Mapping[str, object]", json.loads(path.read_text(encoding="utf-8")))
    return outcomes_survivor_rows(outcomes, repo_line)

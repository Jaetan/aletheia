# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Go mutation lane's shards: which files each sweeps, and the proof that they add up.

The Go sweep is cut across CI jobs by file, as the C++ sweep is cut into
slices: a shard runs gremlins under the package's own configuration with the
files of every other shard added to ``exclude-files``, so it sweeps its own
files' mutants alone, and the merge unions the shards back into the lane's
verdict.

The files are cut on their sizes, read from the tree, so nothing here is a
list anyone keeps; the size stands for a file's share of the sweep, and over
the census recorded when the cut was chosen, 763 mutants, it cut them 399 and
364 where the census itself would cut 382 and 381.  The census is not what the cut is made on
because the only census is gremlins' dry run, and a dry run ahead of a sweep
leaves the package compiled in the build cache: gremlins times its coverage
run to set every mutant's limit, so that run, then quicker than the
mutants' own builds, stopped most of them before their tests ended.

Each shard takes the census after its sweep instead, under the package's own
configuration, and writes it beside its log with its own files.  The merge
holds the shards to that census, file by file: every shard read the same
census, the shards' files are disjoint and are the whole domain, and each
shard swept exactly the census's mutants of its own files and none of anyone
else's.  A shard whose configuration lost one of the package's own exclusions
sweeps mutants the census does not carry, and one that excluded too much
sweeps fewer than it does, so either refuses the merge; the C++ merge compares
its union with a recorded total instead, its census costing a whole build.
"""

from __future__ import annotations

import collections
import json
import os
import re
import shutil
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict, cast

import yaml

from tools._common import RelPath, git_ls_files
from tools.mutation_cpp_config import MutantCount
from tools.mutation_cpp_slices import MutantCounts, Slice, partition
from tools.mutation_report import MutationReport

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterable, Sequence

# Shards the Go sweep is cut into.  Two, because the heaviest file holds two
# fifths of the package's mutants, so no partition gets a shard under that
# share, and two shards already put the lane below the other lanes' wall
# clock, each further shard paying the job's setup again for less.
GO_SHARDS = 2

# The package gremlins sweeps, and the configuration it reads from the module
# root, both repository-relative.
GO_PACKAGE = "go/aletheia"
GO_CONFIG = "go/.gremlins.yaml"

GO_STAGE_ENV = "ALETHEIA_MUTATION_GO_STAGE"
GO_SHARDS_ENV = "ALETHEIA_MUTATION_GO_SHARDS"

# What the stage reads as where the process merges the shards rather than sweeping.
GO_MERGE_STAGE = "merge"

# The merge stage's record of each shard's wall clock, beside ``go.json``.
GO_SHARDS_REPORT = "go-shards.json"

# One shard of the sweep, numbered from one.
ShardNumber = NewType("ShardNumber", int)

# The name a report carries for its binding, ``go`` or one shard's ``go-1``.
Binding = NewType("Binding", str)

# A file of the package as gremlins names it, relative to the package.
PackageFile = NewType("PackageFile", str)

# A regular expression gremlins matches against a ``PackageFile``.
FilePattern = NewType("FilePattern", str)

# What a gremlins run printed, a dry run's listing or a sweep's verdicts.
GremlinsLog = NewType("GremlinsLog", str)

# A gremlins configuration file's text.
GremlinsConfigText = NewType("GremlinsConfigText", str)

# A report file's name, as a run writes it into its artifact directory.
ArtifactName = NewType("ArtifactName", str)

# A run's wall clock in seconds, as the runner's summary records it.
WallSeconds = NewType("WallSeconds", float)

# A commit as the runner's summary records it, its short hash.
ShortSha = NewType("ShortSha", str)

# Each shard's wall clock, by the binding it reported as.
type ShardElapsed = dict[Binding, WallSeconds]


class _SummaryRun(TypedDict, total=False):
    binding: Binding


class _Summary(TypedDict, total=False):
    """The part of the runner's ``summary.json`` the merge reads."""

    commit: ShortSha
    runs: list[_SummaryRun]
    elapsed_s: dict[Binding, WallSeconds]


# The part of gremlins' configuration this module reads and writes; every
# other entry the file carries is kept as read.
_Unleash = TypedDict("_Unleash", {"exclude-files": list[FilePattern]}, total=False)


class _GremlinsConfig(TypedDict, total=False):
    unleash: _Unleash


class ShardJson(TypedDict):
    """What one shard writes beside its log, as JSON."""

    shard: ShardNumber
    domain: list[RelPath]
    files: list[RelPath]
    census: MutantCounts


# A mutant a dry run lists, and one a sweep reported: the verdict, the
# mutator, and the file, named relative to the package as gremlins names it.
_DRY_MUTANT = re.compile(r"^\s*(?:RUNNABLE|NOT COVERED) \w+ at ([\w.]+\.go):\d+:\d+", re.MULTILINE)
_SWEPT_MUTANT = re.compile(
    r"^\s*(?:KILLED|LIVED|TIMED OUT|NOT COVERED|NOT VIABLE) \w+ at ([\w.]+\.go):\d+:\d+",
    re.MULTILINE,
)


def shard_record_name(number: ShardNumber) -> ArtifactName:
    """Name the file a shard writes its record to, beside its log."""
    return ArtifactName(f"go-shard-{number}.json")


def shard_log_name(number: ShardNumber) -> ArtifactName:
    """Name the file a shard writes its sweep's log to."""
    return ArtifactName(f"{shard_binding(number)}.raw.txt")


def shard_binding(number: ShardNumber) -> Binding:
    """Name the binding a shard reports as, so its report never reads as the lane's ``go.json``."""
    return Binding(f"go-{number}")


def is_go_shard(binding: Binding) -> bool:
    """Whether a report's binding name is one shard of the Go lane."""
    name = binding.removeprefix("go-")
    return name != binding and name.isdigit() and 1 <= int(name) <= GO_SHARDS


def go_stage() -> ShardNumber | Literal["merge"] | None:
    """Read what this process does from the environment; unset is the whole lane.

    Raises ``ValueError`` naming the variable on a value that is no shard, so a
    misspelt one in a CI job fails that job rather than sweeping the package
    whole or sweeping nothing.
    """
    stage = os.environ.get(GO_STAGE_ENV, "")
    if not stage:
        return None
    if stage == GO_MERGE_STAGE:
        return GO_MERGE_STAGE
    if not stage.isdigit() or not 1 <= int(stage) <= GO_SHARDS:
        msg = f"{GO_STAGE_ENV}={stage!r} is not a shard of 1 to {GO_SHARDS} or {GO_MERGE_STAGE!r}"
        raise ValueError(msg)
    return ShardNumber(int(stage))


def _config(config_path: Path) -> _GremlinsConfig:
    """Read gremlins' configuration as a mapping, refusing anything else with its path."""
    document = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    if not isinstance(document, dict):
        msg = f"{config_path} is not a gremlins configuration: its top level is no mapping"
        raise TypeError(msg)
    return cast("_GremlinsConfig", document)


def held_out_patterns(config_path: Path) -> list[FilePattern]:
    """Read the file patterns the package's configuration holds out of every sweep."""
    excludes = _config(config_path).get("unleash", {}).get("exclude-files", [])
    return [FilePattern(str(pattern)) for pattern in excludes]


def hold_out_pattern(path: RelPath) -> FilePattern:
    """Build the gremlins pattern matching one file of the package and nothing else.

    gremlins matches ``exclude-files`` against a file's path relative to the
    package, so the pattern is anchored at the start of that path or at a
    separator, and at its end: ``enrich.go`` does not reach ``re_enrich.go``.
    """
    return FilePattern("(^|/)" + re.escape(_package_file(path)) + "$")


def _package_file(path: RelPath) -> PackageFile:
    return PackageFile(path.removeprefix(GO_PACKAGE + "/"))


def shard_domain(repo_root: Path, config_path: Path) -> list[RelPath]:
    """Every file a shard can claim: the package's sources, less what the configuration holds out.

    Derived from the tree rather than listed, so a file the package gains
    joins the partition the moment it is tracked; the configuration's patterns
    are matched the way gremlins matches them, against the path within the
    package.
    """
    holdouts = [re.compile(pattern) for pattern in held_out_patterns(config_path)]
    return sorted(
        path
        for path in git_ls_files(repo_root, GO_PACKAGE)
        if path.endswith(".go")
        and not path.endswith("_test.go")
        and "/" not in str(_package_file(path))
        and not any(holdout.search(_package_file(path)) for holdout in holdouts)
    )


def _counted(names: Iterable[PackageFile]) -> MutantCounts:
    counts: collections.Counter[RelPath] = collections.Counter(
        RelPath(f"{GO_PACKAGE}/{name}") for name in names
    )
    return dict(counts)


def dry_run_census(log: GremlinsLog) -> MutantCounts:
    """Count the mutants a dry run of the package lists, by file: runnable and not covered alike."""
    return _counted(_DRY_MUTANT.findall(log))


def swept_counts(log: GremlinsLog) -> MutantCounts:
    """Count the mutants a sweep reported, by file, whatever their verdict."""
    return _counted(_SWEPT_MUTANT.findall(log))


def shard_files(repo_root: Path, domain: Sequence[RelPath], number: ShardNumber) -> Slice:
    """Cut one shard's files out of the domain, each weighing its size in the tree."""
    sizes = {path: (repo_root / path).stat().st_size for path in domain}
    return partition(domain, sizes, GO_SHARDS)[number - 1]


_GENERATED_HEADER = """\
# Generated by tools/mutation_go.py for shard {number} of {total} of the Go
# mutation lane: the package's own configuration, with the files of the other
# shards held out so this sweep carries this shard's mutants alone.
"""


def shard_config_text(
    config_path: Path, held_out: Iterable[RelPath], number: ShardNumber
) -> GremlinsConfigText:
    """Write one shard's gremlins configuration: the package's, the other shards' files held out.

    The mutators and the package's own exclusions stay as written.  The
    exclusions are extended rather than passed on the command line, because
    an ``--exclude-files`` there replaces the configuration's list instead of
    adding to it, which brings back the generated files the package holds out.
    """
    config = _config(config_path)
    unleash = config.setdefault("unleash", {})
    unleash["exclude-files"] = held_out_patterns(config_path) + [
        hold_out_pattern(path) for path in held_out
    ]
    header = _GENERATED_HEADER.format(number=number, total=GO_SHARDS)
    return GremlinsConfigText(header + yaml.safe_dump(config, sort_keys=False))


class ShardRecord(NamedTuple):
    """What a shard wrote beside its log: the census taken after its sweep, its domain and files."""

    number: ShardNumber
    domain: tuple[RelPath, ...]
    files: tuple[RelPath, ...]
    census: MutantCounts

    def to_json(self) -> ShardJson:
        """Spell the record as the JSON a shard writes."""
        return {
            "shard": self.number,
            "domain": list(self.domain),
            "files": list(self.files),
            "census": dict(self.census),
        }

    @classmethod
    def from_json(cls, document: ShardJson) -> ShardRecord:
        """Read a record a shard wrote."""
        return cls(
            ShardNumber(document["shard"]),
            tuple(RelPath(path) for path in document["domain"]),
            tuple(RelPath(path) for path in document["files"]),
            {RelPath(path): count for path, count in document["census"].items()},
        )


class ShardCut(NamedTuple):
    """One shard's part of the package, cut before its sweep, and the configuration to restore."""

    domain: tuple[RelPath, ...]
    files: Slice
    package_config: GremlinsConfigText


class ShardSweep(NamedTuple):
    """One shard's contribution to the merge: its record and its sweep's log."""

    record: ShardRecord
    log: GremlinsLog


def merge_refusal(shards: Sequence[ShardSweep]) -> Prose | None:
    """Say why the shards' sweeps do not add up to the package's census, or None where they do.

    The shards must be every shard once, read one census over one domain,
    claim disjoint files that are the whole domain, and each must have swept
    exactly the census's mutants of its own files: a file it swept that it
    does not claim, or a count short of or over the census, is a sweep that
    did not do what its record says.
    """
    return _census_refusal(shards) or _claim_refusal(shards) or _sweep_refusal(shards)


def _census_refusal(shards: Sequence[ShardSweep]) -> Prose | None:
    """Refuse a set of shards that is not every shard once, or that read two censuses."""
    numbers = sorted(shard.record.number for shard in shards)
    if numbers != list(range(1, GO_SHARDS + 1)):
        return Prose(f"the Go shards present are {numbers}, wanted 1 to {GO_SHARDS} once each")
    first = shards[0].record
    for shard in shards[1:]:
        if shard.record.census != first.census or shard.record.domain != first.domain:
            return Prose(
                f"Go shards {first.number} and {shard.record.number} read different "
                + "censuses or domains: the tree or the tool differed between their runs"
            )
    outside = sorted(set(first.census) - set(first.domain))
    if outside:
        return Prose(f"the census names files outside the shards' domain: {', '.join(outside)}")
    return None


def _claim_refusal(shards: Sequence[ShardSweep]) -> Prose | None:
    """Refuse shards whose files overlap, or leave a file of the domain to nobody."""
    claimed: dict[RelPath, ShardNumber] = {}
    for shard in shards:
        for path in shard.record.files:
            if path in claimed:
                owner = claimed[path]
                return Prose(f"{path} is claimed by Go shards {owner} and {shard.record.number}")
            claimed[path] = shard.record.number
    unclaimed = sorted(set(shards[0].record.domain) - set(claimed))
    if unclaimed:
        return Prose(f"no Go shard claims {', '.join(unclaimed)}")
    return None


def _sweep_refusal(shards: Sequence[ShardSweep]) -> Prose | None:
    """Refuse a shard that swept other than the census's mutants of its own files."""
    census = shards[0].record.census
    for shard in shards:
        wanted = {path: census[path] for path in shard.record.files if census.get(path)}
        swept = swept_counts(shard.log)
        if swept != wanted:
            diff = sorted(
                f"{path}: swept {swept.get(path, 0)}, census {wanted.get(path, 0)}"
                for path in set(swept) | set(wanted)
                if swept.get(path, 0) != wanted.get(path, 0)
            )
            return Prose(
                f"Go shard {shard.record.number} did not sweep its census: " + "; ".join(diff)
            )
    return None


def shards_elapsed(shards_dir: Path, commit: ShortSha) -> ShardElapsed | Prose:
    """Read each shard's wall clock from the summary its run wrote, or say what is wrong.

    Every shard's summary must be there, once, and must record the commit the
    merge runs at: the shards of another commit merge into a verdict about
    nothing.
    """
    elapsed: ShardElapsed = {}
    for summary_path in sorted(shards_dir.rglob("summary.json")):
        summary = cast("_Summary", json.loads(summary_path.read_text(encoding="utf-8")))
        bindings = [run.get("binding", Binding("")) for run in summary.get("runs", [])]
        shards = [binding for binding in bindings if is_go_shard(binding)]
        secs = summary.get("elapsed_s", {}).get(Binding("go"))
        if not shards or secs is None:
            continue
        if summary.get("commit") != commit:
            return Prose(
                f"{summary_path} is a run at {summary.get('commit')}, the merge is at {commit}"
            )
        if shards[0] in elapsed:
            return Prose(f"{summary_path} is a second {shards[0]} shard")
        elapsed[shards[0]] = secs
    wanted = [shard_binding(ShardNumber(number)) for number in range(1, GO_SHARDS + 1)]
    missing = [shard for shard in wanted if shard not in elapsed]
    if missing:
        return Prose(f"no summary of the {', '.join(missing)} shard under {shards_dir}")
    return elapsed


# The binding the whole Go lane reports as, and the merge of its shards.
GO_LANE = Binding("go")


def go_refusal(
    binding: Binding, error: Prose, log: GremlinsLog = GremlinsLog("")
) -> MutationReport:
    """Report a Go run that reached no verdict, with why and what it printed meanwhile."""
    return MutationReport(binding, "gremlins", 0, 0, log, error=error)


def parse_gremlins_summary(
    raw: GremlinsLog, where: Prose, binding: Binding = GO_LANE
) -> MutationReport:
    """Read a gremlins run's tail summary into a report.

    Separate from the run so the drift gate can be shown to refuse a recorded
    sweep that timed out without one having to be reproduced.  The tail is::

        Killed: N, Lived: N, Not covered: N
        Timed out: N, Not viable: N, Skipped: N
        Test efficacy: P.PP%
        Mutator coverage: P.PP%
    """
    killed_m = re.search(r"Killed:\s*(\d+)", raw)
    survived_m = re.search(r"Lived:\s*(\d+)", raw)
    timeout_m = re.search(r"Timed out:\s*(\d+)", raw)
    if not (killed_m and survived_m):
        return go_refusal(
            binding,
            Prose(f"could not parse gremlins summary (see {binding}.raw.txt; {where})"),
            raw,
        )
    # gremlins' "Not covered" mutants are on lines no test reaches; they do not
    # contribute to the killed/lived split, so total_mutants = killed + survived.
    return MutationReport(
        binding,
        "gremlins",
        int(killed_m.group(1)),
        int(survived_m.group(1)),
        raw,
        timeouts=int(timeout_m.group(1)) if timeout_m else None,
    )


def cut_go_shard(tree: Path, number: ShardNumber) -> ShardCut:
    """Cut one shard out of the package and write its configuration into the tree."""
    config = tree / GO_CONFIG
    package_config = GremlinsConfigText(config.read_text(encoding="utf-8"))
    domain = tuple(shard_domain(tree, config))
    files = shard_files(tree, domain, number)
    held_out = [path for path in domain if path not in files]
    _ = config.write_text(shard_config_text(config, held_out, number), encoding="utf-8")
    return ShardCut(domain, files, package_config)


def record_go_shard(
    number: ShardNumber, cut: ShardCut, census_log: GremlinsLog, artifact_dir: Path
) -> Prose | None:
    """Write a shard's record beside its log, from the census taken after its sweep.

    Returns the lines that open the shard's log, or None where the census is
    empty, a dry run that listed nothing being one that did not run.
    """
    census = dry_run_census(census_log)
    if not census:
        return None
    record = ShardRecord(number, cut.domain, cut.files, census)
    _ = (artifact_dir / shard_record_name(number)).write_text(
        json.dumps(record.to_json(), indent=2)
    )
    carried = sum(census.get(path, 0) for path in cut.files)
    return Prose(
        f"=== Go shard {number} of {GO_SHARDS}: {len(cut.files)} files, {carried} of "
        + f"{sum(census.values())} mutants ===\n"
        + "".join(f"  {path}\n" for path in cut.files)
    )


def _one_file(directory: Path, name: ArtifactName) -> Path | Prose:
    """Find the one file of that name under the directory, or say how many there are."""
    found = sorted(directory.rglob(name))
    if len(found) != 1:
        return Prose(f"{len(found)} copies of {name} under {directory}, wanted one")
    return found[0]


def _read_go_shard(
    shards_dir: Path, artifact_dir: Path, number: ShardNumber
) -> tuple[ShardSweep, MutationReport] | Prose:
    """Copy one shard's record and log beside the merge and read them, or say what is wrong."""
    record_path = _one_file(shards_dir, shard_record_name(number))
    if not isinstance(record_path, Path):
        return record_path
    log_path = _one_file(shards_dir, shard_log_name(number))
    if not isinstance(log_path, Path):
        return log_path
    _ = shutil.copyfile(record_path, artifact_dir / record_path.name)
    _ = shutil.copyfile(log_path, artifact_dir / log_path.name)
    document = cast("ShardJson", json.loads(record_path.read_text(encoding="utf-8")))
    log = GremlinsLog(log_path.read_text(encoding="utf-8"))
    report = parse_gremlins_summary(log, Prose(f"shard {number}"), shard_binding(number))
    if report.error:
        return Prose(report.error)
    return ShardSweep(ShardRecord.from_json(document), log), report


def merge_go_shards(artifact_dir: Path, commit: ShortSha) -> MutationReport:
    """Merge the shards' sweeps found under the directory ``GO_SHARDS_ENV`` names.

    Each shard's record and log are wanted exactly once under that directory,
    wherever the download put them, and the shards must add up to the census
    they took after their sweeps (``merge_refusal``): the merge holds them to
    no recorded total, the census being what the dry run measured.  The merged
    report is the lane's ``go`` report, its counts the shards' sums and its
    log every shard's log, so the drift gate reads its survivors and its
    not-covered mutants as it reads a whole sweep's.
    """
    shards_env = os.environ.get(GO_SHARDS_ENV, "")
    if not shards_env:
        return go_refusal(
            GO_LANE,
            Prose(f"{GO_STAGE_ENV}={GO_MERGE_STAGE} reads the shards from {GO_SHARDS_ENV}: unset"),
        )
    shards_dir = Path(shards_env)
    raw = f"=== merge of the Go shards under {shards_dir} ===\n"
    sweeps: list[ShardSweep] = []
    reports: list[MutationReport] = []
    for number in (ShardNumber(n) for n in range(1, GO_SHARDS + 1)):
        read = _read_go_shard(shards_dir, artifact_dir, number)
        if not isinstance(read, tuple):
            return go_refusal(GO_LANE, read, GremlinsLog(raw + read + "\n"))
        sweeps.append(read[0])
        reports.append(read[1])
    refusal = merge_refusal(sweeps)
    if refusal is not None:
        return go_refusal(GO_LANE, refusal, GremlinsLog(raw + refusal + "\n"))
    elapsed = shards_elapsed(shards_dir, commit)
    if not isinstance(elapsed, dict):
        return go_refusal(GO_LANE, elapsed, GremlinsLog(raw + elapsed + "\n"))
    _ = (artifact_dir / GO_SHARDS_REPORT).write_text(json.dumps(elapsed, indent=2))
    killed = sum(report.killed for report in reports)
    lived = sum(report.survived for report in reports)
    timed_out = sum(report.timeouts or 0 for report in reports)
    not_covered = sum(_not_covered(sweep.log) for sweep in sweeps)
    # The merged figures open the log, in gremlins' own words, so a reader
    # taking the first summary line reads the lane's and not one shard's.
    raw += f"Killed: {killed}, Lived: {lived}, Not covered: {not_covered}\n"
    raw += f"Timed out: {timed_out}\n"
    raw += "".join(f"{shard} swept in {secs}s\n" for shard, secs in elapsed.items())
    raw += "".join(sweep.log for sweep in sweeps)
    (artifact_dir / "go.raw.txt").write_text(raw)
    return MutationReport("go", "gremlins", killed, lived, raw, timeouts=timed_out)


def _not_covered(log: GremlinsLog) -> MutantCount:
    """Read a sweep's not-covered count from its summary."""
    found = re.search(r"Not covered:\s*(\d+)", log)
    return MutantCount(int(found.group(1)) if found else 0)

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Python mutation lane's shards: which mutants each runs, and the proof that they add up.

mutmut cuts no shards of its own, so the witness deals them
(``tools/mutation_witness.py --shard``): every shard makes every mutant and
runs mutmut's whole-suite runs as a whole sweep does, then tests the mutants
of the sorted list its place is dealt, the first shard the first, the third
and so on, as cargo-mutants deals the Rust lane's.  Dealt rather than cut by
file, the shards stay even as the files' costs move: over a sweep of 3,685
timed mutants, the larger of two dealt shards took 50.1% of the time.

Each shard writes its record beside its log: the commit, every mutant mutmut
made, its census, and the mutants it judged, both read from mutmut's
``.meta`` files, where a mutant no shard judged has no exit.  The merge holds
the shards to that: every shard once, all of one commit, one census, and each
having judged exactly its deal of it, so together they judged every mutant
once and the sums of their counts are a whole sweep's.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict, cast

from tools.mutation_go import Binding, ShortSha
from tools.mutation_report import ArtifactName, one_file
from tools.mutation_witness import MutantName

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Sequence

    from aletheia.common_types import ExitStatus

# Shards the Python sweep is dealt into.  Two, because two already put the
# lane below the other lanes' wall clock, and each further shard pays the
# job's setup and mutmut's whole-suite runs again for no shorter check.
PYTHON_SHARDS = 2

PYTHON_STAGE_ENV = "ALETHEIA_MUTATION_PYTHON_STAGE"
PYTHON_SHARDS_ENV = "ALETHEIA_MUTATION_PYTHON_SHARDS"

# What the stage reads as where the process merges the shards rather than sweeping.
PYTHON_MERGE_STAGE = "merge"

# The binding the whole lane reports as, and the merge of its shards.
PYTHON_LANE = Binding("python")

# One shard of the sweep, numbered from one.
ShardNumber = NewType("ShardNumber", int)


class ShardJson(TypedDict):
    """What one shard writes beside its log, as JSON."""

    shard: ShardNumber
    commit: ShortSha
    census: list[MutantName]
    judged: list[MutantName]


class ShardRecord(NamedTuple):
    """One shard's record, as the merge reads it."""

    number: ShardNumber
    commit: ShortSha
    census: tuple[MutantName, ...]
    judged: tuple[MutantName, ...]


def python_stage() -> ShardNumber | Literal["merge"] | None:
    """Read what this process does from the environment; unset is the whole lane.

    Raises ``ValueError`` naming the variable on a value that is no shard, so a
    misspelt one in a CI job fails that job rather than sweeping the whole
    lane or sweeping nothing.
    """
    stage = os.environ.get(PYTHON_STAGE_ENV, "")
    if not stage:
        return None
    if stage == PYTHON_MERGE_STAGE:
        return PYTHON_MERGE_STAGE
    if not stage.isdigit() or not 1 <= int(stage) <= PYTHON_SHARDS:
        msg = (
            f"{PYTHON_STAGE_ENV}={stage!r} is not a shard of 1 to {PYTHON_SHARDS} "
            + f"or {PYTHON_MERGE_STAGE!r}"
        )
        raise ValueError(msg)
    return ShardNumber(int(stage))


def shard_binding(number: ShardNumber) -> Binding:
    """Name the binding a shard reports as, so its report never reads as the lane's."""
    return Binding(f"{PYTHON_LANE}-{number}")


def is_python_shard(binding: Binding) -> bool:
    """Whether a report's binding name is one shard of the Python lane."""
    name = binding.removeprefix(f"{PYTHON_LANE}-")
    return name != binding and name.isdigit() and 1 <= int(name) <= PYTHON_SHARDS


def shard_deal(number: ShardNumber) -> Prose:
    """Spell the witness's ``--shard`` value for this shard."""
    return Prose(f"{number}/{PYTHON_SHARDS}")


def shard_record_name(number: ShardNumber) -> ArtifactName:
    """Name the file a shard writes its record to, beside its log."""
    return ArtifactName(f"python-shard-{number}.json")


def dealt(census: Sequence[MutantName], number: ShardNumber) -> tuple[MutantName, ...]:
    """Return the mutants of the sorted ``census`` that the witness deals to shard ``number``."""
    return tuple(sorted(census)[number - 1 :: PYTHON_SHARDS])


def read_exits(mutants: Path) -> dict[MutantName, ExitStatus | None]:
    """Read every mutant's exit from mutmut's ``.meta`` files under ``mutants``."""
    exits: dict[MutantName, ExitStatus | None] = {}
    for meta in sorted(mutants.rglob("*.meta")):
        exits |= cast(
            "dict[MutantName, ExitStatus | None]",
            json.loads(meta.read_text(encoding="utf-8"))["exit_code_by_key"],
        )
    return exits


def record_python_shard(
    number: ShardNumber, commit: ShortSha, mutants: Path, artifact_dir: Path
) -> Prose | None:
    """Write a shard's record beside its log, from the ``.meta`` files its sweep left.

    Returns the lines that open the shard's log, or None where mutmut made no
    mutant, a sweep that made nothing being one that did not run.
    """
    exits = read_exits(mutants)
    if not exits:
        return None
    judged = sorted(name for name, code in exits.items() if code is not None)
    record: ShardJson = {
        "shard": number,
        "commit": commit,
        "census": sorted(exits),
        "judged": judged,
    }
    _ = (artifact_dir / shard_record_name(number)).write_text(
        json.dumps(record, indent=2), encoding="utf-8"
    )
    return Prose(
        f"=== Python shard {number} of {PYTHON_SHARDS}: {len(judged)} of "
        + f"{len(exits)} mutants ===\n"
    )


def read_record(path: Path) -> ShardRecord:
    """Read a record a shard wrote."""
    document = cast("ShardJson", json.loads(path.read_text(encoding="utf-8")))
    return ShardRecord(
        ShardNumber(document["shard"]),
        ShortSha(document["commit"]),
        tuple(MutantName(name) for name in document["census"]),
        tuple(MutantName(name) for name in document["judged"]),
    )


def merge_refusal(records: Sequence[ShardRecord], commit: ShortSha) -> Prose | None:
    """Say why the shards do not add up to one whole sweep, or None where they do.

    The shards must be every shard once, of the merge's commit, have read one
    census, and each have judged exactly its deal of it: a shard judging a
    mutant dealt to another, or leaving one of its own, is a deal the witness
    did not make.
    """
    numbers = sorted(record.number for record in records)
    if numbers != list(range(1, PYTHON_SHARDS + 1)):
        return Prose(
            f"the Python shards present are {numbers}, wanted 1 to {PYTHON_SHARDS} once each"
        )
    for record in records:
        if record.commit != commit:
            return Prose(
                f"Python shard {record.number} ran at {record.commit}, the merge is at {commit}"
            )
        if record.census != records[0].census:
            return Prose(
                f"Python shards {records[0].number} and {record.number} read different "
                + "censuses: the tree or the tool differed between their runs"
            )
        wanted = dealt(record.census, record.number)
        if record.judged != wanted:
            extra = sorted(set(record.judged) - set(wanted))
            missing = sorted(set(wanted) - set(record.judged))
            return Prose(
                f"Python shard {record.number} judged {len(record.judged)} mutants, its deal "
                + f"is {len(wanted)}: {len(extra)} not dealt to it (first {extra[:1]}), "
                + f"{len(missing)} of its own left (first {missing[:1]})"
            )
    return None


class ShardPart(NamedTuple):
    """One shard's part of the merge: its record, its log and the error its run reported."""

    record: ShardRecord
    log: Prose
    error: Prose | None


class _ReportJson(TypedDict):
    """The part of a shard's ``python-<n>.json`` the merge reads."""

    error: Prose | None


def read_python_shards(shards_dir: Path, commit: ShortSha) -> list[ShardPart] | Prose:
    """Read every shard's record, log and report under ``shards_dir``, or say what is wrong.

    Each is wanted exactly once, wherever the download put it, and the
    records must add up to one whole sweep (``merge_refusal``).
    """
    parts: list[ShardPart] = []
    for number in (ShardNumber(n) for n in range(1, PYTHON_SHARDS + 1)):
        binding = shard_binding(number)
        names = (
            shard_record_name(number),
            ArtifactName(f"{binding}.raw.txt"),
            ArtifactName(f"{binding}.json"),
        )
        found = [one_file(shards_dir, name) for name in names]
        wrong = [item for item in found if not isinstance(item, Path)]
        if wrong:
            return Prose(wrong[0])
        record_path, log_path, report_path = cast("list[Path]", found)
        report = cast("_ReportJson", json.loads(report_path.read_text(encoding="utf-8")))
        parts.append(
            ShardPart(
                read_record(record_path),
                Prose(log_path.read_text(encoding="utf-8")),
                report["error"],
            )
        )
    return merge_refusal([part.record for part in parts], commit) or parts

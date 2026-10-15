# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold that cargo-mutants deals its shards as a partition of its listing.

The Rust lane (``tools/mutation_rust.py``) lists the crate's mutants once and
sweeps them in shards side by side, ``--shard k/N`` with ``k`` from zero, and
its merge refuses shards that miss, repeat or add a mutant.  That the shards
partition the listing is a fact about the cargo-mutants release the record
pins, not about the tree: a release dealing shards another way would fail
every sweep.  So the gate runs when the pin moves in ``docs/MUTATION_BENCH.yaml``
or in the workflow installing it, or when the runner or this gate changes
(``tools/pin_scope.py``).

For every shard count the runner can choose, two to ``RUST_SHARDS_CAP`` for a
sweep in one process and ``RUST_JOBS * RUST_JOB_SHARDS`` for one spread over CI
jobs, the gate lists each shard with ``cargo mutants --list --json`` in the
tree's own crate, which builds nothing, and holds the shards to the whole
listing: each listed mutant in exactly one shard, no shard naming an unlisted
one.  Mutants are keyed as the lane keys them (``mutant_key``).

Exits 0 when the fact holds or nothing it rests on moved; 1 when a count's
shards miss, repeat or add a mutant, or the whole listing is empty or names a
mutant twice; and 2 when cargo or cargo-mutants is absent or not the pinned
release, or a listing fails or does not parse.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from typing import TYPE_CHECKING, cast

from tools._common import emit, git_toplevel, run_capture
from tools.mutation_rust import (
    CRATE,
    RUST_JOB_SHARDS,
    RUST_JOBS,
    RUST_SHARDS_CAP,
    MutantKey,
    RustShard,
    ShardCount,
    check_cargo_mutants,
    mutant_key,
    pinned_version,
)
from tools.pin_scope import PinGate, gate_runs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools.mutation_rust import ListedMutant

STEP = "check-cargo-mutants-shards"

# The keys one count's shards list, shard by shard, in the order cargo-mutants numbers them.
type ShardKeys = Sequence[Sequence[MutantKey]]


def shard_counts() -> tuple[ShardCount, ...]:
    """Return every shard count the runner can choose, a whole sweep's and the CI jobs' total."""
    return (
        *(ShardCount(count) for count in range(2, RUST_SHARDS_CAP + 1)),
        ShardCount(RUST_JOBS * RUST_JOB_SHARDS),
    )


def partition_refusals(
    whole: Sequence[MutantKey], shards: Mapping[ShardCount, ShardKeys]
) -> list[Prose]:
    """Say what breaks the partition: the whole listing's defects, then each count's.

    The whole listing must name at least one mutant and none twice.  For each
    count, the three numbers a shard count is refused on: mutants in more than
    one shard, listed mutants in no shard, and shard mutants the listing lacks.
    """
    refusals: list[Prose] = []
    listed = set(whole)
    if not whole:
        refusals.append(Prose("the listing names no mutant"))
    elif len(listed) != len(whole):
        refusals.append(
            Prose(f"the listing names {len(whole)} mutants, {len(listed)} of them distinct")
        )
    for count, dealt_shards in shards.items():
        dealt = collections.Counter(key for shard in dealt_shards for key in shard)
        twice = sum(1 for seen in dealt.values() if seen > 1)
        missed = len(listed - dealt.keys())
        extra = len(dealt.keys() - listed)
        if twice or missed or extra:
            refusals.append(
                Prose(
                    f"{count} shards: {twice} mutants in more than one shard,"
                    + f" {missed} in none, {extra} not in the listing"
                )
            )
    return refusals


def list_mutants(
    cargo: Path, crate: Path, shard: tuple[RustShard, ShardCount] | None
) -> list[MutantKey] | Prose:
    """List the crate's mutants, or ``shard``'s part of them, or say why the listing is none."""
    dealt = [] if shard is None else ["--shard", f"{shard[0]}/{shard[1]}"]
    cmd = [str(cargo), "mutants", "--list", "--json", "--colors", "never", *dealt]
    ran = run_capture(cmd, cwd=crate)
    spelled = " ".join(cmd[1:])
    if ran.returncode != 0:
        return Prose(f"`cargo {spelled}` in {crate} exited {ran.returncode}: {ran.stderr.strip()}")
    try:
        listed = cast("list[ListedMutant]", json.loads(ran.stdout))
    except json.JSONDecodeError as exc:
        return Prose(f"`cargo {spelled}` in {crate} printed what is not JSON: {exc}")
    try:
        return [mutant_key(mutant) for mutant in listed]
    except TypeError, KeyError:
        return Prose(f"`cargo {spelled}` in {crate} printed what is not a list of mutants")


def check(repo_root: Path) -> ExitStatus:
    """List the crate whole and in every count's shards, and judge the partition."""
    cargo = check_cargo_mutants(pinned_version())
    if isinstance(cargo, str):
        emit(f"{STEP}: {cargo}")
        return ExitStatus(2)
    crate = repo_root / CRATE
    whole = list_mutants(cargo, crate, None)
    if isinstance(whole, str):
        emit(f"{STEP}: {whole}")
        return ExitStatus(2)
    refusals = partition_refusals(whole, {})
    if not refusals:
        shards: dict[ShardCount, ShardKeys] = {}
        for count in shard_counts():
            dealt: list[list[MutantKey]] = []
            for number in range(count):
                listed = list_mutants(cargo, crate, (RustShard(number), count))
                if isinstance(listed, str):
                    emit(f"{STEP}: {listed}")
                    return ExitStatus(2)
                dealt.append(listed)
            shards[count] = dealt
        refusals = partition_refusals(whole, shards)
    for refusal in refusals:
        emit(f"{STEP}: {refusal}")
    return ExitStatus(1 if refusals else 0)


def main() -> ExitStatus:
    """Show the shard-dealing fact when the branch moves what it rests on."""
    _ = argparse.ArgumentParser(description=__doc__).parse_args()
    repo_root = git_toplevel()
    if not gate_runs(PinGate.CARGO_MUTANTS_SHARDS, repo_root):
        return ExitStatus(0)
    return check(repo_root)


if __name__ == "__main__":
    sys.exit(main())

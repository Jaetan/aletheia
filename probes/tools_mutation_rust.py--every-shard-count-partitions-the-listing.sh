#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_rust.py against the pinned cargo-mutants.
# Claim: for every shard count the runner can choose, the shards cargo-mutants
# deals with `--shard k/N` (numbered from zero) partition the mutants its
# `--list --json` names: each listed mutant in exactly one shard, no shard
# naming one the listing does not. The runner lists once and sweeps the
# shards side by side, and its merge refuses shards that break this, so a
# release of the tool that deals shards another way would fail every sweep;
# this probe says so before one runs.
# Non-zero exit: a shard count whose shards miss, repeat or add a mutant, or
# a listing that does not parse. Exits 0 with a note when cargo-mutants is not
# installed, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
command -v cargo > /dev/null || { echo "cargo not installed, claim untestable"; exit 0; }
cargo mutants --version > /dev/null 2>&1 || { echo "cargo-mutants not installed, claim untestable"; exit 0; }

exec "$py" - <<'PY'
import collections
import json
import subprocess
import sys

sys.path.insert(0, ".")
from tools.mutation_rust import RUST_SHARDS_CAP, MutantKey, RustShard, ShardCount, mutant_key


def listing(shard: tuple[RustShard, ShardCount] | None = None) -> list[MutantKey]:
    dealt = [] if shard is None else ["--shard", f"{shard[0]}/{shard[1]}"]
    proc = subprocess.run(
        ["cargo", "mutants", "--list", "--json", "--colors", "never", *dealt],
        cwd="rust", capture_output=True, text=True, check=False,
    )
    if proc.returncode != 0:
        print(f"cargo mutants --list {' '.join(dealt)} exited {proc.returncode}: {proc.stderr.strip()[:200]}")
        raise SystemExit(1)
    return [mutant_key(mutant) for mutant in json.loads(proc.stdout)]


whole = listing()
if not whole or len(set(whole)) != len(whole):
    print(f"the listing names {len(whole)} mutants, {len(set(whole))} of them distinct")
    raise SystemExit(1)
bad = False
for count in (ShardCount(n) for n in range(2, RUST_SHARDS_CAP + 1)):
    dealt = collections.Counter(
        key for k in range(count) for key in listing((RustShard(k), count))
    )
    twice = sum(1 for seen in dealt.values() if seen > 1)
    missed = len(set(whole) - set(dealt))
    extra = len(set(dealt) - set(whole))
    if twice or missed or extra:
        print(f"{count} shards: {twice} mutants in more than one, {missed} in none, {extra} not listed")
        bad = True
if bad:
    raise SystemExit(1)
print(f"PASS: 2 to {RUST_SHARDS_CAP} shards each partition the {len(whole)} listed mutants")
PY

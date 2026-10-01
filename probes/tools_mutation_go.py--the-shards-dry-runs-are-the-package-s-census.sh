#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_go.py, the cut of the Go mutation lane into shards.
# Claim: each shard's gremlins configuration lists exactly that shard's files'
# mutants, and the shards together list exactly the package's. In a scratch
# copy of the tree, a dry run under the package's own configuration is the
# census; a dry run under each shard's configuration, as the lane writes it,
# must list mutants in that shard's files alone, the shards' files must be
# disjoint, and their listings must add up to the census file by file. A shard
# configuration that lost the package's own exclusions lists the generated
# files' mutants, and one that held out too much lists fewer: either fails.
# Non-zero exit: a shard lists a file it does not claim, two shards claim one
# file, or the listings do not add up to the census. Exits 0 with a note when
# gremlins or the built kernel is absent, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v gremlins > /dev/null || { echo "gremlins not installed, claim untestable"; exit 0; }
[ -f build/libaletheia-ffi.so ] || { echo "the kernel is not built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import os
import subprocess
import sys
from pathlib import Path

from tools._common import scratch_worktree
from tools.mutation_cpp_slices import MutantCounts
from tools.mutation_go import (
    GO_CONFIG,
    GO_SHARDS,
    GremlinsLog,
    ShardNumber,
    dry_run_census,
    shard_config_text,
    shard_domain,
    shard_files,
)
from tools.mutation_run import GoFlags, go_sweep_goflags

repo = Path.cwd()
with scratch_worktree(repo) as tree:
    env = dict(os.environ)
    env["ALETHEIA_REPO_ROOT"] = str(tree)
    env["ALETHEIA_LIB"] = str(repo / "build" / "libaletheia-ffi.so")
    env["GOFLAGS"] = go_sweep_goflags(GoFlags(env.get("GOFLAGS", "")))
    config = tree / GO_CONFIG
    package_config = config.read_text(encoding="utf-8")

    def dry() -> MutantCounts:
        run = subprocess.run(
            ["gremlins", "unleash", "--dry-run", "./aletheia"],
            cwd=tree / "go", env=env, capture_output=True, text=True, check=False,
        )
        return dry_run_census(GremlinsLog(run.stdout))

    census = dry()
    if not census:
        print("the package's dry run listed no mutant")
        sys.exit(1)
    domain = shard_domain(tree, config)
    claimed = {}
    listed = {}
    for number in (ShardNumber(n) for n in range(1, GO_SHARDS + 1)):
        files = shard_files(tree, domain, number)
        held_out = [path for path in domain if path not in files]
        config.write_text(shard_config_text(config, held_out, number), encoding="utf-8")
        listing = dry()
        config.write_text(package_config, encoding="utf-8")
        stray = sorted(set(listing) - set(files))
        if stray:
            print(f"shard {number} lists mutants in files it does not claim: {', '.join(stray)}")
            sys.exit(1)
        for path in files:
            if path in claimed:
                print(f"{path} is claimed by shards {claimed[path]} and {number}")
                sys.exit(1)
            claimed[path] = number
        for path, count in listing.items():
            listed[path] = listed.get(path, 0) + count
if listed != census:
    diff = sorted(
        f"{path}: shards {listed.get(path, 0)}, census {census.get(path, 0)}"
        for path in set(listed) | set(census)
        if listed.get(path, 0) != census.get(path, 0)
    )
    print("the shards' listings do not add up to the census: " + "; ".join(diff))
    sys.exit(1)
print(f"PASS: {GO_SHARDS} shards list {sum(listed.values())} mutants over {len(listed)} files, the census")
PY

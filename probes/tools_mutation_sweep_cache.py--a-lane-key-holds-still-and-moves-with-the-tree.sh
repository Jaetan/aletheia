#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_sweep_cache.py, the keys of the Go and Rust lanes'
# kept sweeps.
# Claim: on this host's toolchain a lane's key reads the same twice over one
# tree, so a kept sweep is served at all, and it moves when a tracked file of
# the tree changes, so a kept sweep is never served for another tree. What
# each tool says of itself is part of the key, and a tool whose word changed
# from one asking to the next would leave every sweep unserved. The tracked
# file is changed in a scratch copy of the tree the key is pointed at, never in
# the tree.
# Non-zero exit: a key that moves between two readings of one tree, or one a
# tracked file's change leaves where it was. Exits 2 without the venv.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$PATH:$HOME/go/bin"
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

exec "$py" - <<'PY'
import sys

import tools.mutation_sweep_cache as cache
from tools._common import scratch_worktree

failed = False
for kind in ("go", "rust"):
    first, second = cache.lane_sweep_key(kind), cache.lane_sweep_key(kind)
    if first != second:
        print(f"the {kind} key moves between two readings of one tree: {first}, then {second}")
        failed = True
with scratch_worktree(cache.REPO_ROOT) as tree:
    cache.REPO_ROOT = tree
    for kind, relative in (("go", "go/aletheia/doc.go"), ("rust", "rust/src/lib.rs")):
        before = cache.lane_sweep_key(kind)
        _ = (tree / relative).write_text((tree / relative).read_text(encoding="utf-8") + "\n", encoding="utf-8")
        if cache.lane_sweep_key(kind) == before:
            print(f"the {kind} key stays where it was when {relative} changed")
            failed = True
if failed:
    sys.exit(1)
print("PASS: each lane's key reads the same twice and moves with a tracked file")
PY

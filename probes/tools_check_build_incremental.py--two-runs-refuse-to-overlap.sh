#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_build_incremental.py.
# Claim: while another Agda tool holds the repo-wide lock, a run of the gate
# exits naming the holder, and it neither edits a source nor builds. Two runs
# that overlapped would each capture the other's edit as its own original and
# write it back as the restore. The probe works in a scratch copy of the
# working tree, a detached worktree of HEAD with the uncommitted diff applied,
# holds that copy's lock itself, runs the gate from the copy, and reads the
# refusal; the two probed sources are compared before and after, and a copy
# that ends with no build directory is one the gate did not build.
# Non-zero exit: 1 when the gate ran under a held lock, refused without naming
# the holder, or touched a source or built; 2 when the copy cannot be made.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
work=$(mktemp -d) || exit 2
tree=$work/tree
trap 'git worktree remove --force "$tree" > /dev/null 2>&1; rm -rf "$work"' EXIT
git worktree add -q --detach "$tree" HEAD || exit 2
git diff --no-ext-diff --no-color --binary --src-prefix=a/ --dst-prefix=b/ HEAD |
    git -C "$tree" apply --index --allow-empty || exit 2
# The gate anchors its root on this variable before it walks up from its cwd.
ALETHEIA_REPO=$tree "$py" - "$tree" <<'PY'
import fcntl
import os
import subprocess
import sys
from pathlib import Path

tree = Path(sys.argv[1])
fd = os.open(tree / ".agda-tree.lock", os.O_CREAT | os.O_RDWR, 0o644)
fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
os.write(fd, f"{os.getpid()}\n".encode())

sources = [
    tree / "src/Aletheia/Protocol/ResponseFormat.agda",
    tree / "src/Aletheia/DBC/Formatter.agda",
]
before = [s.read_bytes() for s in sources]
run = subprocess.run(
    [sys.executable, "-m", "tools.check_build_incremental"],
    cwd=tree, capture_output=True, text=True, check=False,
)
after = [s.read_bytes() for s in sources]

bad = []
if run.returncode == 0:
    bad.append("the gate ran to a pass while this probe held the lock")
holder = f"another Agda tool holds .agda-tree.lock (pid {os.getpid()}, alive)"
if holder not in run.stderr:
    bad.append("the refusal does not name this probe as the holder")
if before != after:
    bad.append("a source changed under the refused run")
if (tree / "build").exists():
    bad.append("the gate built under the refused run: the copy has a build directory")
if bad:
    print("a second run of the gate does not refuse the way it should:")
    for line in bad:
        print(f"  {line}")
    print((run.stdout + run.stderr)[-800:])
    raise SystemExit(1)
print(f"PASS: the gate reported the lock held by pid {os.getpid()} and touched nothing")
PY

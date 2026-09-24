#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_build_incremental.py.
# Claim: a marker a killed run left in a probed source refuses the next run
# before it builds or captures anything, naming the run that wrote it, whether
# that run still lives, the file, and the edit that restores it. The probe
# plants the marker of a run that has already exited in a scratch copy of the
# working tree, a detached worktree of HEAD with the uncommitted diff applied,
# so the tree itself is never written, and runs the gate from that copy; a
# copy that ends with no build directory is one the gate did not build.
# Non-zero exit: 1 when the gate passes, builds, or refuses without naming the
# run, the file and the repair; 2 when the copy cannot be made.
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
import subprocess
import sys
from pathlib import Path

tree = Path(sys.argv[1])
sys.path.insert(0, str(tree))
from tools.check_build_incremental import MARKER_PREFIX  # noqa: E402

rel = "src/Aletheia/Protocol/ResponseFormat.agda"
src = tree / rel
original = src.read_text(encoding="utf-8")
anchor = '"uncached_atom"'
if anchor not in original:
    print(f"the gate's anchor {anchor} is gone from {rel}")
    raise SystemExit(2)
with subprocess.Popen([sys.executable, "-c", "pass"]) as child:
    child.wait()
marker = f"{MARKER_PREFIX}RF_pid{child.pid}_20260918T000000Z"
src.write_text(original.replace(anchor, f'"uncached_atom_{marker}"'), encoding="utf-8")
run = subprocess.run(
    [sys.executable, "-m", "tools.check_build_incremental"],
    cwd=tree, capture_output=True, text=True, check=False,
)
out = run.stdout + run.stderr

bad = []
if run.returncode == 0:
    bad.append("the gate passed over a marked source")
run_named = f"carries the marker of an interrupted gate run (pid {child.pid}, started 20260918T000000Z, gone)"
if run_named not in out:
    bad.append("the refusal does not name the run, its start and that it is gone")
if rel not in out:
    bad.append(f"the refusal does not name {rel}")
if f'restore it by replacing "uncached_atom_{marker}" with {anchor}' not in out:
    bad.append("the refusal does not print the edit that restores the file")
if (tree / "build").exists():
    bad.append("the gate built over the marked source: the copy has a build directory")
if bad:
    print("a marker a killed run left does not refuse the gate the way it should:")
    for line in bad:
        print(f"  {line}")
    print(out[-800:])
    raise SystemExit(1)
print(f"PASS: the gate refused on the marker of run {child.pid}, named it and its repair, and built nothing")
PY

#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Claim: the file-to-probe lens reports what it says it reports, so a row it produces
# can be diffed against a later round's row and the difference read as the tree moving
# rather than the method moving.
# Probes: .archive/reviews/frev-cpp-2026-09-15/lens/file_probe_map.py.
# The check is a second, independent reading of the same definition: a probe names a
# file when the file's repository-relative path appears in the probe's text. Every row
# the lens emits is checked both ways, so a probe listed without the path, or a probe
# carrying the path and left out, is caught. The row recorded with the round is not
# compared against, because it is a measurement of the tree at one moment and would go
# red on the next edit rather than on a defect.
# Non-zero exit: the lens disagrees with its own definition, or its totals line does
# not count its own rows.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
lens=.archive/reviews/frev-cpp-2026-09-15/lens/file_probe_map.py
python=python/.venv/bin/python
[ -x "$python" ] || python=python3

"$python" - "$lens" <<'PY'
import subprocess
import sys
from pathlib import Path

lens = sys.argv[1]
out = subprocess.run([sys.executable, lens, "cpp"], capture_output=True, text=True, check=True).stdout
rows, summary = [], None
for line in out.split("\n"):
    if not line:
        continue
    if line.startswith("#"):
        summary = line
        continue
    path, _, listed = line.partition("\t")
    rows.append((path, listed.split()))

probes = sorted(p for p in Path("probes").glob("*.sh") if p.name != "run_all.sh")
texts = {str(p): p.read_text(encoding="utf-8") for p in probes}
bad = []
for path, listed in rows:
    for named in listed:
        if named not in texts:
            bad.append(f"{path}: names {named}, which is not a probe")
        elif path not in texts[named]:
            bad.append(f"{path}: named by {named}, which does not carry the path")
    for name, text in texts.items():
        if path in text and name not in listed:
            bad.append(f"{path}: {name} carries the path and is not named")

tracked = subprocess.run(["git", "ls-files", "cpp"], capture_output=True, text=True, check=True).stdout.split()
if len(rows) != len(tracked):
    bad.append(f"the lens emitted {len(rows)} rows for {len(tracked)} tracked files")
named = sum(1 for _, listed in rows if listed)
if summary is None or f"{len(rows)} tracked files" not in summary or f"{named} named by a probe" not in summary:
    bad.append(f"the totals line does not count the rows: {summary}")

for problem in bad:
    print(problem)
sys.exit(1 if bad else 0)
PY
echo "PASS: the lens agrees with its own definition"

#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md.
# Claim: the project tree the README prints is every top-level directory the
# repository tracks, and nothing else. A curated tree reads as the whole shape
# of the project and goes stale silently: this one had lost five directories,
# among them the one holding the continuous-integration orchestrator and every
# gate it runs.
# Non-zero exit: the tree and the repository disagree, either way round.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import subprocess

text = open("README.md", encoding="utf-8").read()
match = re.search(r"^aletheia/\n((?:[├└].*\n)+)", text, re.M)
if match is None:
    print("README.md no longer prints a project tree")
    raise SystemExit(1)
listed = {m.group(1).split("/")[0] for m in re.finditer(r"[├└]── (\S+?)/", match.group(1))}

tracked = {p.split("/")[0]
           for p in subprocess.run(["git", "ls-files"], capture_output=True, text=True,
                                   check=True).stdout.split()
           if "/" in p}

bad = []
for name in sorted(listed - tracked):
    bad.append(f"the tree lists {name}/, which the repository does not track")
for name in sorted(tracked - listed):
    bad.append(f"the repository tracks {name}/, which the tree omits")

if bad:
    print("README.md's project tree and the repository disagree:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print(f"PASS: the tree names all {len(listed)} tracked top-level directories")
PY

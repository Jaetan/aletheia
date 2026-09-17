#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/INDEX.md.
# Claim: every Markdown document the repository tracks under docs/ and AGENTS/,
# and the root AGENTS.md, is named in the index. The index calls itself the
# complete guide to the documentation and had lost eight documents: a
# development note and all seven per-language standards, listing only the root
# standards file while the front page's own tree named the directory beside it.
# A document is named when its file name appears anywhere in the index, which
# is what a reader navigating by name needs; whether the link is well formed is
# tools/check_docs.py's question.
# The archived review records under .archive/ are out of scope: they are a
# record rather than documentation, and the index is a navigation guide.
# Non-zero exit: the tree carries a document the index does not name.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import subprocess
import sys

index = open("docs/INDEX.md", encoding="utf-8").read()
tracked = subprocess.run(["git", "ls-files", "docs/*.md", "AGENTS/*.md", "AGENTS.md"],
                         capture_output=True, text=True, check=True).stdout.split()
if not tracked:
    print("no tracked documents were listed; the probe would pass vacuously")
    raise SystemExit(2)

missing = [p for p in sorted(tracked)
           if p != "docs/INDEX.md" and p.rsplit("/", 1)[-1] not in index]
if missing:
    print("docs/INDEX.md does not name every tracked document:")
    for path in missing:
        print(f"  {path}")
    sys.exit(1)
print(f"PASS: all {len(tracked) - 1} tracked documents are named in the index")
PY

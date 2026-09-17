#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes PROJECT_STATUS.md against docs/PITCH.md.
# Claim: the phase table's word for the current phase is the word every other
# document uses for it. The table said planned while the development guide said
# active track, and the pitch followed first one and then the other, so a reader
# got a different answer depending on which document they opened.
# The table is the authority: the pitch names it as such, so the pitch is
# checked against it rather than the other way round. The development guide is
# not compared word for word, its sentence being prose about what is being
# worked on rather than a status field.
# Non-zero exit: the table's word and the pitch's disagree.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

status = open("PROJECT_STATUS.md", encoding="utf-8").read()
pitch = open("docs/PITCH.md", encoding="utf-8").read()

row = re.search(r"^\|\s*(\d+(?:\.\d+)?)\s*\|[^|]+\|\s*([^|]+?)\s*\|", status, re.M)
rows = re.findall(r"^\|\s*(\d+(?:\.\d+)?)\s*\|[^|]+\|\s*([^|]+?)\s*\|", status, re.M)
if not rows:
    print("PROJECT_STATUS.md no longer carries a phase table")
    raise SystemExit(1)

# The current phase is the last row that is not complete.
current = [(phase, state) for phase, state in rows if state.strip() != "✅"]
if len(current) != 1:
    print(f"the table has {len(current)} phases that are not complete, so there is no one current phase:")
    for phase, state in current:
        print(f"  phase {phase}: {state}")
    raise SystemExit(1)
phase, state = current[0]
word = state.strip().lower()

bad = []
sentence = re.search(rf"Phase {re.escape(phase)} is ([a-z ]+?)[.:,]", pitch)
if sentence is None:
    bad.append(f"docs/PITCH.md says nothing about phase {phase}")
elif sentence.group(1).strip() != word:
    bad.append(f"the table says phase {phase} is {word!r}; the pitch says {sentence.group(1).strip()!r}")

if bad:
    print("the documents do not agree on which phase the project is in:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: phase {phase} is {word!r} in the table and in the pitch")
PY

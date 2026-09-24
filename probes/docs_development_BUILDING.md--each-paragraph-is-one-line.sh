#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md.
# Claim: outside fenced code blocks, every paragraph, list item and blockquote
# is a single line: no prose line is followed by another prose line, no list
# item continues on an indented line, and no blockquote wraps. Headings, table
# rows and list items may follow one another.
# Non-zero exit: a paragraph spans two or more lines.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - "$doc" <<'PY'
import re, sys
lines = open(sys.argv[1], encoding="utf-8").read().splitlines()
fence = False
prev = None  # kind of the previous non-blank line
bad = []
def kind(l):
    if re.match(r"^#{1,6} ", l): return "heading"
    if l.startswith("|"): return "table"
    if re.match(r"^(- |\* |\d+\. )", l): return "item"
    if l.startswith(">"): return "quote"
    if l.startswith((" ", "\t")): return "continuation"
    if l.strip() == "---": return "rule"
    return "prose"
for n, l in enumerate(lines, 1):
    if re.match(r"^\s*(```|~~~)", l):
        fence = not fence; prev = None; continue
    if fence: continue
    if not l.strip():
        prev = None; continue
    k = kind(l)
    if k == "continuation" or (k == "prose" and prev == "prose") or (k == "quote" and prev == "quote"):
        bad.append(n)
    prev = k
if bad:
    print("paragraphs spanning more than one line, at lines:", ", ".join(map(str, bad)))
    sys.exit(1)
print(f"PASS: every paragraph of {len(lines)} lines is one line")
PY

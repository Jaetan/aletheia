#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md against docs/PITCH.md.
# Claim: the two sections both documents open with, the bug classes the proof
# removes and the comparison with the tested decoders, are one text. They are
# deliberately in both, each document being read without the other, and that is
# exactly why nothing stopped them drifting: a commit refreshed the correctness
# sentence in the pitch and left the README asserting the weaker claim, and the
# bug list lost a conjunction on one side only.
# Blank lines and the horizontal rules are dropped before comparing, being each
# document's own spacing, and the comparison stops at the heading that follows,
# which differs by design.
# Non-zero exit: one document's opening argument has moved and the other's has
# not.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

SHARED = ["## The pain this removes", "## Why switch from cantools / python-can / hand-rolled scripts?"]


def section(path, heading):
    """The heading's own text, up to the next heading of the same level."""
    text = open(path, encoding="utf-8").read()
    if heading not in text:
        return None
    start = text.index(heading)
    nxt = re.search(r"^## ", text[start + len(heading):], re.M)
    body = text[start:start + len(heading) + nxt.start()] if nxt else text[start:]
    return [ln for ln in body.split("\n") if ln.strip() and ln.strip() != "---"]


bad = []
for heading in SHARED:
    a, b = section("README.md", heading), section("docs/PITCH.md", heading)
    if a is None or b is None:
        where = "README.md" if a is None else "docs/PITCH.md"
        bad.append(f"{where} no longer carries {heading!r}")
        continue
    if a != b:
        only_a = [ln for ln in a if ln not in b]
        only_b = [ln for ln in b if ln not in a]
        bad.append(f"{heading!r} differs between the two:")
        for ln in only_a:
            bad.append(f"    README only: {ln[:120]}")
        for ln in only_b:
            bad.append(f"    PITCH only:  {ln[:120]}")

if bad:
    print("the opening the two documents share has drifted:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print(f"PASS: the {len(SHARED)} shared sections are one text in both documents")
PY

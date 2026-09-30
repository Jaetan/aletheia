#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its Dependencies and Licenses section.
# Claim: the ledger states no version. Each layer's pins live in the build file
# the section names, and a version written beside them is a second copy every
# bump has to find: before the ledger dropped its version column, all four C++
# pins, the setuptools floor and the GHC packages had fallen behind their build
# files. No table has a version column, no line carries a version number (an
# SPDX licence identifier such as LGPL-3.0 is not one), and the lead still says
# where the versions are.
# Non-zero exit: the section states a version, or no longer says where they are.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import re
import sys

doc = "docs/development/BUILDING.md"
text = open(doc, encoding="utf-8").read()
if "## Dependencies and Licenses" not in text:
    print(f"{doc} has no Dependencies and Licenses section"); sys.exit(1)
start = text.index("## Dependencies and Licenses")
end = text.find("\n## ", start + 1)
section = text[start:] if end == -1 else text[start:end]
bad = []
if "Versions are not repeated here" not in section:
    bad.append("the lead no longer says the versions live in the build files")
for n, line in enumerate(section.splitlines(), 1):
    if line.startswith("|") and re.search(r"\|\s*versions?\s*\|", line, re.I):
        bad.append(f"line {n} of the section is a table with a version column: {line}")
    for m in re.finditer(r"(?<![-\w.])v?\d+\.\d+(?:\.\d+)*", line):
        bad.append(f"line {n} of the section states {m.group()}: {line[:120]}")
if bad:
    print(f"{doc}'s dependency ledger states a version:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: the dependency ledger states no version and names where the pins are")
PY

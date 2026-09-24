#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md, its build-time table and its "Runtime,
# Python layer" table.
# Claim: the Python rows of the ledger name every package python/pyproject.toml
# lists under [build-system] requires and under the can, yaml and excel extras,
# each extra beside its package, and no other package, and each extra's row
# carries the licence pip records for the installed package. The build-time
# row used to state a setuptools floor two majors behind the manifest's.
# Non-zero exit: a manifest package is missing from the ledger, a ledger row
# names a package the manifest does not, an extra sits beside the wrong
# package, or a row's licence differs from pip's.
set -u
cd "$(dirname "$0")/.." || exit 2
doc=docs/development/BUILDING.md
[ -f "$doc" ] || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - "$doc" <<'PY'
import re, sys, tomllib
doc = open(sys.argv[1], encoding="utf-8").read()
section = doc.split("## Dependencies and Licenses", 1)
if len(section) < 2:
    print("no Dependencies and Licenses section"); sys.exit(1)
section = section[1]
proj = tomllib.load(open("python/pyproject.toml", "rb"))
build = [re.split(r"[<>=!~ ]", r, 1)[0].lower() for r in proj["build-system"]["requires"]]
extras = {k: re.split(r"[<>=!~ \[]", v[0], 1)[0].lower() for k, v in proj["project"]["optional-dependencies"].items() if k in ("can", "yaml", "excel")}
status = 0
build_row = next((l for l in section.splitlines() if l.startswith("| setuptools")), "")
for p in build:
    if p not in build_row.lower():
        print(f"build backend not in the ledger's build-time row: {p}"); status = 1
py_table = re.search(r"### Runtime, Python layer.*?\n(\|.*?)\n\n", section, re.S)
rows = [l for l in (py_table.group(1).splitlines() if py_table else []) if l.startswith("|") and not l.startswith("| Package") and not l.startswith("|--")]
seen = {}
licences = {}
for l in rows:
    cells = [c.strip().strip("*").strip("`") for c in l.strip("|").split("|")]
    seen[cells[0].lower()] = cells[1].strip("[]")
    licences[cells[0].lower()] = cells[2]
import subprocess
for pkg, lic in licences.items():
    show = subprocess.run([sys.executable, "-m", "pip", "show", pkg], capture_output=True, text=True).stdout
    got = next((v.strip() for k, v in (line.split(":", 1) for line in show.splitlines() if ":" in line) if k in ("License-Expression", "License") and v.strip()), "")
    if got != lic:
        print(f"{pkg}: the ledger says {lic!r}, pip records {got!r}"); status = 1
for extra, pkg in extras.items():
    if seen.get(pkg) != extra:
        print(f"extra [{extra}] should sit beside {pkg}; the ledger has {seen.get(pkg)!r}"); status = 1
for pkg in seen:
    if pkg not in extras.values():
        print(f"in the ledger but not an extra's package: {pkg}"); status = 1
if status == 0:
    print(f"PASS: {len(build)} build packages and {len(extras)} extras match python/pyproject.toml, each extra with the licence pip records")
sys.exit(status)
PY

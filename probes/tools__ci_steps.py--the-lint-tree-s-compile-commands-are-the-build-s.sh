#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/_ci_steps.py's C++ lint tree against the binding's build tree.
# Claim: the compile database the clang-tidy gate and its two companion checks
# read, cpp/build-tidy's, configured and never built, names the same
# translation units with the same arguments as cpp/build's, which the test
# build writes, once each tree's own directory is read as the other's. The
# gate reads the configured tree so that it need not wait for the test build;
# this is what lets a developer, and every probe that reads cpp/build's
# database, read what the gate reads.
# Non-zero exit: a translation unit one database names and the other does
# not, or one whose arguments differ. Exits 2 when either tree is not
# configured (run tools/run_ci.py, which configures both).
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f cpp/build/compile_commands.json ] || { echo "cpp/build is not configured"; exit 2; }
[ -f cpp/build-tidy/compile_commands.json ] || { echo "cpp/build-tidy is not configured"; exit 2; }
exec "$py" - <<'PY'
import json
import shlex
from pathlib import Path
from typing import NewType

cpp = Path("cpp").resolve()


# A translation unit, a word of its compile command, each with its tree's
# directory read as <tree>, and a tree under cpp/.
Unit = NewType("Unit", str)
Word = NewType("Word", str)
Tree = NewType("Tree", str)


def units(tree: Tree) -> dict[Unit, list[Word]]:
    root = str(cpp / tree)
    entries = json.loads((cpp / tree / "compile_commands.json").read_text(encoding="utf-8"))
    read = {}
    for entry in entries:
        words = entry.get("arguments") or shlex.split(entry["command"])
        unit = Unit(entry["file"].replace(root, "<tree>"))
        read[unit] = [Word(word.replace(root, "<tree>")) for word in words]
    return read


build, lint = units(Tree("build")), units(Tree("build-tidy"))
only = sorted(set(build) ^ set(lint))
differ = sorted(unit for unit in set(build) & set(lint) if build[unit] != lint[unit])
for unit in only:
    print(f"{unit}: in {'cpp/build' if unit in build else 'cpp/build-tidy'} alone")
for unit in differ:
    print(f"{unit}: arguments differ")
if only or differ:
    raise SystemExit(1)
print(f"PASS: both databases name the same {len(build)} translation units with the same arguments")
PY

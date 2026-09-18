#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/build_mull.sh.
# Claim: the installed Mull plugin carries tools/mull/mull-unique-mutant-ids.patch:
# every mutant identifier it emits has a seventh part, a hash of the function's
# mangled name and an ordinal, and no identifier is registered by more than
# one trampoline, so two mutations of one statement or two instantiations of
# one template never share a name. Shown from the IR the plugin emits for a
# library source that instantiates a reader template at several widths: each
# identifier a trampoline stores is checked for its shape, and the set of
# trampolines storing it must be one. Non-zero exit: an identifier lacks the
# seventh part or two trampolines share one, so the plugin in PATH is not the
# one this script builds. Exits 0 with a note when the toolchain or the
# mutation tree is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "Mull plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=cpp/build-mutation/probe-scratch/unique-ids
mkdir -p "$scratch" || exit 2
"$py" - "$scratch" <<'PY'
import collections
import json
import os
import re
import shlex
import subprocess
import sys

scratch = sys.argv[1]
units = [
    e for e in json.load(open("cpp/build-mutation/compile_commands.json", encoding="utf-8"))
    if e["file"].endswith("/cpp/src/json_parse.cpp")
]
if len(units) != 1:
    print("json_parse.cpp is not in the compile database once")
    sys.exit(1)
unit = units[0]
args = shlex.split(unit["command"])
out = []
skip = False
for a in args:
    if skip:
        skip = False
        continue
    if a == "-o":
        skip = True
        continue
    if a == "-c":
        continue
    out.append(a)
ll_path = os.path.abspath(os.path.join(scratch, "json_parse.cpp.ll"))
out += ["-S", "-emit-llvm", "-o", ll_path]
subprocess.run(out, cwd=unit["directory"], check=True, capture_output=True)
lines = open(ll_path, encoding="utf-8", errors="replace").read().split("\n")
SHAPE = re.compile(r"^[a-z_]+:.+:\d+:\d+:\d+:\d+:[0-9a-f]{1,8}\.\d+$")
owners = collections.defaultdict(set)
current = None
for line in lines:
    if line.startswith("define "):
        current = line.split("@", 1)[1].split("(")[0].strip('"')
    elif line == "}":
        current = None
    elif current and 'store ptr @"cxx_' in line:
        owners[line.split('@"')[1].split('"')[0]].add(current)
bad = [i for i in owners if not SHAPE.match(i)]
shared = {i: o for i, o in owners.items() if len(o) > 1}
for i in sorted(bad):
    print(f"no seventh part: {i.split('/cpp/', 1)[-1]}")
for i, o in sorted(shared.items()):
    print(f"shared by {len(o)} trampolines: {i.split('/cpp/', 1)[-1]}")
if not owners:
    print("no mutant found in json_parse.cpp")
print(f"{len(owners)} identifiers, each stored by one trampoline, each with its seventh part")
sys.exit(1 if bad or shared or not owners else 0)
PY

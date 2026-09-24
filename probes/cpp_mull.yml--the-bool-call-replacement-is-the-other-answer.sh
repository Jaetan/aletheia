#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml, against cpp/src/client.cpp.
# Claim: a bool-returning call carries two replacements, the scalar one whose
# constant truncates to false and the bool one answering true, at the same
# site, so a guard that branches on the value is tested for firing and for not
# firing. Shown from the IR the plugin emits for the client: every site of a
# cxx_replace_bool_call_true mutant is also the site of a
# cxx_replace_scalar_call mutant, and there are such sites. Non-zero exit: a
# true site has no false twin, or the unit has no bool site. Exits 0 with a
# note when the toolchain or the mutation tree is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "Mull plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
MULL_CONFIG="$PWD/cpp/mull.yml" "$py" - "$scratch" "client.cpp" <<'PY'
import json, os, re, shlex, subprocess, sys
scratch, unit_name = sys.argv[1], sys.argv[2]
units = [e for e in json.load(open("cpp/build-mutation/compile_commands.json", encoding="utf-8"))
         if e["file"].endswith("/cpp/src/" + unit_name)]
if len(units) != 1:
    print(unit_name + " is not in the compile database once"); sys.exit(1)
unit = units[0]
args = shlex.split(unit["command"]); out = []; skip = False
for a in args:
    if skip: skip = False; continue
    if a == "-o": skip = True; continue
    if a == "-c": continue
    out.append(a)
ll_path = os.path.abspath(os.path.join(scratch, "unit.ll"))
subprocess.run(out + ["-S", "-emit-llvm", "-o", ll_path], cwd=unit["directory"], check=True, capture_output=True)
# The identifiers the trampolines store, as (mutator, line, column).
sites = set()
for m in re.finditer(r'store ptr @"(cxx_[a-z_]+|negate_mutator):[^"]*?/cpp/src/' + re.escape(unit_name) + r':(\d+):(\d+):', open(ll_path, encoding="utf-8", errors="replace").read()):
    sites.add((m.group(1), int(m.group(2)), int(m.group(3))))
source = open("cpp/src/" + unit_name, encoding="utf-8").read().split("\n")
def lines_matching(pattern):
    return {i + 1 for i, text in enumerate(source) if re.search(pattern, text)}

true_sites = {(line, col) for m, line, col in sites if m == "cxx_replace_bool_call_true"}
false_sites = {(line, col) for m, line, col in sites if m == "cxx_replace_scalar_call"}
orphans = sorted(true_sites - false_sites)
status = 0
if orphans:
    print(f"bool-call sites with no scalar twin: {orphans[:10]}"); status = 1
if not true_sites:
    print("no bool-call mutant in the unit"); status = 1
if status == 0:
    print(f"{len(true_sites)} bool-call sites, each with its scalar twin")
sys.exit(status)
PY

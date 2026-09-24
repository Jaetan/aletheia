#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml, against cpp/src/client.cpp.
# Claim: the pointer-call replacement it names is made only where null is an
# answer the caller reads, a call through a function pointer or a result that
# reaches a comparison with null, and never on a call that cannot answer
# null. Shown from the IR the plugin emits for the client: no line that reads
# an exception's message through what() carries a pointer-call mutant, and
# the unit still carries some, so the rule narrows rather than empties. Non-zero
# exit: a what() line carries one, or the unit carries none at all. Exits 0
# with a note when the toolchain or the mutation tree is not available.
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

what_lines = lines_matching(r"\.what\(\)")
pointer = [(line, col) for m, line, col in sites if m == "cxx_replace_pointer_call_null"]
on_what = sorted(line for line, _ in pointer if line in what_lines)
status = 0
if on_what:
    print(f"pointer-call mutants on what() lines {on_what}"); status = 1
if not pointer:
    print("no pointer-call mutant in the unit at all"); status = 1
if not what_lines:
    print("the unit reads no exception message, so the claim has no instance here"); status = 1
if status == 0:
    print(f"{len(pointer)} pointer-call mutants, none on the {len(what_lines)} what() lines")
sys.exit(status)
PY

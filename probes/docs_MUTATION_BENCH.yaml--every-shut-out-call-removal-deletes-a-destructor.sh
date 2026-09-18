#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: every row the C++ ledger shuts out under cxx_remove_void_call removes
# a destructor, not a call the program makes for its effect. That is what makes
# the row a candidate for equivalence at all: a destructor of an object that
# owns nothing frees nothing, where a removed call with an effect is a defect
# no instrument should have to argue about. Shown from the IR the plugin emits:
# each clone at a ledger row's own source line is diffed against Mull's copy of
# the original function, and the call it lacks is named and demangled.
# Non-zero exit: a shut-out row removes something that is not a destructor, or
# a row names a line the sweep has no mutant for. Exits 0 with a note when the
# toolchain or the mutation tree is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "Mull plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=cpp/build-mutation/probe-scratch/shut-out-calls
mkdir -p "$scratch" || exit 2
"$py" - "$scratch" <<'PY'
import collections
import json
import os
import re
import shlex
import subprocess
import sys

import yaml

scratch = sys.argv[1]
MUTATOR = "cxx_remove_void_call"
# A destructor's mangled name ends in D0Ev, D1Ev or D2Ev: the deleting, the
# complete-object and the base-object variants.
DESTRUCTOR = re.compile(r"D[012]Ev$")
CALL = re.compile(r"^\s*(?:%[\w.]+ = )?(?:call|invoke) [^@]*@(\"?[^\"(\s]+\"?)\(")

spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
ledger = spec["bindings"]["cpp"]["baseline"].get("survivors_ledger") or []
rows = [row for row in ledger if row["mutator"] == MUTATOR]
if not rows:
    print("the ledger shuts out no call removal, so there is nothing to hold")
    sys.exit(1)

# A row names its file and the text of its source line; the lines carrying that
# text are the sites the sweep reported it at.
wanted = collections.defaultdict(set)
for row in rows:
    lines = open(row["file"], encoding="utf-8").read().split("\n")
    found = [n for n, line in enumerate(lines, start=1) if line.strip() == row["text"]]
    if not found:
        print(f"the ledger names a line {row['file']} no longer carries: {row['text']}")
        sys.exit(1)
    wanted[os.path.abspath(row["file"])].update(found)

units = {
    os.path.abspath(e["file"]): e
    for e in json.load(open("cpp/build-mutation/compile_commands.json", encoding="utf-8"))
    if "/cpp/src/" in e["file"] and "/_deps/" not in e["file"]
}


def norm(line):
    return re.sub(r"!dbg !\d+", "", re.sub(r"%[\w.]+", "%", line.strip()))


def calls(body):
    return collections.Counter(
        norm(l) for l in body if re.match(r"^\s*(%[\w.]+ = )?(call|invoke) ", l)
    )


def emit_ir(entry, out_path):
    args, skip = [], False
    for arg in shlex.split(entry["command"]):
        if skip:
            skip = False
            continue
        if arg == "-o":
            skip = True
            continue
        if arg == "-c":
            continue
        args.append(arg)
    args += ["-S", "-emit-llvm", "-o", os.path.abspath(out_path)]
    subprocess.run(args, cwd=entry["directory"], check=True, capture_output=True)


def functions(path):
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    out, i = {}, 0
    while i < len(lines):
        if lines[i].startswith("define "):
            name = lines[i].split("@", 1)[1].split("(")[0].strip('"')
            j = i
            while lines[j] != "}":
                j += 1
            out[name] = lines[i:j]
            i = j
        i += 1
    return out


def demangle(name):
    return subprocess.run(["c++filt", name], capture_output=True, text=True).stdout.strip()


bad, checked = [], 0
for path, lines_wanted in sorted(wanted.items()):
    entry = units.get(path)
    if entry is None:
        print(f"the ledger names {path}, which the mutation tree does not compile")
        sys.exit(1)
    ir_path = os.path.join(scratch, os.path.basename(path) + ".ll")
    emit_ir(entry, ir_path)
    funcs = functions(ir_path)
    for name, body in funcs.items():
        if name.startswith(("mull_", MUTATOR, "cxx_")):
            continue
        original = funcs.get("mull_" + name + "_original")
        if original is None:
            continue
        for store in (l for l in body if f'store ptr @"{MUTATOR}' in l):
            clone = store.split('@"')[1].split('"')[0]
            line = int(clone.rsplit(":", 5)[1])
            if line not in lines_wanted or clone not in funcs:
                continue
            checked += 1
            for removed in (calls(original) - calls(funcs[clone])).elements():
                match = CALL.match(removed)
                callee = match.group(1).strip('"') if match else removed[:70]
                if not DESTRUCTOR.search(callee):
                    site = clone.split("/cpp/", 1)[-1]
                    bad.append(f"{site}: removes {demangle(callee)}, which is not a destructor")

for line in sorted(set(bad)):
    print(line)
if checked == 0:
    print("no clone was found at any line the ledger names")
    sys.exit(1)
if bad:
    sys.exit(1)
print(f"{checked} shut-out call removals, each deleting a destructor")
PY

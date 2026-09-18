#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/build_mull.sh.
# Claim: the installed Mull plugin carries tools/mull/libirm-void-call-removal.patch:
# no cxx_remove_void_call mutant it emits for the library sources removes a
# destructor call or a call in a landing pad. Removing a destructor leaks and
# a landing pad runs only while an exception unwinds, so neither is a change
# a test can see; an unpatched plugin emits both and attaches them to the
# statement's source range, where they read as survivors of the named call.
# Shown from the IR the plugin emits: every clone of every void-call mutant is
# diffed against Mull's copy of the original function, and the call it lacks
# is named. Non-zero exit: a mutant removes a destructor or a landing-pad
# call, so the plugin in PATH is not the one this script builds. Exits 0 with
# a note when the toolchain or the mutation tree is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "Mull plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=cpp/build-mutation/probe-scratch/void-calls
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
    if "/cpp/src/" in e["file"] and "/_deps/" not in e["file"]
]
CALL = re.compile(r"^\s*(?:%\d+ = )?(?:call|invoke) [^@]*@(\"?[^\"(\s]+\"?)\(")
DTOR = re.compile(r"D[012]Ev$")


def norm(line):
    return re.sub(r"!dbg !\d+", "", re.sub(r"%\d+", "%", line.strip()))


def calls(body):
    return collections.Counter(norm(l) for l in body if re.match(r"^\s*(%\d+ = )?(call|invoke) ", l))


def blocks(body):
    out, cur = {}, "entry"
    out[cur] = []
    for l in body:
        m = re.match(r"^(\d+):", l)
        if m:
            cur = m.group(1)
            out[cur] = []
        out[cur].append(l)
    return out


bad = []
seen = 0
for unit in units:
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
    ll_path = os.path.join(scratch, os.path.basename(unit["file"]) + ".ll")
    out += ["-S", "-emit-llvm", "-o", os.path.abspath(ll_path)]
    subprocess.run(out, cwd=unit["directory"], check=True, capture_output=True)
    lines = open(ll_path, encoding="utf-8", errors="replace").read().split("\n")
    funcs = {}
    i = 0
    while i < len(lines):
        if lines[i].startswith("define "):
            name = lines[i].split("@", 1)[1].split("(")[0].strip('"')
            j = i
            while lines[j] != "}":
                j += 1
            funcs[name] = lines[i:j]
            i = j
        i += 1
    for fname, body in funcs.items():
        if fname.startswith(("mull_", "cxx_")):
            continue
        orig = "mull_" + fname + "_original"
        if orig not in funcs:
            continue
        oblocks = blocks(funcs[orig])
        for st in (l for l in body if 'store ptr @"cxx_remove_void_call' in l):
            clone = st.split('@"')[1].split('"')[0]
            if clone not in funcs:
                continue
            seen += 1
            cblocks = blocks(funcs[clone])
            for label, olines in oblocks.items():
                removed = calls(olines) - calls(cblocks.get(label, []))
                for k in removed.elements():
                    m = CALL.match(k)
                    callee = m.group(1).strip('"') if m else k
                    site = clone.split("/cpp/", 1)[1]
                    if DTOR.search(callee):
                        bad.append(f"{site}: removes the destructor {callee}")
                    elif any("landingpad" in l for l in olines):
                        bad.append(f"{site}: removes {callee} in a landing pad")
for line in sorted(set(bad)):
    print(line)
if seen == 0:
    print("no void-call mutant found in the library sources")
sys.exit(1 if bad or seen == 0 else 0)
PY

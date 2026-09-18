#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml.
# Claim: every surviving cxx_remove_void_call mutant of the library sources
# removes nothing but the destructor of a temporary, or nothing at all. Mull
# maps the void calls of a statement to the statement's source range, so a
# call such as push_back(make()) or doc.open(path.string()) yields a mutant
# at the site that deletes only the temporary's destructor, and the named
# call itself has no mutant. Shown from the IR the plugin emits: for each
# surviving identifier, every clone the trampoline can dispatch is diffed
# against Mull's copy of the original function, and the calls it lacks are
# named. The one exception is named below by its file and source text: the
# client drops its last frames at both ends of a stream, as the Go client
# does, so one of the two clears is unobservable whichever end a test looks
# at. Non-zero exit: a surviving void-call removal removes a call that is
# neither a destructor nor that exception, which is a test gap and not a
# tool artifact. Exits 0 with a note when the toolchain or the mutation tree
# is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no compile database, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-void-calls.json
scratch=cpp/build-mutation/probe-scratch/void-calls
rm -f "$report"
mkdir -p "$scratch" || exit 2
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests \
        --report-name=probe-void-calls --reporters=Elements > /dev/null 2>&1) || true
[ -s "$report" ] || {
    echo "the sweep produced no report"
    exit 1
}
"$py" - "$report" "$scratch" <<'PY'
import collections
import json
import os
import re
import shlex
import subprocess
import sys

report, scratch = sys.argv[1], sys.argv[2]
survivors = {
    m["id"]
    for f in json.load(open(report, encoding="utf-8"))["files"].values()
    for m in f.get("mutants", [])
    if m["status"] == "Survived" and m["mutatorName"] == "cxx_remove_void_call"
}
units = [
    e for e in json.load(open("cpp/build-mutation/compile_commands.json", encoding="utf-8"))
    if "/cpp/src/" in e["file"] and "/_deps/" not in e["file"]
]
CALL = re.compile(r"^\s*(?:%\d+ = )?(?:call|invoke) [^@]*@(\"?[^\"(\s]+\"?)\(")
DTOR = re.compile(r"D[012]Ev$")
EXEMPT = {("src/client.cpp", "last_frames_.clear();")}


def site(mutant_id):
    rel, line = mutant_id.split("/cpp/", 1)[1].split(":")[:2]
    with open("cpp/" + rel, encoding="utf-8") as src:
        return rel, src.read().split("\n")[int(line) - 1].strip()


def norm(line):
    return re.sub(r"!dbg !\d+", "", re.sub(r"%\d+", "%", line.strip()))


def calls(body):
    return collections.Counter(norm(l) for l in body if re.match(r"^\s*(%\d+ = )?(call|invoke) ", l))


bad = []
seen = set()
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
        ocalls = calls(funcs[orig])
        for st in (l for l in body if 'store ptr @"cxx_remove_void_call' in l):
            clone = st.split('@"')[1].split('"')[0]
            base = re.sub(r"\.\d+$", "", clone)
            if base not in survivors or clone not in funcs:
                continue
            seen.add(base)
            for k in (ocalls - calls(funcs[clone])).elements():
                m = CALL.match(k)
                callee = m.group(1).strip('"') if m else k
                if not DTOR.search(callee) and site(base) not in EXEMPT:
                    bad.append((base.split("/cpp/", 1)[1], callee))
for base, callee in sorted(set(bad)):
    print(f"{base}: removes {callee}")
missing = sorted(s.split("/cpp/", 1)[1] for s in survivors - seen)
for s in missing:
    print(f"{s}: no clone found in the library sources")
sys.exit(1 if bad or missing else 0)
PY

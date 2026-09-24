#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/build_mull.sh, against cpp/src/ffi_backend.cpp.
# Claim: the installed Mull plugin carries the patches that let the call
# mutators reach a call through a function pointer, which is how the backend
# calls every kernel entry. Shown from the IR the plugin emits for the
# backend: the void-call mutator has a mutant on the line that closes the
# kernel state through close_fn_, the scalar-call mutator one on the line
# that builds a frame through build_frame_bin_fn_, and the pointer-call
# mutator one on the line that processes a command through process_fn_.
# Non-zero exit: one of those lines carries no such mutant, so the plugin in
# PATH refuses indirect calls. Exits 0 with a note when the toolchain or the
# mutation tree is not available.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v clang++-23 > /dev/null || { echo "clang-23 not installed, claim untestable"; exit 0; }
[ -f cpp/build-mutation/compile_commands.json ] || { echo "no mutation tree configured, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "Mull plugin not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
MULL_CONFIG="$PWD/cpp/mull.yml" "$py" - "$scratch" "ffi_backend.cpp" <<'PY'
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

status = 0
for mutator, pattern in (("cxx_remove_void_call", r"close_fn_\(state\)"),
                         ("cxx_replace_scalar_call", r"build_frame_bin_fn_\("),
                         ("cxx_replace_pointer_call_null", r"process_fn_\(state")):
    wanted = lines_matching(pattern)
    if not wanted:
        print(f"no line of {unit_name} matches {pattern}"); status = 1; continue
    found = {line for m, line, _ in sites if m == mutator and line in wanted}
    if not found:
        print(f"no {mutator} mutant on the line(s) {sorted(wanted)} of {unit_name}"); status = 1
    else:
        print(f"{mutator} reaches line {sorted(found)}")
sys.exit(status)
PY

#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: every file the C++ hot_path list names is on the mutation surface,
# which means a dry run over the mutation binary lists at least one mutant in
# it. Before the fix the list named the two loaders and the enricher while no
# suite that reached them was linked into the mutation binary, and the plugin's
# junk detector, re-parsing without the recorded flags, dropped every mutant of
# most units besides, so the list described a surface the lane did not have.
# Non-zero exit: a listed file has no mutant in the dry run. Exits 0 with a
# note when Mull or the mutation tree is not available, since the claim is
# untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-hot-path.json
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests --dry-run \
        --report-name=probe-hot-path --reporters=Elements > /dev/null 2>&1) || {
    echo "the dry run did not run"
    exit 1
}
"$py" - "$report" <<'PY'
import json
import sys

import yaml

report = json.load(open(sys.argv[1], encoding="utf-8"))
counts = {
    path: len(entry.get("mutants", []))
    for path, entry in report["files"].items()
}
spec = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))
missing = []
for rel in spec["bindings"]["cpp"]["hot_path"]:
    n = sum(c for path, c in counts.items() if path.endswith("/" + rel))
    print(f"  {n:4d} {rel}")
    if n == 0:
        missing.append(rel)
if missing:
    print("hot-path files with no mutant in the dry run: " + ", ".join(missing))
    sys.exit(1)
PY

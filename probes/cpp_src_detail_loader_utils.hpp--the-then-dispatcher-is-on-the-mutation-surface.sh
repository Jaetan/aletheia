#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/detail/loader_utils.hpp.
# Claim: the mutation lane sees the then-dispatcher. Its branches are
# string_view comparisons, which Mull's default mutators never touch, so the
# lane reported a clean score over a function it had never mutated; with the
# call mutators configured in cpp/mull.yml, a dry run over the mutation tree
# lists at least one mutant in this header, and every one of them is in the
# dispatcher or the predicates beside it rather than nowhere. Non-zero exit: the
# dry run lists no mutant in the header. Exits 0 with a note when Mull or the
# mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-surface.json
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests --dry-run \
        --report-name=probe-surface --reporters=Elements > /dev/null 2>&1) || {
    echo "the dry run did not run"
    exit 1
}
"$py" - "$report" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
header = "cpp/src/detail/loader_utils.hpp"
mutants = [
    m for path, entry in report["files"].items() if path.endswith(header)
    for m in entry.get("mutants", [])
]
if not mutants:
    print(f"the dry run lists no mutant in {header}")
    sys.exit(1)
lines = sorted({m["location"]["start"]["line"] for m in mutants})
print(f"  {len(mutants)} mutants in {header} at lines {lines}")
PY

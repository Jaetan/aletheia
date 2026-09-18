#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml.
# Claim: the test sources are held out of the mutation surface and the library
# headers they instantiate are not. A mutant in a test measures the harness,
# and one in a fixture's write loop ran until the runner killed the process,
# leaving a multi-gigabyte file behind each time; a library header compiled
# only through a test, such as the loaders' dispatcher through its unit test,
# is library code and keeps its mutants. Non-zero exit: a dry run over the
# mutation tree lists a mutant under cpp/tests, or none in
# cpp/src/detail/loader_utils.hpp. Exits 0 with a note when Mull or the
# mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-held-out.json
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests --dry-run \
        --report-name=probe-held-out --reporters=Elements > /dev/null 2>&1) || {
    echo "the dry run did not run"
    exit 1
}
"$py" - "$report" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
in_tests = {
    path for path, entry in report["files"].items()
    if "/cpp/tests/" in path and entry.get("mutants")
}
header = sum(
    len(entry.get("mutants", [])) for path, entry in report["files"].items()
    if path.endswith("/cpp/src/detail/loader_utils.hpp")
)
bad = False
if in_tests:
    print("mutants listed under cpp/tests: " + ", ".join(sorted(in_tests)))
    bad = True
if header == 0:
    print("no mutant in cpp/src/detail/loader_utils.hpp")
    bad = True
sys.exit(1 if bad else 0)
PY

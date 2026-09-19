#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/mull.yml.
# Claim: the test double under cpp/src/detail is held out of the mutation
# surface. Only the tests include it, so a mutant in it measures the harness
# rather than the library, the reason the test sources are held out; the
# library's other detail sources keep their mutants. Non-zero exit: a dry run
# over the mutation tree lists a mutant in cpp/src/detail/mock_backend.hpp,
# or none in cpp/src/detail/ffi_logic.cpp. Exits 0 with a note when Mull or
# the mutation tree is not available, since the claim is untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v mull-runner-23 > /dev/null || { echo "Mull not installed, claim untestable"; exit 0; }
[ -x cpp/build-mutation/unit_tests ] || { echo "no mutation tree built, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
report=cpp/build-mutation/probe-test-double.json
(cd cpp/build-mutation &&
    env -u ALETHEIA_LIB ALETHEIA_REPO_ROOT="$OLDPWD" mull-runner-23 ./unit_tests --dry-run \
        --report-name=probe-test-double --reporters=Elements > /dev/null 2>&1) || {
    echo "the dry run did not run"
    exit 1
}
"$py" - "$report" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
def mutants(suffix):
    return sum(len(e.get("mutants", [])) for p, e in report["files"].items() if p.endswith(suffix))
bad = False
if mutants("/cpp/src/detail/mock_backend.hpp"):
    print("mutants listed in cpp/src/detail/mock_backend.hpp")
    bad = True
if mutants("/cpp/src/detail/ffi_logic.cpp") == 0:
    print("no mutant in cpp/src/detail/ffi_logic.cpp")
    bad = True
sys.exit(1 if bad else 0)
PY

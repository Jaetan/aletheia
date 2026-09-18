#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_run.py against docs/MUTATION_BENCH.yaml.
# Claim: the Go lane refuses a sweep that timed out instead of testing. A mutant
# gremlins could not finish is neither killed nor lived, so a sweep that timed
# out on nearly all of them reports no survivors and full efficacy, which is
# exactly what the drift gate used to read as a pass. The run that showed it had
# a second sweep beside it: 39 killed, 622 timed out, no survivors reported.
# The gate is driven here through the summary parser rather than by reproducing
# such a run, so the check is deterministic and needs no second sweep: the
# recorded tails of both runs go in, and the two verdicts come out.
# Non-zero exit: the gate takes the loaded run, or refuses the clean one.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import sys

sys.path.insert(0, ".")
from tools.mutation_run import drift_for, load_spec, parse_gremlins_summary

bindings = load_spec().get("bindings", {})
ceiling = bindings.get("go", {}).get("baseline", {}).get("timeout_ceiling")
if ceiling is None:
    print("docs/MUTATION_BENCH.yaml records no timeout ceiling for the Go lane")
    raise SystemExit(1)


def tail(killed, lived, not_covered, timed_out):
    return (
        "Mutation testing completed in 1 minute 44 seconds\n"
        f"Killed: {killed}, Lived: {lived}, Not covered: {not_covered}\n"
        f"Timed out: {timed_out}, Not viable: 0, Skipped: 0\n"
        "Test efficacy: 100.00%\n"
        "Mutator coverage: 84.29%\n"
    )


bad = []

# The run that had a second sweep beside it.
loaded = parse_gremlins_summary(tail(39, 0, 102, 622), "recorded")
if loaded.timeouts != 622:
    bad.append(f"the parser read {loaded.timeouts} timeouts out of the loaded run, not 622")
verdict = drift_for(loaded, bindings)
if verdict.get("status") != "regression":
    bad.append(f"the loaded run verdicts {verdict.get('status')!r}, not a regression: {verdict}")

# The recorded baseline's own run.
base = bindings.get("go", {}).get("baseline", {})
clean = parse_gremlins_summary(
    tail(base.get("total_mutants", 0), base.get("survivors", 0),
         base.get("not_covered", 0), base.get("timeouts", 0)), "recorded")
verdict = drift_for(clean, bindings)
if verdict.get("status") != "ok":
    bad.append(f"the recorded clean run verdicts {verdict.get('status')!r}, not ok: {verdict}")

# A sweep one mutant over the ceiling is refused, so the ceiling is the edge.
edge = parse_gremlins_summary(tail(600, 0, 118, ceiling + 1), "recorded")
if drift_for(edge, bindings).get("status") != "regression":
    bad.append(f"a sweep with {ceiling + 1} timeouts is taken, where the ceiling is {ceiling}")
edge_ok = parse_gremlins_summary(tail(600, 0, 118, ceiling), "recorded")
if drift_for(edge_ok, bindings).get("status") != "ok":
    bad.append(f"a sweep with exactly {ceiling} timeouts is refused, where the ceiling is {ceiling}")

if bad:
    print("the Go mutation lane's drift gate does not read the timeout bucket:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print(f"PASS: the lane refuses a sweep past {ceiling} timeouts and takes one at or below it")
PY

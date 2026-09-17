#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/MUTATION_BENCH.yaml.
# Claim: the Go baseline records a run, not a target. A sweep of the package
# generates the recorded number of mutants and leaves none alive.
#
# Only those two are compared. Every mutant gremlins generates lands in exactly
# one bucket, and the generated total is a property of the source, but the split
# between killed and timed out moves with the machine's load, so the killed
# count and the timeout count are what one run produced rather than what every
# run produces.
# Non-zero exit: the record and a sweep disagree. Exits 0 with a note when
# gremlins is not installed, the claim being untestable then.
set -u
cd "$(dirname "$0")/.." || exit 2
export PATH="$PATH:$HOME/go/bin"
command -v gremlins > /dev/null || { echo "gremlins not installed, claim untestable"; exit 0; }
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
[ -f build/libaletheia-ffi.so ] || { echo "no kernel built, claim untestable"; exit 0; }

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
(cd go && ALETHEIA_LIB="$OLDPWD/build/libaletheia-ffi.so" gremlins unleash ./aletheia) \
	> "$work/sweep.txt" 2>&1 || {
	echo "the sweep did not run:"
	tail -3 "$work/sweep.txt" | sed 's/^/  /'
	exit 1
}

"$py" - "$work/sweep.txt" <<'PY'
import re
import sys

import yaml

raw = open(sys.argv[1], encoding="utf-8").read()
counts = {}
for name, key in (("Killed", "killed"), ("Lived", "survivors"), ("Not covered", "not_covered"),
                  ("Timed out", "timeouts"), ("Not viable", "not_viable"), ("Skipped", "skipped")):
    match = re.search(rf"{name}:\s*(\d+)", raw)
    if match is None:
        print(f"the sweep's summary carries no {name} count")
        raise SystemExit(1)
    counts[key] = int(match.group(1))
observed = {"survivors": counts["survivors"], "generated": sum(counts.values())}

baseline = yaml.safe_load(open("docs/MUTATION_BENCH.yaml", encoding="utf-8"))["bindings"]["go"]["baseline"]
bad = {k: (baseline.get(k), v) for k, v in observed.items() if baseline.get(k) != v}
for key, (was, now) in bad.items():
    print(f"{key}: recorded {was}, a sweep gives {now}")
if bad:
    raise SystemExit(1)
print(f"PASS: the Go baseline records a run ({observed['generated']} generated, "
      f"{observed['survivors']} alive)")
PY

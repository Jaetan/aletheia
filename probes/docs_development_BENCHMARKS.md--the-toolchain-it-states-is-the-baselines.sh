#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: no runtime version the document states in prose contradicts what a
# committed baseline's system object records, and the document names that
# object as where the versions are. The document stated one rustc for the
# whole set while the Rust latency baseline, re-taken later, recorded another;
# a version list in prose goes stale one file at a time.
# Non-zero exit: a stated version is not the one every baseline of that
# runtime records, or the document no longer points at the system object.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import glob, json, re, sys

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()
prose = re.sub(r"```.*?```", "", text, flags=re.S)
prose = re.sub(r"`[^`]*`", "", prose)
bad = []
if "`system` object" not in text:
    bad.append("the document does not name the system object as where the runtime versions are")

recorded = {"go": set(), "python": set(), "rust": set()}
for path in glob.glob("benchmarks/results/*_baseline.json"):
    system = json.load(open(path, encoding="utf-8"))["system"]
    for key in recorded:
        if key in system:
            recorded[key].add(str(system[key]))

stated = {
    "go": re.findall(r"\bGo (\d+\.\d+(?:\.\d+)?)", prose),
    "python": re.findall(r"\bPython (\d+\.\d+(?:\.\d+)?)", prose),
    "rust": re.findall(r"\brustc (\d+\.\d+(?:\.\d+)?)", prose),
}
for key, versions in stated.items():
    for v in versions:
        held = recorded[key]
        if not all(v in h for h in held):
            bad.append(f"the document states {key} {v}; the baselines record {sorted(held)}")

if bad:
    print(f"{doc} states a toolchain the baselines do not all record:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: every runtime version the document states is the one every baseline records, and the system object is named")
PY

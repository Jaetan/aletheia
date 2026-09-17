#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: every cell of the canonical throughput table is the mean of the lane of
# that name in the committed baseline set, benchmarks/results/*_throughput_baseline.json,
# and the standard-deviation bound the section states holds over the same set.
# A hand-typed table drifts silently from the artifact the gate compares against:
# this one had, by as much as half on one lane, while still reading as current.
# Every lane the baselines carry must appear, so a lane added to the schema
# cannot be left out of the table.
# Non-zero exit: a cell, the bound, or the lane roster has left the baselines.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import json
import re
import sys

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()

base = {}
for b in ("cpp", "go", "python", "rust"):
    for row in json.load(open(f"benchmarks/results/{b}_throughput_baseline.json", encoding="utf-8"))["results"]:
        base.setdefault(row["name"], {})[b] = row

section = text[text.index("## Canonical Results"):text.index("## Cross-Language Runner")]
header = next(l for l in section.split("\n") if l.startswith("| Benchmark "))
columns = [c.strip().removesuffix(" (fps)").replace("C++", "cpp").replace("Rust", "rust")
           .replace("Go", "go").replace("Python", "python") for c in header.strip("|").split("|")][1:]

bad = []
seen = set()
for line in section.split("\n"):
    if not line.startswith("| ") or line.startswith(("| Benchmark", "|---")):
        continue
    cells = [c.strip() for c in line.strip().strip("|").split("|")]
    lane, values = cells[0], cells[1:]
    if lane not in base:
        bad.append(f"the table has a lane the baselines do not: {lane!r}")
        continue
    seen.add(lane)
    if len(values) != len(columns):
        bad.append(f"{lane}: {len(values)} cells under {len(columns)} columns")
        continue
    for binding, printed in zip(columns, values, strict=True):
        want = f"{base[lane][binding]['fps_mean']:,.0f}"
        if printed != want:
            bad.append(f"{lane}, {binding}: the table says {printed}, the baseline {want}")

for lane in base:
    if lane not in seen:
        bad.append(f"the baselines carry a lane the table omits: {lane!r}")

# The stated bound, read out of the prose rather than restated here.
m = re.search(r"standard deviation exceeds ([\d.]+)% of its mean", section)
if not m:
    bad.append("the section no longer states a standard-deviation bound")
else:
    claimed = float(m.group(1))
    worst_lane, worst = max(
        ((f"{lane} {b}", 100 * r["fps_stdev"] / r["fps_mean"]) for lane, v in base.items() for b, r in v.items()),
        key=lambda t: t[1])
    if round(worst, 1) != claimed:
        bad.append(f"the section claims at most {claimed}%, the baselines' worst is {worst:.1f}% ({worst_lane})")

if bad:
    print(f"{doc}'s canonical table has left the committed baseline set:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: {len(seen)} lanes across {len(columns)} bindings match the committed baselines")
PY

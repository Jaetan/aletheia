#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: the two measurements the document states in prose rather than in its
# table still carry the values their sources hold. The per-frame latency figures
# are the committed C++ latency baseline's own streaming lane, and the residency
# sentence states the budget and the frame count the Python residency test
# asserts. Both are numbers a reader takes as current and neither is compared
# against anything by a gate: the table has a probe, these did not, and the
# latency figures had already been left behind once by a runner change that
# moved what the baselines measure.
# Non-zero exit: a prose measurement has left the artifact or the test it names.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import ast
import json
import re
import sys

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()
bad = []

# The latency figures, against the lane of that name in the committed baseline.
lane = "CAN 2.0B Streaming LTL"
row = next((r for r in json.load(open("benchmarks/results/cpp_latency_baseline.json", encoding="utf-8"))["results"]
            if r["name"] == lane), None)
if row is None:
    print(f"the committed C++ latency baseline no longer carries the {lane!r} lane")
    raise SystemExit(2)

m = re.search(r"median of ([\d.]+) µs and a mean of ([\d.]+) µs", text)
if not m:
    bad.append("the document no longer states a per-frame median and mean")
else:
    for what, printed, held in (("median", m.group(1), row["p50_us"]), ("mean", m.group(2), row["mean_us"])):
        if float(printed) != held:
            bad.append(f"the {what} reads {printed} µs, the committed baseline holds {held} µs")

# The residency sentence, against the test that asserts it.
tree = ast.parse(open("python/tests/test_streaming_residency.py", encoding="utf-8").read())
named = {}
for node in ast.walk(tree):
    if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        named[node.target.id] = node.value
if "_MAX_GROWTH_KIB" not in named or "_CASES" not in named:
    print("python/tests/test_streaming_residency.py no longer names its budget and its cases")
    raise SystemExit(2)
budget_mib = eval(ast.unparse(named["_MAX_GROWTH_KIB"]), {"__builtins__": {}}) / 1024
counts = {frames for _, frames in ast.literal_eval(named["_CASES"])}

m = re.search(r"a session of ([\d,]+) frames whose peak resident set grows by (\d+) MiB", text)
if not m:
    bad.append("the document no longer states a residency budget over a frame count")
else:
    printed_frames = int(m.group(1).replace(",", ""))
    if printed_frames not in counts:
        bad.append(f"the document names a session of {printed_frames:,} frames, the test runs {sorted(counts)}")
    if float(m.group(2)) != budget_mib:
        bad.append(f"the document states a {m.group(2)} MiB budget, the test asserts {budget_mib:.0f} MiB")

if bad:
    print(f"{doc} states a measurement its source does not hold:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: the latency figures are the committed baseline's and the residency budget is the test's ({budget_mib:.0f} MiB)")
PY

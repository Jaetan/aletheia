#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh against the four harnesses.
# Claim: the runner tells every binding how much to warm before timing latency,
# so no binding's own default decides what the published numbers measure. The
# four defaults do not agree: Python and C++ warm 500 operations and Go and
# Rust warm 2, and the runner used to pass nothing, so each committed latency
# baseline was taken a different way. The flag is pinned for the mode by
# benchmarks/SCHEMA.yaml, which is read here rather than restated.
# The check is of the runner's four lanes, one per binding, because what the
# ruling asks for is that each is told: a run would show only that the flag was
# accepted, which the schema gate already drives with a warmup of zero.
# Non-zero exit: a lane no longer carries the flag, or the schema stopped
# pinning it.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

import yaml

runner = open("benchmarks/run_all.sh", encoding="utf-8").read()
bad = []

if "--warmup" not in yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))["modes"]["latency"]["flags"]:
    bad.append("benchmarks/SCHEMA.yaml no longer pins --warmup for the latency mode")

lanes = {"PYTHON_ARGS": "Python", "CPP_ARGS": "C++", "GO_ARGS": "Go", "RUST_ARGS": "Rust"}
for var, binding in lanes.items():
    arm = re.search(rf"^\s*latency\)\s+{var}.*$", runner, re.M)
    if arm is None:
        bad.append(f"the runner has no latency lane for {binding}")
        continue
    if "--warmup" not in arm.group(0):
        bad.append(f"the {binding} latency lane is not told how much to warm: {arm.group(0).strip()}")

if not re.search(r"^WARMUP=\d+$", runner, re.M):
    bad.append("the runner records no warmup to pass")

if bad:
    print("the runner does not tell every binding how much to warm:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: all {len(lanes)} latency lanes are told how much to warm")
PY

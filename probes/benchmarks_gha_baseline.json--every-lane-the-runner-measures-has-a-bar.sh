#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/gha_baseline.json, the runner bar tools/benchmark_gate.py
# reads.
# Claim: the gate's bindings are the languages benchmarks/SCHEMA.yaml names,
# and the baseline carries every throughput lane the schema pins for each of
# them, with a positive number. The gate skips a lane the baseline lacks
# without a word, so a missing bar is a lane no regression can fail.
# Non-zero exit: a binding or lane is missing, extra, or non-positive. Exits 2
# when the interpreter or its YAML reader is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import json, sys
from pathlib import Path
import yaml
from tools.benchmark_gate import BINDINGS
schema = yaml.safe_load(Path("benchmarks/SCHEMA.yaml").read_text(encoding="utf-8"))
languages = set(schema["envelope"]["languages"])
lanes = set(schema["modes"]["throughput"]["lane_names"])
baseline = json.loads(Path("benchmarks/gha_baseline.json").read_text(encoding="utf-8"))
bad = 0
if set(BINDINGS) != languages:
    print(f"gate reads {sorted(BINDINGS)}, schema names {sorted(languages)}"); bad = 1
if set(baseline) != set(BINDINGS):
    print(f"baseline has {sorted(baseline)}, gate reads {sorted(BINDINGS)}"); bad = 1
for binding in BINDINGS:
    rows = baseline.get(binding, {})
    if set(rows) != lanes:
        print(f"{binding}: lanes {sorted(set(rows) ^ lanes)} differ from the schema"); bad = 1
    for lane, fps in rows.items():
        if not (isinstance(fps, (int, float)) and fps > 0):
            print(f"{binding} / {lane}: {fps!r} is not a positive number"); bad = 1
print(f"{len(baseline)} bindings, {sum(len(r) for r in baseline.values())} lanes")
sys.exit(bad)
PY

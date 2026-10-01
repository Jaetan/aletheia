#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the Python setup steps of .github/workflows/.
# Claim: every job that installs into the dev venv sets Python up with pip's
# wheel cache, keyed on python/pyproject.toml, before it installs. The venv is
# created afresh on every run, so without the cache the install fetches every
# wheel again, and its time is whatever the package index answers in: about
# 20 s in most jobs, 97 s and 255 s in two of one run.
# Non-zero exit: a job installs into python/.venv with no setup-python step
# ahead of it carrying `cache: pip` and that dependency path, or no such job
# is found. Exits 2 when the interpreter or its YAML reader is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
exec "$py" - <<'PY'
import sys
from pathlib import Path

import yaml

faults = []
jobs = 0
for path in sorted(Path(".github/workflows").glob("*.yml")):
    doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    for name, job in (doc.get("jobs") or {}).items():
        steps = job.get("steps") or []
        installs = [i for i, step in enumerate(steps) if "python/.venv/bin/pip install" in str(step.get("run", ""))]
        if not installs:
            continue
        jobs += 1
        setups = [
            i for i, step in enumerate(steps)
            if "actions/setup-python@" in str(step.get("uses", ""))
            and (step.get("with") or {}).get("cache") == "pip"
            and (step.get("with") or {}).get("cache-dependency-path") == "python/pyproject.toml"
        ]
        if not setups or setups[0] > installs[0]:
            faults.append(f"{path.name}:{name} installs into the dev venv without pip's cache set up ahead of it")
for line in faults:
    print(line)
if jobs == 0:
    print("no job installs into the dev venv")
    sys.exit(1)
if faults:
    sys.exit(1)
print(f"PASS: {jobs} jobs install into the dev venv, each with pip's cache")
PY

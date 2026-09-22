#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the build-tree cache steps of .github/workflows/.
# Claim: every restore and save under the build-tree key names one path set,
# and that set holds _build, where Agda writes its interface files. The
# platform hashes the path list into an entry's version, so a step naming a
# different set misses however the key matches; and a tree without the
# interfaces hands the proof gate a cold closure on every run.
# Non-zero exit: two cache steps name different path sets, or a set omits
# _build. Exits 2 when the interpreter or its YAML reader is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import sys
from pathlib import Path
import yaml
sets = {}
for path in sorted(Path(".github/workflows").glob("*.yml")):
    doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    for name, job in doc.get("jobs", {}).items():
        for step in job.get("steps", []):
            with_ = step.get("with") or {}
            if "actions/cache" in str(step.get("uses", "")) and str(with_.get("key", "")).startswith("build-tree-"):
                paths = tuple(line.strip() for line in str(with_.get("path", "")).splitlines() if line.strip())
                sets.setdefault(paths, []).append(f"{path.name}:{name}")
for paths, where in sets.items():
    print(f"{list(paths)} in {', '.join(where)}")
if not sets:
    print("no build-tree cache step found"); sys.exit(1)
if len(sets) != 1:
    print(f"{len(sets)} path sets"); sys.exit(1)
(paths,) = sets
sys.exit(0 if "_build" in paths else 1)
PY

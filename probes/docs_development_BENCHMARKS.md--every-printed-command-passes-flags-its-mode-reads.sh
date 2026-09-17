#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: every benchmark command the document prints passes only flags the mode
# it names actually reads. benchmarks/SCHEMA.yaml pins the flag set per mode and
# is read here rather than restated. The defect this catches is silent: all four
# binaries declare one flag set for every mode, so a frame count handed to the
# latency or the scaling mode is accepted, discarded, and the run measures its
# default while the reader believes they asked for something else.
# The runner's own flags are checked against its argument parser the same way.
# Non-zero exit: a printed command passes a flag its mode does not read.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

import yaml

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()
schema = yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))["modes"]

# The runner takes its own three flags, read from its parser rather than typed.
runner = set(re.findall(r"^\s*--(\w+)\)", open("benchmarks/run_all.sh", encoding="utf-8").read(), re.M))
if not runner:
    print("could not read run_all.sh's flags from its argument parser")
    raise SystemExit(2)

bad = []
for line in text.split("\n"):
    stripped = line.strip()
    flags = re.findall(r"--[a-z-]+", stripped)
    if not flags:
        continue
    if "run_all.sh" in stripped and stripped.startswith("./"):
        # A runner line names its mode with --bench, not positionally.
        unknown = [f for f in flags if f[2:] not in runner]
        if unknown:
            bad.append(f"{stripped}\n    runner does not take {', '.join(unknown)}")
        continue
    m = re.match(r"\./\S*benchmark\s+(\w+)\s", stripped)
    if not m:
        continue
    mode = m.group(1)
    if mode not in schema:
        bad.append(f"{stripped}\n    no such mode: {mode}")
        continue
    allowed = set(schema[mode]["flags"])
    unread = [f for f in flags if f not in allowed]
    if unread:
        bad.append(f"{stripped}\n    the {mode} mode does not read {', '.join(unread)}"
                   f" (SCHEMA.yaml pins {', '.join(sorted(allowed))})")

if bad:
    print(f"{doc} prints a command whose flags its mode does not read:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: every printed benchmark command passes flags its mode reads")
PY

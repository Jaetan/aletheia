#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md and CLAUDE.md.
# Claim: every benchmark command either document prints passes only flags the
# mode it names actually reads. benchmarks/SCHEMA.yaml pins the binaries' flag
# set per mode and benchmarks/run_all.sh names the runner's, and both are read
# here rather than restated. The defect this catches is silent for a binary:
# all four declare one flag set for every mode, so a frame count handed to the
# latency or the scaling mode is accepted, discarded, and the run measures its
# default while the reader believes they asked for something else. For the
# runner it is loud, the runner refusing such a flag, so a printed command that
# carries one does not run at all.
# Non-zero exit: a printed command passes a flag its mode does not read.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import re
import sys

import yaml

schema = yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))["modes"]

# The runner's flags, read from its parser, and what each of its modes reads,
# read from the table it refuses by.
source = open("benchmarks/run_all.sh", encoding="utf-8").read()
runner = set(re.findall(r"^\s*--(\w+)\)", source, re.M))
reads = {m: set(f.split()) for m, f in re.findall(r'^\s*(\w+)\)\s+READS="([^"]+)"', source, re.M)}
if not runner or not reads:
    print("could not read run_all.sh's flags and per-mode sets from its own source")
    raise SystemExit(2)

bad = []
for doc in ("docs/development/BENCHMARKS.md", "CLAUDE.md"):
  text = open(doc, encoding="utf-8").read()
  for line in text.split("\n"):
    stripped = line.strip()
    flags = re.findall(r"--[a-z-]+", stripped)
    if not flags:
        continue
    if "run_all.sh" in stripped and re.match(r"(\./|bash )", stripped):
        # A runner line names its mode with --bench, and takes the throughput
        # mode when it names none, which is the runner's own default.
        unknown = [f for f in flags if f[2:] not in runner]
        if unknown:
            bad.append(f"{doc}: {stripped}\n    runner does not take {', '.join(unknown)}")
            continue
        m = re.search(r"--bench\s+(\w+)", stripped)
        mode = m.group(1) if m else "throughput"
        if mode not in reads:
            bad.append(f"{doc}: {stripped}\n    the runner has no {mode} mode")
            continue
        unread = [f for f in flags if f != "--bench" and f[2:] not in reads[mode]]
        if unread:
            bad.append(f"{doc}: {stripped}\n    the runner's {mode} mode does not read"
                       f" {', '.join(unread)}, and refuses it"
                       f" (it reads {', '.join('--' + f for f in sorted(reads[mode]))})")
        continue
    m = re.match(r"\./\S*benchmark\s+(\w+)\s", stripped)
    if not m:
        continue
    mode = m.group(1)
    if mode not in schema:
        bad.append(f"{doc}: {stripped}\n    no such mode: {mode}")
        continue
    allowed = set(schema[mode]["flags"])
    unread = [f for f in flags if f not in allowed]
    if unread:
        bad.append(f"{doc}: {stripped}\n    the {mode} mode does not read {', '.join(unread)}"
                   f" (SCHEMA.yaml pins {', '.join(sorted(allowed))})")

if bad:
    print("a printed command passes flags its mode does not read:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print("PASS: every printed benchmark command passes flags its mode reads")
PY

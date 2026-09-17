#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes every tracked file that prints a benchmark command.
# Claim: every benchmark command the tree prints passes only flags the mode it
# names actually reads. The files are found rather than listed, a list being
# the thing that goes stale when a fourth document prints the invocation. benchmarks/SCHEMA.yaml pins the binaries' flag
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
import subprocess
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

# Every tracked file that names the runner or a benchmark binary, less the
# round's archived records, which are the output of runs rather than
# instructions, and the probe store, which builds its commands from variables.
tracked = subprocess.run(["git", "ls-files"], capture_output=True, text=True, check=True).stdout.split()
docs = [p for p in tracked
        if not p.startswith((".archive/", "probes/"))
        and not p.endswith((".json", ".png", ".svg"))]

bad = []
scanned = 0
for doc in docs:
  try:
      text = open(doc, encoding="utf-8").read()
  except (UnicodeDecodeError, IsADirectoryError):
      continue
  if "run_all.sh" not in text and "/benchmark " not in text:
      continue
  scanned += 1
  # An invocation may sit in a fence or inside a code span in a sentence, so it
  # is matched where it starts rather than at the start of a line.
  for stripped in re.findall(r"(?:\./|bash )?(?:benchmarks/run_all\.sh|\S*benchmark) [^`\n]*", text):
    stripped = stripped.strip()
    if "[--" in stripped:
        # A usage synopsis brackets its optional flags and names them all; it
        # is what the runner offers rather than a command anyone runs.
        continue
    flags = re.findall(r"--[a-z-]+", stripped)
    if not flags:
        continue
    if "run_all.sh" in stripped:
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
    m = re.match(r"\S*benchmark\s+(\w+)\s", stripped)
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
print(f"PASS: every benchmark command printed in {scanned} tracked files passes flags its mode reads")
PY

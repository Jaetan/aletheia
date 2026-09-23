#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: the Local baselines section names the committed baseline files by
# the pattern they follow, one file exists for every binding and mode
# benchmarks/SCHEMA.yaml lists and each carries the language and mode its name
# says, and the counts the section states per mode are the counts every row
# of every file records: the frames and runs of a throughput lane, the timed
# operations of a latency lane, and the full trace-size sweep of a scaling
# file. The section did not exist, and the counts a fresh run must reproduce
# were written nowhere a reader would find them.
# Non-zero exit: the section, a file, or a stated count has left the others.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import json, re, sys
import yaml

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()
schema = yaml.safe_load(open("benchmarks/SCHEMA.yaml", encoding="utf-8"))
bad = []
if "## Local baselines" not in text:
    print(f"{doc} has no Local baselines section"); sys.exit(1)
section = text[text.index("## Local baselines"):]
section = section[:section.index("\n## ", 1)] if "\n## " in section[1:] else section
if "`benchmarks/results/<binding>_<mode>_baseline.json`" not in section:
    bad.append("the section does not name the baseline files by their pattern")

def stated(pattern, what):
    m = re.search(pattern, section)
    if not m:
        bad.append(f"the section no longer states {what}")
        return None
    return int(m.group(1).replace(",", ""))

runs = stated(r"throughput baseline is ([\d,]+) runs of", "the throughput run count")
frames = stated(r"throughput baseline is [\d,]+ runs of ([\d,]+) frames", "the throughput frame count")
ops = stated(r"latency baseline ([\d,]+) timed operations", "the latency operation count")
full = len(schema["experiment"]["trace_sizes"]["full"])

for lang in schema["envelope"]["languages"]:
    for mode in schema["envelope"]["benchmarks"]:
        path = f"benchmarks/results/{lang}_{mode}_baseline.json"
        try:
            data = json.load(open(path, encoding="utf-8"))
        except OSError:
            bad.append(f"missing: {path}"); continue
        if data.get("language") != lang or data.get("benchmark") != mode:
            bad.append(f"{path} says {data.get('language')} {data.get('benchmark')}")
            continue
        rows = data["results"]
        if mode == "throughput":
            for r in rows:
                if (r["frames"], r["runs"]) != (frames, runs):
                    bad.append(f"{path}: {r['name']} is {r['runs']} runs of {r['frames']} frames, the section says {runs} of {frames}")
        elif mode == "latency":
            for r in rows:
                if r["count"] != ops:
                    bad.append(f"{path}: {r['name']} counts {r['count']} operations, the section says {ops}")
        else:
            for sweep in ("trace_size_can20", "trace_size_canfd"):
                if len(rows[sweep]) != full:
                    bad.append(f"{path}: {sweep} has {len(rows[sweep])} sizes, the full sweep has {full}")

if bad:
    print(f"{doc}'s Local baselines section has left the files:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
print(f"PASS: every baseline file exists and records {runs} runs of {frames} frames, {ops} operations, or the {full}-size sweep")
PY

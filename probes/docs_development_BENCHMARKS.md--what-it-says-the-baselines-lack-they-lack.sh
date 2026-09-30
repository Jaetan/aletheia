#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BENCHMARKS.md.
# Claim: while the Local baselines section says the committed files carry
# neither a `parameters` object nor a C++ compiler, no committed baseline
# carries a `parameters` object and no C++ baseline's `system` names a
# compiler; and while the section does not say so, every baseline carries
# both, so the sentence goes the day the baselines are re-taken rather than
# outliving them.
# Non-zero exit: the section and the committed files disagree about what the
# files record.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import glob, json, sys

doc = "docs/development/BENCHMARKS.md"
text = open(doc, encoding="utf-8").read()
section = text[text.index("## Local baselines"):]
section = section[:section.index("\n## ", 1)]
says_lacking = "the committed files carry neither" in section
paths = sorted(glob.glob("benchmarks/results/*_baseline.json"))
if not paths:
    print("no committed baseline to read"); sys.exit(2)
bad = []
for path in paths:
    data = json.load(open(path, encoding="utf-8"))
    has = "parameters" in data and (data["language"] != "cpp" or "compiler" in data["system"])
    if says_lacking and ("parameters" in data or "compiler" in data["system"]):
        bad.append(f"{path} records what the section says the committed files lack")
    if not says_lacking and not has:
        bad.append(f"{path} lacks its parameters or its compiler, and the section no longer says so")
if bad:
    print(f"{doc}'s Local baselines section and the committed files disagree:")
    for line in bad:
        print(f"  {line}")
    sys.exit(1)
state = "lacks" if says_lacking else "records"
print(f"PASS: every one of the {len(paths)} committed baselines {state} its parameters, as the section says")
PY

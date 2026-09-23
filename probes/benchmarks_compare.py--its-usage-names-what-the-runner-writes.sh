#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/compare.py.
# Claim: the script's own usage text names every binding the runner measures
# and shows paths of the shape the runner writes, <binding>_<mode>.json under
# benchmarks/results/. It named three bindings and a results/python.json that
# nothing has ever written.
# Non-zero exit: a binding is missing from the usage text, or an example path
# in it is not of the shape the runner writes.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import ast, re, sys
doc = ast.get_docstring(ast.parse(open("benchmarks/compare.py", encoding="utf-8").read())) or ""
bad = []
for name in ("Python", "C++", "Go", "Rust"):
    if name not in doc:
        bad.append(f"the usage does not name {name}")
paths = re.findall(r"\S+\.json", doc)
if not paths:
    bad.append("the usage shows no example path")
for p in paths:
    if not re.fullmatch(r"benchmarks/results/(\*|[a-z]+)_(throughput|latency|scaling)(_baseline|\*)?\.json", p):
        bad.append(f"not a path the runner writes: {p}")
if bad:
    print("\n".join(bad)); sys.exit(1)
print("PASS: the usage names the four bindings and paths of the runner's shape")
PY

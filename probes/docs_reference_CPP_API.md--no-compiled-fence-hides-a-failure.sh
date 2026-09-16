#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the documents the C++ doc-example harness compiles and runs.
# Claim: no fence answers a failed call by exiting zero. The harness judges a
# fence by its exit code, so an error path that returns zero reports green
# however the call went, and the example then demonstrates nothing past the
# line that failed. Also refuses an empty catch and a discarded result beside
# a client call. Non-zero exit: a fence carries one of those shapes, or the
# harness's document list cannot be read.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import re
import sys
from pathlib import Path

harness = Path("cpp/tests/doc_example_tests.cpp").read_text(encoding="utf-8")
listing = re.search(r"k_doc_files\s*=\s*\{(.*?)\};", harness, re.S)
if listing is None:
    print("the harness's document list could not be read")
    raise SystemExit(2)
docs = re.findall(r'"([^"]+)"', listing.group(1))
if not docs:
    print("the harness lists no document")
    raise SystemExit(2)

fence = re.compile(r"^```cpp\n(.*?)^```", re.M | re.S)
shapes = {
    "an error path exiting zero": re.compile(r"\breturn 0;"),
    "an empty catch": re.compile(r"catch\s*\([^)]*\)\s*\{\s*\}"),
    "a discarded call result": re.compile(r"^\s*\(void\)\s*\w+;"),
}
found = []
for rel in docs:
    path = Path(rel)
    if not path.is_file():
        continue
    text = path.read_text(encoding="utf-8")
    for match in fence.finditer(text):
        first = text[: match.start()].count("\n") + 1
        body = match.group(1)
        calls = re.search(r"\b(client|backend)\.\w+\(|\bload_checks_from_\w+\(", body)
        if calls is None:
            continue
        for label, pattern in shapes.items():
            for line in pattern.finditer(body):
                at = first + body[: line.start()].count("\n") + 1
                found.append(f"{rel}:{at}: {label}")
for problem in found:
    print(problem)
sys.exit(1 if found else 0)
PY

#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the coverage tree compiles without the source-prefix map the shipped
# build carries, so llvm-cov names a header the library compiled and a test
# compiled by one path and counts it once; the first measurement of the tree
# with the map counted every header twice, once under each path. Read off
# the two trees' compile commands: the shipped tree maps, the coverage tree
# does not.
# Non-zero exit: a coverage-tree compile command carries the prefix map, or a
# shipped-tree library compile command does not. Exits 2 when either tree is
# not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/compile_commands.json ] || exit 2
[ -f cpp/build-coverage/compile_commands.json ] || exit 2

python/.venv/bin/python - <<'PY' || exit 1
import json
import sys
from pathlib import Path


def commands(tree: str) -> dict[str, str]:
    entries = json.loads(Path(f"cpp/{tree}/compile_commands.json").read_text(encoding="utf-8"))
    return {e["file"]: e["command"] for e in entries}


shipped = commands("build")
coverage = commands("build-coverage")
library = [f for f in shipped if "/cpp/src/" in f and "/cli/" not in f]
if not library:
    print("the shipped tree compiles no library source")
    sys.exit(1)
unmapped = [f for f in library if "-ffile-prefix-map=" not in shipped[f]]
if unmapped:
    print(f"the shipped tree does not map these library sources: {unmapped}")
    sys.exit(1)
# The fetched libraries carry maps of their own, and the export holds them
# out by path; the claim is over the tree's own sources.
own = {f: cmd for f, cmd in coverage.items() if "/_deps/" not in f}
if not own:
    print("the coverage tree compiles none of the tree's own sources")
    sys.exit(1)
mapped = [f for f, cmd in own.items() if "-ffile-prefix-map=" in cmd]
if mapped:
    print(f"the coverage tree maps these sources: {mapped}")
    sys.exit(1)
instrumented = [f for f, cmd in own.items() if "-fcoverage-mapping" not in cmd]
if instrumented:
    print(f"the coverage tree leaves these uninstrumented: {instrumented}")
    sys.exit(1)
print(f"{len(own)} of the tree's own compile commands unmapped and instrumented")
PY
exit 0

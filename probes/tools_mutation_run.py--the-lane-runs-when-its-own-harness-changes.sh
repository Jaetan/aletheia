#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_run.py.
# Claim: a change to any module of the mutation harness puts every binding in
# the lane's scope. The scope rule runs all bindings when a global path
# changed, and names the harness among those paths; the harness is every
# module of the tools package the runner and the scope question load, read
# from what they import rather than from their names, and every tracked
# tools/mutation_*.py besides. A harness module the list does not cover is a
# change the lane never exercises on its own pull request: the legs decide
# they have nothing to sweep, and the change is first run on main.
# Non-zero exit: a harness module that no global path prefix covers, each
# named.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, ".")
from tools.mutation_run import _GLOBAL_MUTATION_PATHS  # noqa: PLC2701

LOADED = """import sys
import tools.mutation_run
import tools.mutation_scope
for name, module in sorted(sys.modules.items()):
    if (name == "tools" or name.startswith("tools.")) and getattr(module, "__file__", None):
        print(module.__file__)
"""
loaded = subprocess.run([sys.executable, "-c", LOADED], capture_output=True, text=True, check=True).stdout.split()
tracked = subprocess.run(
    ["git", "ls-files", "tools/mutation_*.py"], capture_output=True, text=True, check=True
).stdout.split()
harness = sorted({*tracked, *(Path(path).relative_to(Path.cwd()).as_posix() for path in loaded)})
uncovered = [path for path in harness if not path.startswith(_GLOBAL_MUTATION_PATHS)]
for path in uncovered:
    print(f"{path}: a harness module no global path covers")
print(f"{len(harness)} harness modules, {len(uncovered)} uncovered")
sys.exit(1 if uncovered else 0)
PY

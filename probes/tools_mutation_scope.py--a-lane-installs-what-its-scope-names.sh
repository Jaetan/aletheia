#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_scope.py against tools/mutation_run.py.
# Claim: the answer a CI lane reads before it installs a toolchain is the
# decision the sweep itself takes, over a real branch diff: a lane installs when
# the runner would run its binding and installs nothing when the runner would
# skip it, and it installs on every case the runner fails safe on (an empty
# diff, a shared path, a git error).  The decision is taken by asking the runner
# rather than by reading the diff a second time, which is checked here as well,
# because a second reader is a second decision and only one of them gates the
# installs.
# Run against throwaway repositories built here, so the answers are real git
# diffs rather than a stand-in, and none of them is this repository.
# Non-zero exit: a lane would install what its sweep does not need, skip what it
# does, or take its own reading of the diff.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

"$py" - <<'PY'
import ast
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, ".")
from tools.mutation_scope import lane_sweeps

BINDINGS = ("python", "go", "cpp", "rust")


def repo(changed: list[str]) -> Path:
    """Build a repository whose branch differs from main by exactly `changed`."""
    root = Path(tempfile.mkdtemp(prefix="mutation-scope-probe-"))
    git = ["git", "-C", str(root), "-c", "user.email=probe@example.invalid",
           "-c", "user.name=probe"]
    subprocess.run([*git[:3], "init", "-q", "-b", "main", str(root)], check=True,
                   stdout=subprocess.DEVNULL)
    (root / "seed.txt").write_text("seed\n", encoding="utf-8")
    subprocess.run([*git, "add", "-A"], check=True)
    subprocess.run([*git, "commit", "-q", "-m", "seed"], check=True)
    subprocess.run([*git, "checkout", "-q", "-b", "branch"], check=True)
    for name in changed:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("changed\n", encoding="utf-8")
    if changed:
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-q", "-m", "change"], check=True)
    return root


cases: list[tuple[str, list[str], dict[str, bool]]] = [
    ("a documentation-only branch", ["docs/DESIGN.md", "README.md"],
     {"python": False, "go": False, "cpp": False, "rust": False}),
    ("a Python-only branch", ["python/aletheia/checks.py"],
     {"python": True, "go": False, "cpp": False, "rust": False}),
    ("a C++ test-only branch", ["cpp/tests/client_tests.cpp"],
     {"python": False, "go": False, "cpp": True, "rust": False}),
    ("a Rust config-only branch", ["rust/.cargo/mutants.toml"],
     {"python": False, "go": False, "cpp": False, "rust": True}),
    ("a branch touching the shared kernel", ["src/Aletheia/Main.agda"],
     {"python": True, "go": True, "cpp": True, "rust": True}),
    ("a branch level with main", [],
     {"python": True, "go": True, "cpp": True, "rust": True}),
]

bad: list[str] = []
for label, changed, expected in cases:
    root = repo(changed)
    try:
        for binding in BINDINGS:
            got = lane_sweeps(binding, root)
            if got is not expected[binding]:
                bad.append(
                    f"{label}: the {binding} lane {'installs' if got else 'installs nothing'}, "
                    f"where the runner would {'run' if expected[binding] else 'skip'} it"
                )
    finally:
        shutil.rmtree(root, ignore_errors=True)

# A repository git cannot read is the fail-safe case, and a lane that read it as
# "nothing to do" would skip the toolchain of a sweep that then runs.
for binding in BINDINGS:
    if not lane_sweeps(binding, Path("/nonexistent-mutation-scope-probe")):
        bad.append(f"a diff that cannot be taken stops the {binding} lane installing")

# One reader: the module asks the runner for the scope, and runs nothing itself.
# Read as code rather than as text, so the prose saying what the module does not
# do is not mistaken for it doing it.
tree = ast.parse(Path("tools/mutation_scope.py").read_text(encoding="utf-8"))
imported = {
    alias.name.split(".")[0]
    for node in ast.walk(tree)
    if isinstance(node, ast.Import)
    for alias in node.names
} | {
    node.module.split(".")[0]
    for node in ast.walk(tree)
    if isinstance(node, ast.ImportFrom) and node.module
}
called = {
    node.func.id if isinstance(node.func, ast.Name) else node.func.attr
    for node in ast.walk(tree)
    if isinstance(node, ast.Call) and isinstance(node.func, (ast.Name, ast.Attribute))
}
if "subprocess" in imported:
    bad.append("tools/mutation_scope.py imports subprocess, so it can take a diff of its own")
for spawner in ("run_capture", "run_streaming", "check_output", "Popen", "system"):
    if spawner in called:
        bad.append(f"tools/mutation_scope.py calls {spawner}, so it can take a diff of its own")
if "bindings_in_scope" not in called:
    bad.append("tools/mutation_scope.py does not ask the runner for the scope")

if bad:
    print("a mutation lane does not install what its scope names:")
    for line in bad:
        print(f"  {line}")
    raise SystemExit(1)
print(f"PASS: {len(cases) + 1} diffs, {len(BINDINGS)} lanes each, every answer the runner's")
PY

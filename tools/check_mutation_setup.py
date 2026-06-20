# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Static mutation-setup coverage gate.

Two always-on invariants, checked without running the mutation tools (which
take 30 min - 2 hours wall):

1. **Hot-path sources exist.** Parses ``docs/MUTATION_BENCH.yaml`` and verifies,
   for every binding, that the declared hot-path source files exist on disk —
   catches silent removal or rename of a hot-path file.

2. **Tools-importing tests are excluded from the Python mutmut lane.** Every
   ``python/tests/test_*.py`` that imports the repo-root ``tools`` package must
   appear as ``--ignore=tests/<name>`` in ``[tool.mutmut].pytest_add_cli_args``.
   Such a test ModuleNotFound-aborts pytest collection inside mutmut's relocated
   ``mutants/`` work-tree (which has no ``tools``), which kills the baseline
   stats phase -> *zero* mutants run -> the (advisory) lane silently goes red.
   This gate is in the REQUIRED sweep, so it surfaces the drift at PR time.
   (Reproduced 2026-06-20: ``tests/test_check_changelog.py`` landed in #51
   importing ``tools`` without an ignore, crashing the lane unnoticed for days.)

The dynamic counterpart is ``tools/mutation_run.py``, which actually drives
each binding's mutation tool against this list and writes per-binding
survivor counts.

Usage:
  python3 tools/check_mutation_setup.py

Exits 0 if both invariants hold, 1 otherwise (with a precise diagnostic naming
the offending entries).

Forward-revert verified 2026-05-09 (invariant 1): rename one hot-path entry in
the YAML to a non-existent path -> this gate fires; restore the path -> exit 0.
Forward-revert verified 2026-06-20 (invariant 2): drop the
``test_check_changelog.py`` ignore -> this gate fires; restore it -> exit 0.
"""

from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"
PYPROJECT_PATH = REPO_ROOT / "python" / "pyproject.toml"
PY_TESTS_DIR = REPO_ROOT / "python" / "tests"

# A DIRECT top-level ``import tools`` / ``from tools ...`` (matches a transitive
# or lazy in-function import is NOT caught — that also does not abort collection).
_TOOLS_IMPORT_RE = re.compile(r"^[ \t]*(?:from|import)[ \t]+tools(?:\.|[ \t]|$)", re.MULTILINE)
# An ``--ignore=tests/<name>.py`` entry in the mutmut pytest args.
_IGNORE_ARG_RE = re.compile(r"^--ignore=(tests/[\w./-]+\.py)$")


def _load_bindings() -> dict[str, object]:
    """Load and validate ``SPEC_PATH``, returning its ``bindings`` mapping.

    Exits 2 with a precise stderr diagnostic if the spec is missing,
    malformed, or its ``bindings`` entry is not a mapping.
    """
    if not SPEC_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: spec missing at {SPEC_PATH}\n")
        sys.exit(2)
    spec: object = yaml.safe_load(SPEC_PATH.read_text())
    if not isinstance(spec, dict) or "bindings" not in spec:
        _ = sys.stderr.write(f"ERROR: malformed spec at {SPEC_PATH}\n")
        sys.exit(2)
    bindings = cast("dict[str, object]", spec)["bindings"]
    if not isinstance(bindings, dict):
        _ = sys.stderr.write("ERROR: spec.bindings must be a mapping\n")
        sys.exit(2)
    return cast("dict[str, object]", bindings)


def _collect_failures(bindings: dict[str, object]) -> list[str]:
    """Return one diagnostic per spec defect across every binding entry."""
    failures: list[str] = []
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            failures.append(
                f"[{binding_name}] binding spec must be a mapping",
            )
            continue
        spec = cast("dict[str, object]", binding_spec)
        tool = spec.get("tool")
        if not isinstance(tool, str) or not tool:
            failures.append(
                f"[{binding_name}] missing 'tool' field in spec",
            )
        hot_path = spec.get("hot_path", [])
        if not isinstance(hot_path, list) or not hot_path:
            failures.append(
                f"[{binding_name}] missing or empty 'hot_path' field",
            )
            continue
        for rel in cast("list[object]", hot_path):
            if not isinstance(rel, str):
                continue
            full = REPO_ROOT / rel
            if not full.is_file():
                failures.append(
                    f"[{binding_name}] hot-path source does not exist: {rel}",
                )
    return failures


def _mutmut_ignored_tests() -> set[str]:
    """Return the ``tests/<name>.py`` files excluded via ``--ignore`` in [tool.mutmut].

    Exits 2 if pyproject.toml is missing or its ``[tool.mutmut]`` section absent —
    those would silently make the invariant-2 check vacuous.
    """
    if not PYPROJECT_PATH.is_file():
        _ = sys.stderr.write(f"ERROR: pyproject.toml missing at {PYPROJECT_PATH}\n")
        sys.exit(2)
    data = tomllib.loads(PYPROJECT_PATH.read_text())
    mutmut = data.get("tool", {}).get("mutmut")
    if not isinstance(mutmut, dict):
        _ = sys.stderr.write(f"ERROR: no [tool.mutmut] section in {PYPROJECT_PATH}\n")
        sys.exit(2)
    args = cast("dict[str, object]", mutmut).get("pytest_add_cli_args", [])
    ignored: set[str] = set()
    if isinstance(args, list):
        for arg in cast("list[object]", args):
            if isinstance(arg, str):
                match = _IGNORE_ARG_RE.match(arg)
                if match:
                    ignored.add(match.group(1))
    return ignored


def _tools_importing_tests_unignored() -> list[str]:
    """One diagnostic per ``tools``-importing test missing from the mutmut ignore list."""
    if not PY_TESTS_DIR.is_dir():
        return []
    ignored = _mutmut_ignored_tests()
    failures: list[str] = []
    for path in sorted(PY_TESTS_DIR.glob("test_*.py")):
        if _TOOLS_IMPORT_RE.search(path.read_text(encoding="utf-8")):
            rel = f"tests/{path.name}"
            if rel not in ignored:
                failures.append(
                    f"[python/mutmut] {rel} imports the repo-root `tools` package but is "
                    + f"not excluded — add `--ignore={rel}` to [tool.mutmut].pytest_add_cli_args "
                    + "(else it aborts mutmut's baseline collection in mutants/ -> zero mutants)",
                )
    return failures


def _total_hot_paths(bindings: dict[str, object]) -> int:
    """Return the total number of declared hot-path sources across bindings."""
    total = 0
    for binding_spec in bindings.values():
        if not isinstance(binding_spec, dict):
            continue
        hot_path = cast("dict[str, object]", binding_spec).get("hot_path", [])
        if isinstance(hot_path, list):
            total += len(cast("list[object]", hot_path))
    return total


def main() -> int:
    """Check both invariants: hot-path sources exist + tools-tests are mutmut-ignored."""
    bindings = _load_bindings()
    failures = _collect_failures(bindings)
    failures += _tools_importing_tests_unignored()

    if failures:
        _ = sys.stderr.write("Mutation-setup coverage gate FAILED:\n")
        for failure in failures:
            _ = sys.stderr.write(f"  - {failure}\n")
        _ = sys.stderr.write(
            f"\n{len(failures)} issue(s) above.  For a missing hot-path source: "
            + f"restore it or update {SPEC_PATH.relative_to(REPO_ROOT)} to reflect "
            + "the rename (AGENTS.md cat 14(g) has the canonical lists).  For a "
            + "tools-importing test: add its `--ignore=` to [tool.mutmut].\n",
        )
        return 1

    total = _total_hot_paths(bindings)
    emit(
        "Mutation-setup coverage gate OK: "
        + f"{len(bindings)} bindings, {total} hot-path sources all present; "
        + "all tools-importing tests are mutmut-ignored.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

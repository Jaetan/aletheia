#!/usr/bin/env python3
"""Static mutation-setup coverage gate (R18 cluster 7).

Parses ``docs/MUTATION_BENCH.yaml`` and verifies, for every binding, that the
declared hot-path source files exist on disk.  Lightweight static gate —
catches silent removal or rename of a hot-path file without running the
mutation tools (which take 30 min - 2 hours wall).

The dynamic counterpart is ``tools/mutation_run.py``, which actually drives
each binding's mutation tool against this list and writes per-binding
survivor counts.

Usage:
  python3 tools/check_mutation_setup.py

Exits 0 if every declared hot-path source exists, 1 otherwise (with a precise
diagnostic naming the missing entries).

Forward-revert verified 2026-05-09: rename one hot-path entry in the YAML to
a non-existent path -> this gate fires with a precise diagnostic; restore the
path -> exit 0.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"


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
    """Verify every binding's declared hot-path source file exists on disk."""
    bindings = _load_bindings()
    failures = _collect_failures(bindings)

    if failures:
        _ = sys.stderr.write("Mutation-setup coverage gate FAILED:\n")
        for failure in failures:
            _ = sys.stderr.write(f"  - {failure}\n")
        _ = sys.stderr.write(
            f"\n{len(failures)} issue(s) above.  Either restore the "
            + "missing hot-path source, or update "
            + f"{SPEC_PATH.relative_to(REPO_ROOT)} "
            + "to reflect the rename.  See AGENTS.md cat 14(g) for the canonical "
            + "hot-path lists per binding.\n",
        )
        return 1

    total = _total_hot_paths(bindings)
    emit(
        "Mutation-setup coverage gate OK: "
        + f"{len(bindings)} bindings, {total} hot-path sources all present.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

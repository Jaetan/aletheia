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

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "MUTATION_BENCH.yaml"


def main() -> int:
    if not SPEC_PATH.is_file():
        print(f"ERROR: spec missing at {SPEC_PATH}", file=sys.stderr)
        return 2
    spec = yaml.safe_load(SPEC_PATH.read_text())
    if not isinstance(spec, dict) or "bindings" not in spec:
        print(f"ERROR: malformed spec at {SPEC_PATH}", file=sys.stderr)
        return 2
    bindings = spec["bindings"]
    if not isinstance(bindings, dict):
        print("ERROR: spec.bindings must be a mapping", file=sys.stderr)
        return 2

    failures: list[str] = []
    for binding_name, binding_spec in bindings.items():
        tool = binding_spec.get("tool")
        if not tool:
            failures.append(
                f"[{binding_name}] missing 'tool' field in spec",
            )
        hot_path = binding_spec.get("hot_path", [])
        if not hot_path:
            failures.append(
                f"[{binding_name}] missing or empty 'hot_path' field",
            )
            continue
        for rel in hot_path:
            full = REPO_ROOT / rel
            if not full.is_file():
                failures.append(
                    f"[{binding_name}] hot-path source does not exist: {rel}",
                )

    if failures:
        print("Mutation-setup coverage gate FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        print(
            f"\n{len(failures)} issue(s) above.  Either restore the "
            f"missing hot-path source, or update {SPEC_PATH.relative_to(REPO_ROOT)} "
            f"to reflect the rename.  See AGENTS.md cat 14(g) for the canonical "
            f"hot-path lists per binding.",
            file=sys.stderr,
        )
        return 1

    total = sum(len(b.get("hot_path", [])) for b in bindings.values())
    print(
        f"Mutation-setup coverage gate OK: "
        f"{len(bindings)} bindings, {total} hot-path sources all present.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

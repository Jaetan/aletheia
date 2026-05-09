#!/usr/bin/env python3
"""Static stability-bench coverage gate (R18 cluster 6).

Parses ``docs/STABILITY_BENCH.yaml`` and verifies, for every
``(binding, sub_check)`` pair, that the binding's harness source file
contains the declared ``source_marker`` substring.  Lightweight grep-based
gate — catches silent removal or rename of a sub-check assertion without
running the harness.

The dynamic counterpart is ``tools/stability_run.py``, which actually
executes the harnesses against ≥1M frames and writes per-binding verdicts.

Usage:
  python3 tools/check_stability_bench.py

Exits 0 if every declared marker is present, 1 otherwise (with a precise
diagnostic naming the missing entries).

Forward-revert verified 2026-05-08: commenting out one sub-check call
(e.g., the ``num_fds()`` line in ``python/benchmarks/stability.py``) fires
this gate with a precise diagnostic; restoring brings it back to clean.
"""

from __future__ import annotations

import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "STABILITY_BENCH.yaml"


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
        print(f"ERROR: spec.bindings must be a mapping", file=sys.stderr)
        return 2

    failures: list[str] = []
    for binding_name, binding_spec in bindings.items():
        harness_rel = binding_spec.get("harness")
        sub_checks = binding_spec.get("sub_checks", [])
        if not harness_rel:
            failures.append(
                f"[{binding_name}] missing 'harness' field in spec",
            )
            continue
        harness_path = REPO_ROOT / harness_rel
        if not harness_path.is_file():
            failures.append(
                f"[{binding_name}] harness file does not exist: {harness_rel}",
            )
            continue
        source = harness_path.read_text()
        for sc in sub_checks:
            name = sc.get("name", "<unnamed>")
            marker = sc.get("source_marker")
            if not marker:
                failures.append(
                    f"[{binding_name}/{name}] missing 'source_marker' field in spec",
                )
                continue
            if marker not in source:
                failures.append(
                    f"[{binding_name}/{name}] marker {marker!r} not found in {harness_rel}",
                )

    if failures:
        print("Stability-bench coverage gate FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        print(
            f"\n{len(failures)} marker(s) missing.  Either add the sub-check to "
            f"the harness source, or update {SPEC_PATH.relative_to(REPO_ROOT)} to "
            f"reflect the intended coverage.",
            file=sys.stderr,
        )
        return 1

    total = sum(len(b.get("sub_checks", [])) for b in bindings.values())
    print(
        f"Stability-bench coverage gate OK: "
        f"{len(bindings)} bindings, {total} sub-checks all present.",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Static stability-bench coverage gate.

Parses ``docs/STABILITY_BENCH.yaml`` and verifies, for every
``(binding, sub_check)`` pair, that the binding's harness source file
contains the declared ``source_marker`` substring.  Lightweight grep-based
gate -- catches silent removal or rename of a sub-check assertion without
running the harness.

The dynamic counterpart is ``tools/stability_run.py``, which actually
executes the harnesses against >=1M frames and writes per-binding verdicts.

Usage:
  python3 -m tools.check_stability_bench

Exits 0 if every declared marker is present, 1 otherwise (with a precise
diagnostic naming the missing entries).

Forward-revert verified 2026-05-08: commenting out one sub-check call
(e.g., the ``num_fds()`` line in ``python/benchmarks/stability.py``) fires
this gate with a precise diagnostic; restoring brings it back to clean.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "STABILITY_BENCH.yaml"

EXIT_OK = 0
EXIT_MISSING = 1
EXIT_USAGE = 2


def _load_bindings(spec_path: Path) -> dict[str, object]:
    """Load and validate the ``bindings`` mapping from the spec file.

    Exits with ``EXIT_USAGE`` (2) if the spec is missing or malformed.
    """
    if not spec_path.is_file():
        _ = sys.stderr.write(f"ERROR: spec missing at {spec_path}\n")
        sys.exit(EXIT_USAGE)
    spec: object = yaml.safe_load(spec_path.read_text())
    if not isinstance(spec, dict) or "bindings" not in spec:
        _ = sys.stderr.write(f"ERROR: malformed spec at {spec_path}\n")
        sys.exit(EXIT_USAGE)
    bindings = cast("dict[str, object]", spec).get("bindings")
    if not isinstance(bindings, dict):
        _ = sys.stderr.write("ERROR: spec.bindings must be a mapping\n")
        sys.exit(EXIT_USAGE)
    return cast("dict[str, object]", bindings)


def _sub_checks(binding_spec: dict[str, object]) -> list[object]:
    """Return the ``sub_checks`` list for one binding, defaulting to empty."""
    raw = binding_spec.get("sub_checks", [])
    return cast("list[object]", raw) if isinstance(raw, list) else []


def _check_binding(binding_name: str, binding_spec: dict[str, object]) -> list[str]:
    """Return the coverage failures for a single binding (empty if all present)."""
    failures: list[str] = []
    harness_rel = binding_spec.get("harness")
    if not isinstance(harness_rel, str) or not harness_rel:
        failures.append(f"[{binding_name}] missing 'harness' field in spec")
        return failures
    harness_path = REPO_ROOT / harness_rel
    if not harness_path.is_file():
        failures.append(
            f"[{binding_name}] harness file does not exist: {harness_rel}",
        )
        return failures
    source = harness_path.read_text()
    for entry in _sub_checks(binding_spec):
        if not isinstance(entry, dict):
            continue
        sc = cast("dict[str, object]", entry)
        name = sc.get("name", "<unnamed>")
        marker = sc.get("source_marker")
        if not isinstance(marker, str) or not marker:
            failures.append(
                f"[{binding_name}/{name}] missing 'source_marker' field in spec",
            )
            continue
        if marker not in source:
            failures.append(
                f"[{binding_name}/{name}] marker {marker!r} not found in {harness_rel}",
            )
    return failures


def _report_failures(failures: list[str]) -> None:
    """Write the failure diagnostic block to stderr."""
    _ = sys.stderr.write("Stability-bench coverage gate FAILED:\n")
    for failure in failures:
        _ = sys.stderr.write(f"  - {failure}\n")
    _ = sys.stderr.write(
        f"\n{len(failures)} marker(s) missing.  Either add the sub-check to "
        + "the harness source, or update "
        + f"{SPEC_PATH.relative_to(REPO_ROOT)} to "
        + "reflect the intended coverage.\n",
    )


def main() -> int:
    """Verify every STABILITY_BENCH.yaml source_marker is present in its harness."""
    bindings = _load_bindings(SPEC_PATH)
    failures: list[str] = []
    total = 0
    for binding_name, binding_spec in bindings.items():
        if not isinstance(binding_spec, dict):
            failures.append(f"[{binding_name}] binding spec must be a mapping")
            continue
        spec = cast("dict[str, object]", binding_spec)
        total += len(_sub_checks(spec))
        failures.extend(_check_binding(binding_name, spec))

    if failures:
        _report_failures(failures)
        return EXIT_MISSING

    emit(
        "Stability-bench coverage gate OK: "
        + f"{len(bindings)} bindings, {total} sub-checks all present.",
    )
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())

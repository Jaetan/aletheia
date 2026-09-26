# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Static coverage-record gate, run in the always-on sweep.

The coverage lane (``tools/coverage_run.py``) measures each binding's suite
and holds the figures to the floors ``docs/COVERAGE_BENCH.yaml`` records.
The lane is opt-in and runs its four suites, so what it reads is checked
here, without running any of them:

1. **The floors are percentages**, each a number over zero and at most a
   hundred, and every binding the runner knows has an entry.

2. **Every path a scope names exists** in the tree, so a binding whose
   sources moved is a failure here and not a figure over nothing.

3. **A recorded figure is over its floor.** A record under the floor is a
   contradiction: the lane would have refused the run that produced it, so
   the figure was typed rather than measured.  A null record, before the
   first run, is not held.

4. **The second figure is named**, as one of the units the runner produces,
   so a reader never takes a block or a region for a branch.

5. **The pinned Rust tool is the one the workflow installs.**  The runner
   refuses any other version, so a pin the workflow does not honour is a
   lane that fails on every run.

Usage:
  python -m tools.check_coverage_setup

Exits 0 when the record holds, 1 with one line per defect otherwise, 2 when
the record cannot be read.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import cast

import yaml

from tools._common import emit
from tools.coverage_run import RUNNERS

REPO_ROOT = Path(__file__).resolve().parent.parent
SPEC_PATH = REPO_ROOT / "docs" / "COVERAGE_BENCH.yaml"
WORKFLOW_PATH = REPO_ROOT / ".github" / "workflows" / "pr-build-lanes.yml"

# The units the runner's figures carry, by binding: the first is lines
# everywhere, the second is what each tool counts.
SECOND_UNITS = frozenset({"branches", "blocks", "regions"})

# How the workflow pins cargo-llvm-cov.
_CARGO_INSTALL_RE = re.compile(r"cargo install cargo-llvm-cov --version (\S+)")

type Spec = dict[str, object]


def load_spec(path: Path = SPEC_PATH) -> Spec:
    """Load the record, exiting 2 where it is missing or not a mapping."""
    if not path.is_file():
        _ = sys.stderr.write(f"ERROR: record missing at {path}\n")
        sys.exit(2)
    spec: object = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(spec, dict) or "bindings" not in spec or "floors" not in spec:
        _ = sys.stderr.write(f"ERROR: malformed record at {path}\n")
        sys.exit(2)
    return cast("Spec", spec)


_WHOLE = 100


def _is_pct(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and 0 < value <= _WHOLE


def floors_are_percentages(spec: Spec) -> list[str]:
    """Hold both floors to being a percentage over zero."""
    floors = cast("dict[str, object]", spec.get("floors", {}))
    return [
        f"[floors/{name}] must be a percentage over 0 and at most 100, not {floors.get(name)!r}"
        for name in ("lines_pct", "branches_pct")
        if not _is_pct(floors.get(name))
    ]


def every_runner_has_an_entry(spec: Spec) -> list[str]:
    """Hold the record to one entry per binding the runner measures, and no other."""
    bindings = cast("dict[str, object]", spec["bindings"])
    known = {name for name, _ in RUNNERS}
    return [f"[bindings] no entry for {name}" for name in sorted(known - set(bindings))] + [
        f"[bindings/{name}] the runner has no such binding"
        for name in sorted(set(bindings) - known)
    ]


def scope_paths_exist(spec: Spec, repo_root: Path = REPO_ROOT) -> list[str]:
    """Hold every path a scope names to existing in the tree."""
    failures: list[str] = []
    for name, entry in cast("dict[str, dict[str, object]]", spec["bindings"]).items():
        scope = entry.get("scope")
        if not isinstance(scope, list) or not scope:
            failures.append(f"[{name}/scope] must be a non-empty list of paths")
            continue
        failures += [
            f"[{name}/scope] {path} is not in the tree"
            for path in cast("list[object]", scope)
            if not isinstance(path, str) or not (repo_root / path).exists()
        ]
    return failures


def second_figure_is_named(spec: Spec) -> list[str]:
    """Hold every binding's second figure to a unit the runner produces."""
    failures: list[str] = []
    for name, entry in cast("dict[str, dict[str, object]]", spec["bindings"]).items():
        second = entry.get("second")
        unit = cast("dict[str, object]", second).get("unit") if isinstance(second, dict) else None
        if unit not in SECOND_UNITS:
            failures.append(
                f"[{name}/second/unit] must be one of {sorted(SECOND_UNITS)}, not {unit!r}"
            )
    return failures


def recorded_figures_are_over_the_floors(spec: Spec) -> list[str]:
    """Hold every recorded figure to its floor; a null record is not yet held."""
    floors = cast("dict[str, float]", spec.get("floors", {}))
    failures: list[str] = []
    for name, entry in cast("dict[str, dict[str, object]]", spec["bindings"]).items():
        baseline = entry.get("baseline")
        if not isinstance(baseline, dict):
            failures.append(f"[{name}/baseline] must be a mapping")
            continue
        base = cast("dict[str, object]", baseline)
        for key, floor_key in (("lines_pct", "lines_pct"), ("second_pct", "branches_pct")):
            recorded = base.get(key)
            if recorded is None:
                continue
            if not isinstance(recorded, (int, float)):
                failures.append(f"[{name}/baseline/{key}] must be a number or null")
            elif recorded < floors.get(floor_key, 0):
                failures.append(
                    f"[{name}/baseline/{key}] {recorded} is under the floor "
                    + f"{floors[floor_key]}: the lane refuses that run, "
                    + "so the figure was not measured"
                )
    return failures


def rust_pin_is_what_the_workflow_installs(spec: Spec, workflow: Path = WORKFLOW_PATH) -> list[str]:
    """Hold the record's cargo-llvm-cov pin to the version the workflow installs."""
    rust = cast("dict[str, dict[str, object]]", spec["bindings"]).get("rust", {})
    pinned = rust.get("version")
    if not isinstance(pinned, str):
        return ["[rust/version] must pin cargo-llvm-cov exactly"]
    if not workflow.is_file():
        return [f"[rust/version] {workflow.name} is missing, so nothing installs the pin"]
    installed = _CARGO_INSTALL_RE.findall(workflow.read_text(encoding="utf-8"))
    if pinned not in installed:
        return [
            f"[rust/version] the record pins cargo-llvm-cov {pinned}, the workflow installs "
            + f"{installed or 'no version'}"
        ]
    return []


def collect_failures(spec: Spec) -> list[str]:
    """Return one line per defect of the record."""
    return (
        floors_are_percentages(spec)
        + every_runner_has_an_entry(spec)
        + scope_paths_exist(spec)
        + second_figure_is_named(spec)
        + recorded_figures_are_over_the_floors(spec)
        + rust_pin_is_what_the_workflow_installs(spec)
    )


def main() -> int:
    """Check the coverage record's shape without running a suite."""
    failures = collect_failures(load_spec())
    if failures:
        emit("check-coverage-setup: FAIL")
        for line in failures:
            emit(f"  {line}")
        return 1
    emit("check-coverage-setup: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

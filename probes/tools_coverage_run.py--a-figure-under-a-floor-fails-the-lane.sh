#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/coverage_run.py and docs/COVERAGE_BENCH.yaml.
# Claim: the floors gate. A report one hundredth of a point under either
# floor is judged a regression, one on the floor passes, a report of nothing
# is refused, and the recorded figures are held over the floors by the static
# gate, which goes red on a scratch copy of the record with one figure typed
# under its floor. The record itself is never written.
# Non-zero exit: a figure under a floor passes, a figure on it fails, a total
# of nothing passes, or the static gate accepts a recorded figure under its
# floor.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT

python/.venv/bin/python - "$scratch" <<'PY' || exit 1
import sys
from pathlib import Path

import yaml

from tools import check_coverage_setup as setup
from tools.coverage_run import CoverageReport, Figure, gate, load_spec

spec = load_spec()
floors = spec["floors"]
lines_floor, second_floor = floors["lines_pct"], floors["branches_pct"]
unit = spec["bindings"]["go"]["second"]["unit"]


def report(lines: tuple[int, int], second: tuple[int, int]) -> CoverageReport:
    return CoverageReport("go", "t", Figure("statements", *lines), Figure(unit, *second))


def status(lines: tuple[int, int], second: tuple[int, int]) -> str:
    return gate(report(lines, second), spec)["status"]


# One hundredth of a point either side of each floor, over 10000 units.
under_lines = (int(lines_floor * 100) - 1, 10000)
on_lines = (int(lines_floor * 100), 10000)
under_second = (int(second_floor * 100) - 1, 10000)
on_second = (int(second_floor * 100), 10000)
checks = {
    "lines under the floor": (status(under_lines, on_second), "regression"),
    "the second figure under the floor": (status(on_lines, under_second), "regression"),
    "both on the floor": (status(on_lines, on_second), "ok"),
    "a total of nothing": (status((0, 0), on_second), "regression"),
    "a tool that did not run": (gate(CoverageReport("go", "t", error="x"), spec)["status"], "error"),
}
failed = False
for what, (got, want) in checks.items():
    if got != want:
        print(f"{what}: judged {got}, want {want}")
        failed = True

# The static gate on a scratch copy of the record with one figure under its floor.
scratch = Path(sys.argv[1])
copy = scratch / "COVERAGE_BENCH.yaml"
broken = load_spec()
broken["bindings"]["cpp"]["baseline"]["lines_pct"] = lines_floor - 0.01
copy.write_text(yaml.safe_dump(broken), encoding="utf-8")
failures = setup.recorded_figures_are_over_the_floors(setup.load_spec(copy))
if not any("[cpp/baseline/lines_pct]" in f for f in failures):
    print(f"the static gate accepted a recorded figure under the floor: {failures}")
    failed = True
if setup.recorded_figures_are_over_the_floors(spec):
    print("the static gate refuses the record as committed")
    failed = True
sys.exit(1 if failed else 0)
PY
exit 0

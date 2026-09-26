# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_coverage_setup``: each arm goes red on the defect it names.

The gate reads the coverage record without running a suite.  Every check
is given the record as it stands and a copy with one thing wrong, so a
check that cannot fail is caught here rather than trusted.
"""

from __future__ import annotations

import copy
from typing import TYPE_CHECKING, cast

import pytest

from tools import check_coverage_setup as gate

if TYPE_CHECKING:
    from pathlib import Path


def _record() -> gate.Spec:
    return gate.load_spec()


def _bindings(spec: gate.Spec) -> dict[str, dict[str, object]]:
    return cast("dict[str, dict[str, object]]", spec["bindings"])


def test_the_record_as_committed_holds() -> None:
    """The record as committed holds."""
    spec = _record()
    assert not gate.collect_failures(spec)


@pytest.mark.parametrize("bad", [0, 101, -1, "80", None, True])
def test_a_floor_that_is_not_a_percentage_is_refused(bad: object) -> None:
    """A floor that is not a percentage is refused."""
    spec = _record()
    broken = copy.deepcopy(spec)
    cast("dict[str, object]", broken["floors"])["lines_pct"] = bad
    assert any("[floors/lines_pct]" in f for f in gate.floors_are_percentages(broken))


def test_a_binding_the_runner_measures_needs_an_entry_and_no_other_may_have_one() -> None:
    """A binding the runner measures needs an entry and no other may have one."""
    spec = _record()
    broken = copy.deepcopy(spec)
    del _bindings(broken)["rust"]
    _bindings(broken)["haskell"] = {}
    failures = gate.every_runner_has_an_entry(broken)
    assert "[bindings] no entry for rust" in failures
    assert "[bindings/haskell] the runner has no such binding" in failures


def test_a_scope_path_that_left_the_tree_is_refused() -> None:
    """A scope path that left the tree is refused."""
    spec = _record()
    broken = copy.deepcopy(spec)
    _bindings(broken)["go"]["scope"] = ["go/aletheia", "go/gone"]
    assert gate.scope_paths_exist(broken) == ["[go/scope] go/gone is not in the tree"]
    _bindings(broken)["go"]["scope"] = []
    assert gate.scope_paths_exist(broken) == ["[go/scope] must be a non-empty list of paths"]


def test_a_second_figure_outside_the_runners_units_is_refused() -> None:
    """A second figure outside the runners units is refused."""
    spec = _record()
    broken = copy.deepcopy(spec)
    _bindings(broken)["rust"]["second"] = {"unit": "branches-ish"}
    assert any("[rust/second/unit]" in f for f in gate.second_figure_is_named(broken))
    del _bindings(broken)["rust"]["second"]
    assert any("[rust/second/unit]" in f for f in gate.second_figure_is_named(broken))


def test_a_recorded_figure_under_its_floor_is_refused_and_a_null_record_is_not() -> None:
    """A recorded figure under its floor is refused and a null record is not."""
    spec = _record()
    broken = copy.deepcopy(spec)
    baseline = cast("dict[str, object]", _bindings(broken)["cpp"]["baseline"])
    baseline["lines_pct"] = 79.9
    baseline["second_pct"] = None
    failures = gate.recorded_figures_are_over_the_floors(broken)
    assert len(failures) == 1
    assert failures[0].startswith("[cpp/baseline/lines_pct] 79.9 is under the floor 80")
    baseline["lines_pct"] = None
    assert not gate.recorded_figures_are_over_the_floors(broken)
    baseline["second_pct"] = 59
    assert len(gate.recorded_figures_are_over_the_floors(broken)) == 1
    baseline["second_pct"] = "60"
    assert gate.recorded_figures_are_over_the_floors(broken) == [
        "[cpp/baseline/second_pct] must be a number or null"
    ]


def test_a_rust_pin_the_workflow_does_not_install_is_refused(tmp_path: Path) -> None:
    """A rust pin the workflow does not install is refused."""
    spec = _record()
    broken = copy.deepcopy(spec)
    _bindings(broken)["rust"]["version"] = "0.0.1"
    (failure,) = gate.rust_pin_is_what_the_workflow_installs(broken)
    assert failure.startswith("[rust/version] the record pins cargo-llvm-cov 0.0.1")
    del _bindings(broken)["rust"]["version"]
    assert gate.rust_pin_is_what_the_workflow_installs(broken) == [
        "[rust/version] must pin cargo-llvm-cov exactly"
    ]
    assert gate.rust_pin_is_what_the_workflow_installs(spec, workflow=tmp_path / "none.yml") == [
        "[rust/version] none.yml is missing, so nothing installs the pin"
    ]


def test_main_reports_the_verdict(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """Main reports the verdict."""
    assert gate.main() == 0
    assert "check-coverage-setup: OK" in capsys.readouterr().out

    def broken(_spec: gate.Spec) -> list[str]:
        return ["[x] broken"]

    monkeypatch.setattr(gate, "collect_failures", broken)
    assert gate.main() == 1
    out = capsys.readouterr().out
    assert "check-coverage-setup: FAIL" in out
    assert "[x] broken" in out


def test_a_missing_or_malformed_record_exits_two(tmp_path: Path) -> None:
    """A missing or malformed record exits two."""
    with pytest.raises(SystemExit) as missing:
        _ = gate.load_spec(tmp_path / "none.yaml")
    assert missing.value.code == 2
    malformed = tmp_path / "bad.yaml"
    _ = malformed.write_text("bindings: {}\n")
    with pytest.raises(SystemExit) as bad:
        _ = gate.load_spec(malformed)
    assert bad.value.code == 2

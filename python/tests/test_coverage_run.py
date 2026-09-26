# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.coverage_run``: the readers, the gate and the scope.

The lane runs four suites under four tools, which no unit test does; what a
unit test holds is that each tool's report is read into the one shape, that
the gate refuses exactly a figure under its floor, a tool that did not run
and a total of nothing, and that the diff scope answers the way the mutation
lane's does with this lane's own tables.
"""

from __future__ import annotations

import json
import subprocess
from typing import TYPE_CHECKING, cast

import pytest

from tools import coverage_run, mutation_run
from tools.coverage_run import CoverageReport, Figure

if TYPE_CHECKING:
    from pathlib import Path


def _fake_diff(monkeypatch: pytest.MonkeyPatch, *, files: list[str], returncode: int = 0) -> None:
    stdout = "".join(f"{f}\n" for f in files)

    def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr="")

    monkeypatch.setattr(mutation_run, "run_capture", fake)


def _spec(
    *,
    lines_floor: float = 80,
    branches_floor: float = 60,
    unit: str = "branches",
    recorded: float | None = None,
) -> coverage_run.Spec:
    baseline: dict[str, object] = {"lines_pct": recorded, "second_pct": recorded}
    return {
        "floors": {"lines_pct": lines_floor, "branches_pct": branches_floor},
        "bindings": {"x": {"second": {"unit": unit}, "baseline": baseline}},
    }


def _report(
    lines: tuple[int, int], second: tuple[int, int], unit: str = "branches"
) -> CoverageReport:
    return CoverageReport(
        binding="x",
        tool="t",
        lines=Figure("lines", *lines),
        second=Figure(unit, *second),
    )


def _status(verdict: coverage_run.Verdict, figure: str) -> object:
    return cast("dict[str, object]", verdict[figure])["status"]


def _sha(_root: Path) -> str:
    return "abc1234"


# ── Figure ───────────────────────────────────────────────────────────────────


def test_a_figure_is_its_counts_and_a_figure_of_nothing_is_zero() -> None:
    """A figure is its counts and a figure of nothing is zero."""
    assert Figure("lines", 1, 4).pct == 25.0
    assert Figure("lines", 0, 0).pct == 0.0
    assert Figure("lines", 3, 4).to_dict() == {
        "unit": "lines",
        "covered": 3,
        "total": 4,
        "pct": 75.0,
    }


# ── The readers ──────────────────────────────────────────────────────────────


def test_the_python_report_is_read_whole_and_per_file() -> None:
    """The python report is read whole and per file."""
    report = {
        "totals": {
            "covered_lines": 90,
            "num_statements": 100,
            "covered_branches": 7,
            "num_branches": 10,
        },
        "files": {
            "aletheia/a.py": {
                "summary": {
                    "covered_lines": 1,
                    "num_statements": 2,
                    "covered_branches": 0,
                    "num_branches": 0,
                }
            }
        },
    }
    lines, branches, per_file = coverage_run.parse_python_report(report)
    assert (lines.unit, lines.covered, lines.total) == ("lines", 90, 100)
    assert (branches.unit, branches.covered, branches.total) == ("branches", 7, 10)
    assert per_file == {"python/aletheia/a.py": {"lines_pct": 50.0, "branches_pct": 0.0}}


_PROFILE = """mode: atomic
github.com/Jaetan/aletheia/go/v5/aletheia/a.go:10.2,12.3 2 1
github.com/Jaetan/aletheia/go/v5/aletheia/a.go:14.2,15.3 3 0
github.com/Jaetan/aletheia/go/v5/aletheia/a.go:14.2,15.3 3 5
github.com/Jaetan/aletheia/go/v5/aletheia/b.go:1.1,2.2 1 0
github.com/Jaetan/aletheia/go/v5/benchmarks/h.go:1.1,2.2 9 0
"""


def test_the_go_profile_keys_blocks_on_position_and_holds_the_harness_out() -> None:
    """A block two test binaries both report is one block, hit if either hit it."""
    blocks = coverage_run.parse_go_profile(_PROFILE)
    assert sorted((b.file, b.statements, b.hit) for b in blocks) == [
        ("go/aletheia/a.go", 2, True),
        ("go/aletheia/a.go", 3, True),
        ("go/aletheia/b.go", 1, False),
    ]
    statements, blocks_figure, per_file = coverage_run.go_figures(blocks)
    assert (statements.unit, statements.covered, statements.total) == ("statements", 5, 6)
    assert (blocks_figure.unit, blocks_figure.covered, blocks_figure.total) == ("blocks", 2, 3)
    assert per_file["go/aletheia/b.go"] == {"lines_pct": 0.0, "blocks_pct": 0.0}
    assert per_file["go/aletheia/a.go"] == {"lines_pct": 100.0, "blocks_pct": 100.0}


def test_a_go_block_hit_in_an_earlier_line_stays_hit() -> None:
    """A go block hit in an earlier line stays hit."""
    profile = "mode: atomic\nm/x.go:1.1,2.2 1 3\nm/x.go:1.1,2.2 1 0\n"
    blocks = coverage_run.parse_go_profile(profile, exclude_prefix="none/")
    assert len(blocks) == 1
    assert blocks[0].hit


def _llvm_export(second: str) -> dict[str, object]:
    return {
        "data": [
            {
                "totals": {
                    "lines": {"covered": 8, "count": 10},
                    second: {"covered": 3, "count": 6},
                },
                "files": [
                    {
                        "filename": str(coverage_run.REPO_ROOT / "cpp" / "src" / "a.cpp"),
                        "summary": {
                            "lines": {"percent": 80.0},
                            second: {"percent": 50.0},
                        },
                    }
                ],
            }
        ]
    }


@pytest.mark.parametrize("second", ["branches", "regions"])
def test_an_llvm_export_is_read_for_lines_and_the_named_second_unit(second: str) -> None:
    """An llvm export is read for lines and the named second unit."""
    lines, other, per_file = coverage_run.parse_llvm_export(_llvm_export(second), second=second)
    assert (lines.covered, lines.total) == (8, 10)
    assert (other.unit, other.covered, other.total) == (second, 3, 6)
    assert per_file == {"cpp/src/a.cpp": {"lines_pct": 80.0, f"{second}_pct": 50.0}}


def test_the_ctest_listing_is_where_the_objects_come_from(monkeypatch: pytest.MonkeyPatch) -> None:
    """The ctest listing is where the objects come from."""
    listing = {"tests": [{"command": ["/b/unit_tests", "--x"]}, {"command": ["/b/cli_tests"]}]}

    def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        assert "--show-only=json-v1" in cmd
        return subprocess.CompletedProcess(cmd, 0, stdout=json.dumps(listing), stderr="")

    monkeypatch.setattr(coverage_run, "run_capture", fake)
    assert coverage_run.ctest_objects(coverage_run.CPP_BUILD_DIR) == [
        "/b/cli_tests",
        "/b/unit_tests",
    ]


def test_a_ctest_listing_that_fails_is_an_error_not_an_empty_object_list(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A ctest listing that fails is an error not an empty object list."""

    def fake(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="no tree")

    monkeypatch.setattr(coverage_run, "run_capture", fake)
    with pytest.raises(RuntimeError, match="no tree"):
        _ = coverage_run.ctest_objects(coverage_run.CPP_BUILD_DIR)


def test_shared_objects_are_the_real_files_not_the_symlinks(tmp_path: Path) -> None:
    """Shared objects are the real files not the symlinks."""
    real = tmp_path / "libx.so.1"
    _ = real.write_bytes(b"")
    (tmp_path / "libx.so").symlink_to(real)
    _ = (tmp_path / "notes.txt").write_text("")
    assert coverage_run.shared_objects(tmp_path) == [str(real)]


@pytest.mark.parametrize(
    ("output", "version"),
    [("cargo-llvm-cov 0.8.7\n", "0.8.7"), ("cargo-llvm-cov 0.10.12", "0.10.12"), ("", None)],
)
def test_the_cargo_llvm_cov_version_is_read_from_its_banner(
    output: str, version: str | None
) -> None:
    """The cargo llvm cov version is read from its banner."""
    assert coverage_run.cargo_llvm_cov_version(output) == version


# ── The gate ─────────────────────────────────────────────────────────────────


def test_a_binding_over_both_floors_passes_and_reports_its_distance_from_the_record() -> None:
    """A binding over both floors passes and reports its distance from the record."""
    verdict = coverage_run.gate(_report((90, 100), (70, 100)), _spec(recorded=85.0))
    assert verdict["status"] == "ok"
    assert verdict["lines"] == {
        "unit": "lines",
        "observed_pct": 90.0,
        "floor_pct": 80.0,
        "status": "ok",
        "recorded_pct": 85.0,
        "delta_pct": 5.0,
    }
    assert _status(verdict, "second") == "ok"


@pytest.mark.parametrize(
    ("lines", "second", "red"),
    [((79, 100), (70, 100), "lines"), ((90, 100), (59, 100), "second")],
)
def test_a_figure_under_its_floor_fails_the_binding(
    lines: tuple[int, int], second: tuple[int, int], red: str
) -> None:
    """A figure under its floor fails the binding."""
    verdict = coverage_run.gate(_report(lines, second), _spec())
    assert verdict["status"] == "regression"
    assert _status(verdict, red) == "under_floor"


def test_a_figure_exactly_on_the_floor_passes() -> None:
    """A figure exactly on the floor passes."""
    verdict = coverage_run.gate(_report((80, 100), (60, 100)), _spec())
    assert verdict["status"] == "ok"


def test_a_total_of_nothing_is_a_measurement_of_nothing_and_fails() -> None:
    """A total of nothing is a measurement of nothing and fails."""
    verdict = coverage_run.gate(_report((0, 0), (60, 100)), _spec())
    assert verdict["status"] == "regression"
    assert _status(verdict, "lines") == "empty"


def test_a_tool_that_did_not_run_fails_with_its_reason() -> None:
    """A tool that did not run fails with its reason."""
    rep = CoverageReport(binding="x", tool="t", error="cargo-llvm-cov is not installed")
    assert coverage_run.gate(rep, _spec()) == {
        "status": "error",
        "error": "cargo-llvm-cov is not installed",
    }


def test_a_second_figure_the_record_does_not_name_fails() -> None:
    """The record says what the second unit is; a tool giving another is a defect."""
    verdict = coverage_run.gate(_report((90, 100), (70, 100), unit="regions"), _spec())
    assert verdict["status"] == "error"
    assert "regions" in str(verdict["error"])


def test_a_missing_figure_fails() -> None:
    """A missing figure fails."""
    rep = CoverageReport(binding="x", tool="t", lines=Figure("lines", 9, 10))
    verdict = coverage_run.gate(rep, _spec())
    assert verdict["status"] == "regression"
    assert verdict["second"] == {"status": "missing"}


def test_the_baseline_fragment_carries_the_run_as_the_record_reads_it() -> None:
    """The baseline fragment carries the run as the record reads it."""
    fragment = coverage_run.baseline_fragment(_report((9, 10), (3, 4)), "2026-09-26")
    assert "lines_pct: 90.00" in fragment
    assert "second_pct: 75.00" in fragment
    assert 'run_at: "2026-09-26"' in fragment
    assert coverage_run.baseline_fragment(CoverageReport("x", "t"), "2026-09-26") == ""


# ── The scope ────────────────────────────────────────────────────────────────


@pytest.mark.parametrize(
    ("files", "expected"),
    [
        (["rust/src/lib.rs"], {"rust"}),
        (["rust/excel/src/lib.rs"], {"rust"}),
        (["go/excel/excel_test.go"], {"go"}),
        (["cpp/tests/unit_tests_json.cpp"], {"cpp"}),
        (["python/tests/test_types.py"], {"python"}),
        (["docs/COVERAGE.md", "README.md"], set[str]()),
        (["src/Aletheia/Main.agda"], None),
        (["tools/coverage_run.py"], None),
        (["docs/COVERAGE_BENCH.yaml"], None),
        (["tools/mutation_run.py"], None),
        ([".github/workflows/pr-build-lanes.yml"], None),
        ([], None),
    ],
)
def test_the_scope_is_this_lanes_tables_over_the_mutation_lanes_reading(
    monkeypatch: pytest.MonkeyPatch, files: list[str], expected: set[str] | None
) -> None:
    """The scope is this lanes tables over the mutation lanes reading."""
    monkeypatch.delenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", raising=False)
    _fake_diff(monkeypatch, files=files)
    assert coverage_run.coverage_scope(coverage_run.REPO_ROOT) == expected


def test_the_mutation_lanes_own_escape_hatch_does_not_widen_this_lane(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The mutation lanes own escape hatch does not widen this lane."""
    monkeypatch.setenv("ALETHEIA_MUTATION_NO_DIFF_SCOPE", "1")
    monkeypatch.delenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", raising=False)
    _fake_diff(monkeypatch, files=["docs/x.md"])
    assert coverage_run.coverage_scope(coverage_run.REPO_ROOT) == set()
    monkeypatch.setenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", "1")
    assert coverage_run.coverage_scope(coverage_run.REPO_ROOT) is None


@pytest.mark.parametrize(
    "case",
    [
        (["go/aletheia/x.go"], "go", "1"),
        (["go/aletheia/x.go"], "rust", "0"),
        (["go/aletheia/x.go"], None, "1"),
        (["docs/x.md"], None, "0"),
        (["src/x.agda"], "rust", "1"),
    ],
)
def test_the_scope_answer_is_written_where_the_workflow_reads_it(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    case: tuple[list[str], str | None, str],
) -> None:
    """The answer lands in GITHUB_ENV where it names a file, on stdout where it does not."""
    files, binding, answer = case
    monkeypatch.delenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", raising=False)
    _fake_diff(monkeypatch, files=files)
    github_env = tmp_path / "env"
    monkeypatch.setenv("GITHUB_ENV", str(github_env))
    assert coverage_run.write_scope(binding, coverage_run.REPO_ROOT) == 0
    assert github_env.read_text() == f"LANE_MEASURES={answer}\n"
    monkeypatch.delenv("GITHUB_ENV")
    assert coverage_run.write_scope(binding, coverage_run.REPO_ROOT) == 0
    assert capsys.readouterr().out == f"LANE_MEASURES={answer}\n"


def test_the_scope_flag_measures_nothing(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """The scope flag measures nothing."""
    _fake_diff(monkeypatch, files=["docs/x.md"])
    monkeypatch.delenv("GITHUB_ENV", raising=False)
    monkeypatch.delenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", raising=False)
    assert coverage_run.main(["--scope", "--binding", "cpp"]) == 0
    assert capsys.readouterr().out == "LANE_MEASURES=0\n"


# ── main, end to end with the runners replaced ───────────────────────────────


def test_main_archives_each_report_and_fails_on_one_binding_under_a_floor(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Main archives each report and fails on one binding under a floor."""
    monkeypatch.setenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", "1")
    monkeypatch.setattr(coverage_run, "ARTIFACT_BASE", tmp_path)
    monkeypatch.setattr(coverage_run, "short_sha", _sha)

    def green(_art: Path, _spec: coverage_run.Spec) -> CoverageReport:
        return CoverageReport("go", "t", Figure("statements", 9, 10), Figure("blocks", 7, 10))

    def red(_art: Path, _spec: coverage_run.Spec) -> CoverageReport:
        return CoverageReport("rust", "t", Figure("lines", 5, 10), Figure("regions", 7, 10))

    monkeypatch.setattr(coverage_run, "RUNNERS", [("go", green), ("rust", red)])
    assert coverage_run.main([]) == 1
    summary = json.loads((tmp_path / "abc1234" / "summary.json").read_text())
    assert summary["passed"] is False
    assert summary["verdicts"]["go"]["status"] == "ok"
    assert summary["verdicts"]["rust"]["lines"]["status"] == "under_floor"
    assert (tmp_path / "abc1234" / "go.json").is_file()
    assert "lines_pct: 50.00" in (tmp_path / "abc1234" / "baseline-rust.yaml").read_text()
    # One binding at a time: each writes its own summary and keeps the other's
    # report, so the four concurrent CI steps never write one file.
    monkeypatch.setattr(coverage_run, "RUNNERS", [("go", green), ("rust", red)])
    assert coverage_run.main(["--binding", "go"]) == 0
    assert coverage_run.main(["--binding", "rust"]) == 1
    whole = json.loads((tmp_path / "abc1234" / "summary.json").read_text())
    assert sorted(whole["verdicts"]) == ["go", "rust"]
    go_only = json.loads((tmp_path / "abc1234" / "summary-go.json").read_text())
    assert list(go_only["verdicts"]) == ["go"]
    assert go_only["passed"] is True
    rust_only = json.loads((tmp_path / "abc1234" / "summary-rust.json").read_text())
    assert list(rust_only["verdicts"]) == ["rust"]
    assert rust_only["passed"] is False
    assert (tmp_path / "abc1234" / "go.json").is_file()
    assert (tmp_path / "abc1234" / "rust.json").is_file()


def test_main_measures_nothing_out_of_scope_and_passes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Main measures nothing out of scope and passes."""
    monkeypatch.delenv("ALETHEIA_COVERAGE_NO_DIFF_SCOPE", raising=False)
    _fake_diff(monkeypatch, files=["docs/x.md"])
    monkeypatch.setattr(coverage_run, "ARTIFACT_BASE", tmp_path)
    monkeypatch.setattr(coverage_run, "short_sha", _sha)

    def never(_art: Path, _spec: coverage_run.Spec) -> CoverageReport:
        pytest.fail("a binding out of scope was measured")

    monkeypatch.setattr(coverage_run, "RUNNERS", [("go", never)])
    assert coverage_run.main([]) == 0
    summary = json.loads((tmp_path / "abc1234" / "summary.json").read_text())
    assert summary["runs"] == []
    assert summary["passed"] is True

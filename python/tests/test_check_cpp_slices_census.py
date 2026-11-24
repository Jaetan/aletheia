# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The slices census gate records the whole tree's census and holds the slices' union to it.

``tools/check_cpp_slices_census.py`` has three faces: ``--census`` builds the
whole tree, dry-runs it and records the report, ``--compare`` unions the
slices' reports found under a directory and holds the union to that record,
and ``--slices`` builds and dry-runs each slice and compares them so.  The
build, the dry run and the search for the toolchain are replaced here by
answers the test writes, and the reports are planted, so each refusal and the
pass are read without a compiler.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, NamedTuple

import pytest
from _processes import CommandWord

from tools import check_cpp_slices_census
from tools.check_cpp_slices_census import (
    GATE,
    MutantId,
    ReportName,
    census,
    census_difference,
    compare,
    dry_run_slices,
    find_reports,
)
from tools.mutation_cpp_elements import MullPath
from tools.mutation_cpp_legs import CPP_WHOLE_CENSUS, CppLeg
from tools.mutation_report import MutationReport

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools.mutation_cpp import LegPaths
    from tools.pin_scope import PinGate

# What one planted Elements report says: each file's mutants, by identifier.
type PlantedFiles = Mapping[MullPath, Sequence[MutantId]]

_SLICE_REPORTS = [ReportName(f"{CppLeg(number).report_name}.json") for number in (1, 2, 3)]
_WHOLE_REPORT = ReportName(CPP_WHOLE_CENSUS)

# The files of a tree of three slices, one per slice.
_A = MullPath("/t/cpp/src/a.cpp")
_B = MullPath("/t/cpp/src/b.cpp")
_C = MullPath("/t/cpp/src/c.cpp")

# Three slices that partition the three files, and the whole tree's census of them.
_SLICES: list[PlantedFiles] = [
    {_A: [MutantId("m:a:1"), MutantId("m:a:2")]},
    {_B: [MutantId("m:b:1")]},
    {_C: [MutantId("m:c:1")]},
]
_WHOLE: PlantedFiles = {
    _A: [MutantId("m:a:1"), MutantId("m:a:2")],
    _B: [MutantId("m:b:1")],
    _C: [MutantId("m:c:1")],
}


def _elements(files: PlantedFiles) -> Prose:
    """Spell an Elements report carrying ``files``, as Mull writes one."""
    report = {
        "files": {
            path: {"mutants": [{"id": identifier} for identifier in identifiers]}
            for path, identifiers in files.items()
        }
    }
    return Prose(json.dumps(report))


def _plant(legs_dir: Path, slices: Sequence[PlantedFiles], whole: PlantedFiles) -> Path:
    """Write each slice's report and the whole census under ``legs_dir``, each in its own leg."""
    for name, files in zip(_SLICE_REPORTS, slices, strict=True):
        leg_dir = legs_dir / name.removesuffix(".json")
        leg_dir.mkdir(parents=True)
        _ = (leg_dir / name).write_text(_elements(files), encoding="utf-8")
    _ = (legs_dir / _SLICE_REPORTS[0].removesuffix(".json") / _WHOLE_REPORT).write_text(
        _elements(whole), encoding="utf-8"
    )
    return legs_dir


def test_a_union_equal_to_the_census_is_no_difference() -> None:
    """Order and repetition aside, the same identifiers are no difference."""
    whole = [MutantId("m:1"), MutantId("m:2")]
    union = [MutantId("m:2"), MutantId("m:1"), MutantId("m:1")]
    assert census_difference(whole, union) is None


def test_the_census_carrying_what_no_slice_does_is_named_three_at_a_time() -> None:
    """A mutant only the whole tree carries is named, three of them at most, with the sizes."""
    whole = [MutantId(f"m:{number}") for number in range(1, 6)]
    union = [MutantId("m:1")]
    assert census_difference(whole, union) == Prose(
        "the whole tree carries 5 mutants and the slices' union 1\n"
        + "the whole tree carries m:2 and no slice does\n"
        + "the whole tree carries m:3 and no slice does\n"
        + "the whole tree carries m:4 and no slice does"
    )


def test_a_slice_carrying_what_the_census_lacks_is_named() -> None:
    """A mutant only a slice carries is named beside those only the whole tree carries."""
    whole = [MutantId("m:1"), MutantId("m:2")]
    union = [MutantId("m:1"), MutantId("m:9")]
    assert census_difference(whole, union) == Prose(
        "the whole tree carries 2 mutants and the slices' union 2\n"
        + "the whole tree carries m:2 and no slice does\n"
        + "a slice carries m:9 and the whole tree does not"
    )


def test_every_report_is_found_once_wherever_it_lies(tmp_path: Path) -> None:
    """Each slice's report and the census are found under their own leg directories."""
    legs_dir = _plant(tmp_path, _SLICES, _WHOLE)
    found = find_reports(legs_dir)
    assert not isinstance(found, str)
    assert dict(found) == {
        _SLICE_REPORTS[0]: legs_dir / "cpp-mull-1" / "cpp-mull-1.json",
        _SLICE_REPORTS[1]: legs_dir / "cpp-mull-2" / "cpp-mull-2.json",
        _SLICE_REPORTS[2]: legs_dir / "cpp-mull-3" / "cpp-mull-3.json",
        _WHOLE_REPORT: legs_dir / "cpp-mull-1" / CPP_WHOLE_CENSUS,
    }


def test_a_missing_slice_report_is_named_with_the_stage_that_writes_it(tmp_path: Path) -> None:
    """A slice whose report is not there is named with the lane stage that writes it."""
    legs_dir = _plant(tmp_path, _SLICES, _WHOLE)
    (legs_dir / "cpp-mull-2" / "cpp-mull-2.json").unlink()
    assert find_reports(legs_dir) == Prose(
        f"0 copies of cpp-mull-2.json under {legs_dir}, wanted one: run the lane at stage 2"
    )


def test_a_census_present_twice_is_named_with_the_face_that_writes_it(tmp_path: Path) -> None:
    """Two copies of the census is no census: the refusal names the face that writes it."""
    legs_dir = _plant(tmp_path, _SLICES, _WHOLE)
    _ = (legs_dir / "cpp-mull-3" / _WHOLE_REPORT).write_text(_elements(_WHOLE), encoding="utf-8")
    assert find_reports(legs_dir) == Prose(
        f"2 copies of {CPP_WHOLE_CENSUS} under {legs_dir}, wanted one: "
        + "run --census in the first leg"
    )


def test_slices_that_union_to_the_census_pass_naming_their_sizes(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Slices unioning to exactly the census pass, each slice's count and the whole's printed."""
    assert compare(_plant(tmp_path, _SLICES, _WHOLE)) == ExitStatus(0)
    assert (
        capsys.readouterr().out
        == f"{GATE}: slices of 2, 1, 1 union to the whole tree's 4 mutants\n"
    )


def test_a_slice_carrying_a_mutant_the_census_lacks_fails(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A mutant a slice carries that the whole tree does not is a renamed mutant, refused."""
    slices: list[PlantedFiles] = [
        _SLICES[0],
        {_B: [MutantId("m:b:1"), MutantId("m:b:9")]},
        _SLICES[2],
    ]
    assert compare(_plant(tmp_path, slices, _WHOLE)) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{GATE}: the whole tree carries 4 mutants and the slices' union 5\n"
        + "a slice carries m:b:9 and the whole tree does not\n"
    )


def test_a_census_mutant_no_slice_carries_fails(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A mutant the whole tree carries and no slice does is a lost mutant, refused."""
    whole: PlantedFiles = {**_WHOLE, MullPath("/t/cpp/src/d.cpp"): [MutantId("m:d:1")]}
    assert compare(_plant(tmp_path, _SLICES, whole)) == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{GATE}: the whole tree carries 5 mutants and the slices' union 4\n"
        + "the whole tree carries m:d:1 and no slice does\n"
    )


def test_a_mutant_two_slices_carry_is_the_union_s_refusal(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A file no slice held out arrives from every slice, and the union refuses it first."""
    slices: list[PlantedFiles] = [
        _SLICES[0],
        {_B: [MutantId("m:b:1")], _C: [MutantId("m:c:1")]},
        _SLICES[2],
    ]
    assert compare(_plant(tmp_path, slices, _WHOLE)) == ExitStatus(1)
    assert capsys.readouterr().out.startswith(
        f"{GATE}: slices 2 and 3 both carry m:c:1 in /t/cpp/src/c.cpp: "
    )


def test_a_missing_report_is_no_answer(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With a slice's report missing the comparison reaches no claim."""
    legs_dir = _plant(tmp_path, _SLICES, _WHOLE)
    (legs_dir / "cpp-mull-3" / "cpp-mull-3.json").unlink()
    assert compare(legs_dir) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{GATE}: 0 copies of cpp-mull-3.json under {legs_dir}, wanted one: "
        + "run the lane at stage 3\n"
    )


def test_a_report_present_twice_is_no_answer(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With a slice's report there twice the comparison reaches no claim."""
    legs_dir = _plant(tmp_path, _SLICES, _WHOLE)
    _ = (legs_dir / "cpp-mull-2" / "cpp-mull-1.json").write_text(
        _elements(_SLICES[0]), encoding="utf-8"
    )
    assert compare(legs_dir) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"{GATE}: 2 copies of cpp-mull-1.json under {legs_dir}, wanted one: "
        + "run the lane at stage 1\n"
    )


# What a failed build logs: the configure, then the compiler's refusal.
_BUILD_LOG = Prose("=== cmake configure ===\nfake cmake refuses\n")


# What each leg's build carries: the whole tree its census, each slice its own files.
_CARRIED: Mapping[CppLeg, PlantedFiles] = {
    CppLeg(): _WHOLE,
    **{CppLeg(number): files for number, files in enumerate(_SLICES, start=1)},
}


class _Answers(NamedTuple):
    """What the stand-in lane answers.

    A build fails with ``build_error`` where told to: every build, or only the
    one in the tree of ``failing``.  A dry run reports what ``carried`` says
    the leg's build carries.
    """

    tools: Prose | None = None
    build_error: Prose | None = None
    failing: CppLeg | None = None
    writes_report: bool = True
    carried: Mapping[CppLeg, PlantedFiles] = _CARRIED


# A lane whose every answer is the plain one.
_PLAIN = _Answers()


class _Lane:
    """Stand in for the lane: the toolchain, the build and the dry run, each answering as told."""

    def __init__(self, root: Path, answers: _Answers) -> None:
        self.root = root
        self.answers = answers
        self.built: list[tuple[CommandWord, LegPaths]] = []
        self.dry_runs: list[tuple[CppLeg, Path]] = []
        self.configured: list[tuple[CppLeg, Path]] = []

    def check_tools(self) -> tuple[CommandWord, CommandWord] | Prose:
        """Answer the toolchain search as told."""
        if self.answers.tools is not None:
            return self.answers.tools
        return (CommandWord("/usr/bin/cmake"), CommandWord("/usr/bin/mull-runner-23"))

    def build(self, cmake: CommandWord, paths: LegPaths) -> Prose | MutationReport:
        """Record the build and answer it as told, a failed one writing its log as the lane does."""
        self.built.append((cmake, paths))
        failing = self.answers.failing
        error = self.answers.build_error
        if error is not None and (failing is None or paths.build_dir == self.build_dir(failing)):
            _ = (paths.artifact_dir / "cpp.raw.txt").write_text(_BUILD_LOG, encoding="utf-8")
            return MutationReport("cpp", "mull", 0, 0, Prose(_BUILD_LOG), error=error)
        return Prose("built\n")

    def dry_run(self, leg: CppLeg, report_dir: Path) -> Path | Prose:
        """Record the dry run and write what the leg's build carries where asked, when told to."""
        self.dry_runs.append((leg, report_dir))
        if not self.answers.writes_report:
            return Prose(f"the dry run of the {leg} leg wrote no {leg.report_name}.json")
        report = report_dir / f"{leg.report_name}.json"
        _ = report.write_text(_elements(self.answers.carried[leg]), encoding="utf-8")
        return report

    def config(self, leg: CppLeg, build_dir: Path) -> Path:
        """Record the configuration asked for and name the lane's own."""
        self.configured.append((leg, build_dir))
        return self.root / "cpp" / "mull.yml"

    def sweep_directory(self) -> Path:
        """Name the directory the lane sweeps in."""
        return self.root / "cpp"

    def build_dir(self, leg: CppLeg) -> Path:
        """Name the directory the leg builds in."""
        return self.root / "cpp" / leg.directory


def _lane(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, answers: _Answers = _PLAIN) -> _Lane:
    """Put a lane answering as told under the gate, rooted in ``tmp_path``."""
    lane = _Lane(tmp_path, answers)

    def commit(_root: Path) -> Prose:
        return Prose("abc1234")

    monkeypatch.setattr(check_cpp_slices_census, "check_cpp_tools", lane.check_tools)
    monkeypatch.setattr(check_cpp_slices_census, "build_cpp_mutation_tree", lane.build)
    monkeypatch.setattr(check_cpp_slices_census, "dry_run_report", lane.dry_run)
    monkeypatch.setattr(check_cpp_slices_census, "leg_config", lane.config)
    monkeypatch.setattr(check_cpp_slices_census, "cpp_sweep_directory", lane.sweep_directory)
    monkeypatch.setattr(check_cpp_slices_census, "leg_build_dir", lane.build_dir)
    monkeypatch.setattr(check_cpp_slices_census, "short_sha", commit)
    monkeypatch.setattr(
        check_cpp_slices_census, "ARTIFACT_BASE", tmp_path / "benchmarks" / "mutation"
    )
    return lane


def test_the_census_is_built_as_the_lane_builds_and_recorded_beside_the_reports(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The whole tree is built with the lane's paths, dry-run apart, and its census recorded.

    The lane's own sweep of the whole tree, beside it, is held to the census
    and left as it was.
    """
    lane = _lane(monkeypatch, tmp_path)
    artifact_dir = tmp_path / "benchmarks" / "mutation" / "abc1234"
    artifact_dir.mkdir(parents=True)
    own_sweep = artifact_dir / "cpp-mull.json"
    _ = own_sweep.write_text(_elements(_WHOLE), encoding="utf-8")
    assert census() == ExitStatus(0)
    whole = CppLeg()
    build_dir = tmp_path / "cpp" / "build-mutation"
    assert lane.configured == [(whole, build_dir)]
    assert len(lane.built) == 1
    cmake, paths = lane.built[0]
    assert cmake == "/usr/bin/cmake"
    assert paths.cpp_root == tmp_path / "cpp"
    assert paths.build_dir == build_dir
    assert paths.artifact_dir != artifact_dir
    assert paths.config == tmp_path / "cpp" / "mull.yml"
    assert len(lane.dry_runs) == 1
    leg, report_dir = lane.dry_runs[0]
    assert leg == whole
    assert report_dir == paths.artifact_dir
    assert not report_dir.exists()
    recorded = artifact_dir / CPP_WHOLE_CENSUS
    assert json.loads(recorded.read_text(encoding="utf-8")) == json.loads(_elements(_WHOLE))
    assert own_sweep.read_text(encoding="utf-8") == _elements(_WHOLE)
    assert capsys.readouterr().out == (
        f"{GATE}: the whole tree carries 4 mutants, recorded in {recorded}\n"
        + f"{GATE}: the cpp leg's sweep reports the 4 mutants its dry run lists\n"
    )


def _sweep_beside(tmp_path: Path, leg: CppLeg, files: PlantedFiles) -> None:
    """Write the report ``leg``'s sweep would leave in the artifact directory."""
    artifact_dir = tmp_path / "benchmarks" / "mutation" / "abc1234"
    artifact_dir.mkdir(parents=True, exist_ok=True)
    _ = (artifact_dir / f"{leg.report_name}.json").write_text(_elements(files), encoding="utf-8")


def test_with_no_sweep_beside_it_the_census_is_recorded_alone(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no sweep report to hold, the census is the face's one answer."""
    lane = _lane(monkeypatch, tmp_path)
    assert census() == ExitStatus(0)
    assert [leg for leg, _report_dir in lane.dry_runs] == [CppLeg()]
    recorded = tmp_path / "benchmarks" / "mutation" / "abc1234" / CPP_WHOLE_CENSUS
    assert capsys.readouterr().out == (
        f"{GATE}: the whole tree carries 4 mutants, recorded in {recorded}\n"
    )


def test_a_whole_sweep_reporting_other_mutants_than_the_census_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A local sweep listing a mutant the dry run does not, and missing one it does, is refused."""
    _ = _lane(monkeypatch, tmp_path)
    _sweep_beside(tmp_path, CppLeg(), {**_WHOLE, _C: [MutantId("m:c:9")]})
    assert census() == ExitStatus(1)
    assert capsys.readouterr().out.splitlines()[1:] == [
        f"{GATE}: a dry run of the cpp leg's build lists 4 mutants and its sweep reports 4",
        "a dry run lists m:c:1 and the sweep does not",
        "the sweep reports m:c:9 and a dry run does not",
    ]


def test_a_slice_s_sweep_is_held_to_a_dry_run_of_its_tree_unbuilt(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A CI leg's slice report is held to a dry run of the slice's tree, which is not rebuilt."""
    lane = _lane(monkeypatch, tmp_path)
    _sweep_beside(tmp_path, CppLeg(1), _SLICES[0])
    assert census() == ExitStatus(0)
    assert [paths.build_dir.name for _cmake, paths in lane.built] == ["build-mutation"]
    assert [leg for leg, _report_dir in lane.dry_runs] == [CppLeg(), CppLeg(1)]
    assert capsys.readouterr().out.splitlines()[1:] == [
        f"{GATE}: the cpp-1 leg's sweep reports the 2 mutants its dry run lists",
    ]


def test_a_slice_s_sweep_missing_a_mutant_its_dry_run_lists_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A slice's sweep that dropped a mutant its build carries is refused, naming it."""
    _ = _lane(monkeypatch, tmp_path)
    _sweep_beside(tmp_path, CppLeg(1), {_A: [MutantId("m:a:1")]})
    assert census() == ExitStatus(1)
    assert capsys.readouterr().out.splitlines()[1:] == [
        f"{GATE}: a dry run of the cpp-1 leg's build lists 2 mutants and its sweep reports 1",
        "a dry run lists m:a:2 and the sweep does not",
    ]


def test_a_slice_s_dry_run_writing_no_report_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no dry run of the slice's tree to hold its sweep to, the face reaches no claim."""
    lane = _lane(monkeypatch, tmp_path)
    _sweep_beside(tmp_path, CppLeg(2), _SLICES[1])

    def whole_only(leg: CppLeg, report_dir: Path) -> Path | Prose:
        if leg.slice_no is None:
            return lane.dry_run(leg, report_dir)
        return Prose(f"the dry run of the {leg} leg wrote no {leg.report_name}.json")

    monkeypatch.setattr(check_cpp_slices_census, "dry_run_report", whole_only)
    assert census() == ExitStatus(2)
    assert capsys.readouterr().out.splitlines()[1:] == [
        f"{GATE}: the dry run of the cpp-2 leg wrote no cpp-mull-2.json",
    ]


def test_a_missing_tool_is_no_answer_and_builds_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without the toolchain the gate names what is missing and builds nothing."""
    lane = _lane(monkeypatch, tmp_path, _Answers(tools=Prose("mull-runner-23 not in PATH")))
    assert census() == ExitStatus(2)
    assert not lane.built
    assert not lane.dry_runs
    assert capsys.readouterr().out == f"{GATE}: mull-runner-23 not in PATH\n"


def test_a_tree_that_does_not_build_is_no_answer_and_is_not_dry_run(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A failed build is reported with its error and its log's tail, and nothing is dry-run.

    The build logs where the gate tells it to, so the lane's own log of a
    sweep at the same commit, beside its reports, is left as it was.
    """
    lane = _lane(monkeypatch, tmp_path, _Answers(build_error=Prose("cmake build failed (exit 2)")))
    artifact_dir = tmp_path / "benchmarks" / "mutation" / "abc1234"
    artifact_dir.mkdir(parents=True)
    own_log = artifact_dir / "cpp.raw.txt"
    _ = own_log.write_text("the lane's own sweep log\n", encoding="utf-8")
    assert census() == ExitStatus(2)
    assert len(lane.built) == 1
    assert lane.built[0][1].artifact_dir != artifact_dir
    assert not lane.dry_runs
    assert not (artifact_dir / CPP_WHOLE_CENSUS).exists()
    assert own_log.read_text(encoding="utf-8") == "the lane's own sweep log\n"
    assert capsys.readouterr().out == (
        f"{GATE}: cmake build failed (exit 2)\n=== cmake configure ===\nfake cmake refuses\n"
    )


def test_a_dry_run_writing_no_report_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A dry run that writes no report leaves no census and the gate says so."""
    lane = _lane(monkeypatch, tmp_path, _Answers(writes_report=False))
    assert census() == ExitStatus(2)
    assert len(lane.dry_runs) == 1
    assert not (tmp_path / "benchmarks" / "mutation" / "abc1234" / CPP_WHOLE_CENSUS).exists()
    assert capsys.readouterr().out == f"{GATE}: the dry run of the cpp leg wrote no cpp-mull.json\n"


def _record_census(tmp_path: Path) -> Path:
    """Write the whole tree's census where ``--census`` records it, and return the directory."""
    artifact_dir = tmp_path / "benchmarks" / "mutation" / "abc1234"
    artifact_dir.mkdir(parents=True)
    _ = (artifact_dir / CPP_WHOLE_CENSUS).write_text(_elements(_WHOLE), encoding="utf-8")
    return artifact_dir


def test_each_slice_is_built_as_its_leg_builds_and_their_union_held_to_the_census(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Each slice is built in its leg's tree under its leg's configuration, dry-run apart, compared.

    The slices' reports never reach the artifact directory, where the
    comparison of the legs' own reports would find them.
    """
    lane = _lane(monkeypatch, tmp_path)
    artifact_dir = _record_census(tmp_path)
    assert dry_run_slices() == ExitStatus(0)
    legs = [CppLeg(number) for number in (1, 2, 3)]
    build_dirs = [tmp_path / "cpp" / f"build-mutation-{number}" for number in (1, 2, 3)]
    assert lane.configured == list(zip(legs, build_dirs, strict=True))
    assert [paths.build_dir for _cmake, paths in lane.built] == build_dirs
    assert [leg for leg, _report_dir in lane.dry_runs] == legs
    assert [report_dir for _leg, report_dir in lane.dry_runs] == [
        paths.artifact_dir for _cmake, paths in lane.built
    ]
    assert len({report_dir for _leg, report_dir in lane.dry_runs}) == len(legs)
    assert not any(report_dir.exists() for _leg, report_dir in lane.dry_runs)
    assert list(artifact_dir.iterdir()) == [artifact_dir / CPP_WHOLE_CENSUS]
    assert (
        capsys.readouterr().out
        == f"{GATE}: slices of 2, 1, 1 union to the whole tree's 4 mutants\n"
    )


def test_a_slice_whose_build_carries_what_the_census_lacks_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A mutant only a slice's build carries is refused, as the merge refuses it."""
    carried = {**_CARRIED, CppLeg(2): {_B: [MutantId("m:b:1"), MutantId("m:b:9")]}}
    _ = _lane(monkeypatch, tmp_path, _Answers(carried=carried))
    _ = _record_census(tmp_path)
    assert dry_run_slices() == ExitStatus(1)
    assert capsys.readouterr().out == (
        f"{GATE}: the whole tree carries 4 mutants and the slices' union 5\n"
        + "a slice carries m:b:9 and the whole tree does not\n"
    )


def test_without_a_recorded_census_the_slices_are_no_answer_and_unbuilt(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With nothing to compare them with, no slice is built."""
    lane = _lane(monkeypatch, tmp_path)
    assert dry_run_slices() == ExitStatus(2)
    assert not lane.built
    recorded = tmp_path / "benchmarks" / "mutation" / "abc1234" / CPP_WHOLE_CENSUS
    assert capsys.readouterr().out == f"{GATE}: no census at {recorded}: run --census first\n"


def test_a_slice_that_does_not_build_ends_the_face_before_the_next(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The slice that does not build is not dry-run, and no later slice is built."""
    failing = _Answers(build_error=Prose("cmake build failed (exit 2)"), failing=CppLeg(2))
    lane = _lane(monkeypatch, tmp_path, failing)
    _ = _record_census(tmp_path)
    assert dry_run_slices() == ExitStatus(2)
    assert [paths.build_dir.name for _cmake, paths in lane.built] == [
        "build-mutation-1",
        "build-mutation-2",
    ]
    assert [leg for leg, _report_dir in lane.dry_runs] == [CppLeg(1)]
    assert capsys.readouterr().out == (
        f"{GATE}: cmake build failed (exit 2)\n=== cmake configure ===\nfake cmake refuses\n"
    )


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing the gate rests on."""
    return False


def _in_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved what the gate rests on."""
    return True


def _never_census() -> ExitStatus:
    """Fail the test if the gate reaches for the build."""
    raise AssertionError


def _never_compare(_legs_dir: Path) -> ExitStatus:
    """Fail the test if the gate reaches for the reports."""
    raise AssertionError


def _never_slices() -> ExitStatus:
    """Fail the test if the gate reaches for the slices' builds."""
    raise AssertionError


@pytest.mark.parametrize("face", [["--census"], ["--compare", "legs"], ["--slices"]])
def test_a_branch_moving_nothing_the_fact_rests_on_runs_neither_face(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, face: list[CommandWord]
) -> None:
    """Out of scope, the gate passes without building or reading a report."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_cpp_slices_census, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cpp_slices_census, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_cpp_slices_census, "census", _never_census)
    monkeypatch.setattr(check_cpp_slices_census, "compare", _never_compare)
    monkeypatch.setattr(check_cpp_slices_census, "dry_run_slices", _never_slices)
    monkeypatch.setattr("sys.argv", ["check_cpp_slices_census", *face])
    assert check_cpp_slices_census.main() == ExitStatus(0)


def test_in_scope_the_census_face_s_verdict_is_the_census_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the fact rests on gets the census's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def refusing() -> ExitStatus:
        return ExitStatus(2)

    monkeypatch.setattr(check_cpp_slices_census, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cpp_slices_census, "gate_runs", _in_scope)
    monkeypatch.setattr(check_cpp_slices_census, "census", refusing)
    monkeypatch.setattr(check_cpp_slices_census, "compare", _never_compare)
    monkeypatch.setattr(check_cpp_slices_census, "dry_run_slices", _never_slices)
    monkeypatch.setattr("sys.argv", ["check_cpp_slices_census", "--census"])
    assert check_cpp_slices_census.main() == ExitStatus(2)


def test_in_scope_the_slices_face_s_verdict_is_the_slices_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the fact rests on gets the slices' own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def refusing() -> ExitStatus:
        return ExitStatus(1)

    monkeypatch.setattr(check_cpp_slices_census, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cpp_slices_census, "gate_runs", _in_scope)
    monkeypatch.setattr(check_cpp_slices_census, "census", _never_census)
    monkeypatch.setattr(check_cpp_slices_census, "compare", _never_compare)
    monkeypatch.setattr(check_cpp_slices_census, "dry_run_slices", refusing)
    monkeypatch.setattr("sys.argv", ["check_cpp_slices_census", "--slices"])
    assert check_cpp_slices_census.main() == ExitStatus(1)


def test_in_scope_the_compare_face_s_verdict_is_the_comparison_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving what the fact rests on gets the comparison's exit over the directory."""

    def the_tree() -> Path:
        return tmp_path

    def refusing(legs_dir: Path) -> ExitStatus:
        assert legs_dir == tmp_path / "legs"
        return ExitStatus(1)

    monkeypatch.setattr(check_cpp_slices_census, "git_toplevel", the_tree)
    monkeypatch.setattr(check_cpp_slices_census, "gate_runs", _in_scope)
    monkeypatch.setattr(check_cpp_slices_census, "census", _never_census)
    monkeypatch.setattr(check_cpp_slices_census, "compare", refusing)
    monkeypatch.setattr(check_cpp_slices_census, "dry_run_slices", _never_slices)
    legs_dir = tmp_path / "legs"
    monkeypatch.setattr("sys.argv", ["check_cpp_slices_census", "--compare", str(legs_dir)])
    assert check_cpp_slices_census.main() == ExitStatus(1)


@pytest.mark.parametrize(
    "argv",
    [
        [],
        ["--unknown"],
        ["--census", "--compare", "legs"],
        ["--census", "--slices"],
        ["--slices", "--compare", "legs"],
        ["--compare"],
    ],
)
def test_the_gate_refuses_what_is_not_one_face(
    monkeypatch: pytest.MonkeyPatch, argv: list[CommandWord]
) -> None:
    """No face, an unknown argument, two faces or a bare --compare stop the gate as it starts."""
    monkeypatch.setattr("sys.argv", ["check_cpp_slices_census", *argv])
    with pytest.raises(SystemExit) as stopped:
        _ = check_cpp_slices_census.main()
    assert stopped.value.code == 2

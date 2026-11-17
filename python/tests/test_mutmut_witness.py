# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The mutmut witness gate asks each fact from a scratch project and names each it refuses.

``tools/check_mutmut_witness.py`` asks the venv's mutmut, through its own code,
for what the Python lane's witness and its checks read.  These tests stand in
for the facts: every refusal is named and fails the gate, a venv without
mutmut is no answer, an import failing for another package is raised, the
facts are asked from a scratch project that names one source and turns the
log on, and out of scope the gate asks nothing.  What the pinned mutmut itself
answers is the gate's own run in the mutation lane.
"""

from __future__ import annotations

import collections
import importlib
import json
import logging
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import TYPE_CHECKING, Literal, NewType, cast

import pytest

from tools import check_mutmut_witness
from tools.check_mutmut_operators import INSTALL_HINT
from tools.check_mutmut_witness import STATUSES, check

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterator
    from types import ModuleType

    from tools.mutation_witness import MutantName
    from tools.pin_scope import PinGate

# A dotted module name, as import_module takes it.
ModuleName = NewType("ModuleName", str)


def _refusing(missing: ModuleName) -> ModuleType:
    """Fail the import of ``missing`` as a venv without it would."""
    raise ImportError(name=missing)


def test_each_refused_fact_is_named_and_fails_the_gate(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Every fact mutmut no longer holds reaches stdout, in order, and the gate exits 1."""

    def refused(_scratch: Path) -> list[Prose]:
        return [Prose("the first fact"), Prose("the second fact")]

    monkeypatch.setattr(check_mutmut_witness, "facts_refused", refused)
    assert check() == ExitStatus(1)
    assert capsys.readouterr().out == (
        "check-mutmut-witness: the first fact\ncheck-mutmut-witness: the second fact\n"
    )


def test_every_fact_holding_passes_silently(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no fact refused the gate exits 0 and writes nothing."""

    def holding(_scratch: Path) -> list[Prose]:
        return []

    monkeypatch.setattr(check_mutmut_witness, "facts_refused", holding)
    assert check() == ExitStatus(0)
    assert capsys.readouterr() == ("", "")


def test_the_facts_are_asked_from_a_scratch_project(monkeypatch: pytest.MonkeyPatch) -> None:
    """The facts are asked inside a project made for them, since mutmut reads the one it runs in."""
    seen: list[Prose] = []
    before = Path.cwd()

    def looking(scratch: Path) -> list[Prose]:
        seen.extend(
            [
                Prose(str(Path.cwd() == scratch)),
                Prose((scratch / "pyproject.toml").read_text(encoding="utf-8")),
                Prose((scratch / "m.py").read_text(encoding="utf-8")),
            ]
        )
        return []

    monkeypatch.setattr(check_mutmut_witness, "facts_refused", looking)
    assert check() == ExitStatus(0)
    assert seen == [
        "True",
        '[tool.mutmut]\nsource_paths = ["m.py"]\nlog_to_file = true\n',
        "",
    ]
    assert Path.cwd() == before


def test_a_venv_without_mutmut_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without mutmut the gate exits 2 and names the extra that installs it."""

    def importer(name: ModuleName) -> ModuleType:
        if name.split(".", 1)[0] == "mutmut":
            return _refusing(name)
        return importlib.import_module(name)

    monkeypatch.setattr(check_mutmut_witness, "import_module", importer)
    assert check() == ExitStatus(2)
    assert capsys.readouterr().out == f"check-mutmut-witness: {INSTALL_HINT}\n"


def test_an_import_that_fails_for_another_package_is_raised(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An import failing for a module the extra does not install is a defect, raised as it is."""

    def importer(_name: ModuleName) -> ModuleType:
        return _refusing(ModuleName("yaml.loader"))

    monkeypatch.setattr(check_mutmut_witness, "import_module", importer)
    with pytest.raises(ImportError) as raised:
        _ = check()
    assert raised.value.name == "yaml.loader"


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked() -> ExitStatus:
    """Fail the test if the gate reaches for mutmut."""
    raise AssertionError


def test_a_branch_moving_nothing_the_facts_rest_on_asks_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without asking mutmut."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_mutmut_witness, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mutmut_witness, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_mutmut_witness, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_mutmut_witness"])
    assert check_mutmut_witness.main() == ExitStatus(0)


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving the pin or a reader of it gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(_gate: PinGate, root: Path) -> bool:
        assert root == tmp_path
        return True

    def refusing() -> ExitStatus:
        return ExitStatus(1)

    monkeypatch.setattr(check_mutmut_witness, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mutmut_witness, "gate_runs", in_scope)
    monkeypatch.setattr(check_mutmut_witness, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_mutmut_witness"])
    assert check_mutmut_witness.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(monkeypatch: pytest.MonkeyPatch) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_mutmut_witness", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_mutmut_witness.main()
    assert stopped.value.code == 2


# mutmut's exit table as the pinned release files the exits the gate reads.
_TABLE = dict(STATUSES)


def _named(*, mutant_name: MutantName | None, tests: list[Prose]) -> ExitStatus:
    """Stand in for ``PytestRunner.run_tests``, naming its mutant as the pinned release does."""
    _ = mutant_name, tests
    return ExitStatus(0)


def _renamed(*, mutant: MutantName | None, tests: list[Prose]) -> ExitStatus:
    """Name the mutant under another parameter, as a later release might."""
    _ = mutant, tests
    return ExitStatus(0)


# The listing mutmut's run calls, which a shard's deal wraps.
_LISTING = Prose("collect_source_file_mutation_data")

# What the stand-in listing gives: each mutant's file data, name and exit, and
# every file's data by path.
type _ListedMutant = tuple[SimpleNamespace, MutantName, ExitStatus | None]
type _Listed = list[_ListedMutant]
type _ByPath = dict[Prose, SimpleNamespace]

# How the stand-in run and listing behave: as pinned, or with one fact of the deal moved.
type _ListingMove = Literal["as pinned", "called otherwise", "names", "checked only", "absent"]

# Where and how the pinned release keeps its exits and its log.
_META_KEY = Prose("exit_code_by_key")
_META_SUFFIX = Prose(".meta")
_LOG = Prose("mutants/mutmut-debug.log")


@dataclass(frozen=True)
class _Release:
    """mutmut as the stand-ins behave: the pinned release, or it with one fact moved."""

    parameter: Literal["mutant_name", "mutant"] = "mutant_name"
    table: dict[ExitStatus | None, Prose] = field(default_factory=lambda: dict(_TABLE))
    key: Prose = _META_KEY
    suffix: Prose = _META_SUFFIX
    line: Prose | None = None
    log_to_file: bool = True
    log: Prose = _LOG


def _stand_ins(
    release: _Release, listing_move: _ListingMove = "as pinned"
) -> dict[Prose, SimpleNamespace]:
    """Return mutmut's six modules as ``release`` and ``listing_move`` behave, by their names."""
    stats = SimpleNamespace(status_by_exit_code=release.table, print_status=None)
    saved: list[SimpleNamespace] = []

    def source_data(*, path: Prose) -> SimpleNamespace:
        """Stand in for ``SourceFileMutationData``, writing its ``.meta`` as ``release`` does."""
        data = SimpleNamespace(exit_code_by_key={})

        def save() -> None:
            meta = Path("mutants") / f"{path}{release.suffix}"
            text = json.dumps({release.key: data.exit_code_by_key})
            _ = meta.write_text(text, encoding="utf-8")
            saved.append(data)

        data.save = save
        return data

    def print_stats(by_path: dict[Prose, SimpleNamespace], *, force_output: bool = False) -> None:
        counts = collections.Counter(
            str(release.table[code])
            for data in by_path.values()
            for code in data.exit_code_by_key.values()
        )
        total = sum(counts.values())
        line = release.line or Prose(
            f"{total - counts['not checked']}/{total}  🎉 {counts['killed']} "
            + f"🫥 {counts['no tests']}  ⏰ {counts['timeout']}  🤔 {counts['suspicious']}  "
            + f"🙁 {counts['survived']}  🔇 {counts['skipped']}  "
            + f"🧙 {counts['caught by type check']}"
        )
        stats.print_status(line, force_output=force_output)

    def setup_file_logging() -> None:
        log = Path(release.log)
        log.parent.mkdir(parents=True, exist_ok=True)
        logging.getLogger("mutmut").addHandler(logging.FileHandler(log))

    def listing(*, mutant_names: tuple[MutantName, ...]) -> tuple[_Listed, _ByPath]:
        """Stand in for mutmut's listing of the saved file's mutants, as ``release`` gives them."""
        _ = mutant_names
        mutants = [
            (data, name, code) for data in saved for name, code in data.exit_code_by_key.items()
        ]
        if listing_move == "names":
            return cast("_Listed", [name for _, name, _ in mutants]), {}
        if listing_move == "checked only":
            mutants = [mutant for mutant in mutants if mutant[2] is not None]
        return mutants, {Prose("m.py"): saved[-1]}

    stats.print_stats = print_stats
    names = () if listing_move == "called otherwise" else (_LISTING,)
    main = SimpleNamespace(_run=SimpleNamespace(__code__=SimpleNamespace(co_names=names)))
    if listing_move != "absent":
        main.collect_source_file_mutation_data = listing
    config = SimpleNamespace(log_to_file=release.log_to_file)
    run_tests = _named if release.parameter == "mutant_name" else _renamed
    return {
        Prose("mutmut.runners.harness"): SimpleNamespace(
            PytestRunner=SimpleNamespace(run_tests=run_tests)
        ),
        Prose("mutmut.stats"): stats,
        Prose("mutmut.mutation.data"): SimpleNamespace(SourceFileMutationData=source_data),
        Prose("mutmut.configuration"): SimpleNamespace(config=lambda: config),
        Prose("mutmut.utils.logging_utils"): SimpleNamespace(setup_file_logging=setup_file_logging),
        Prose("mutmut.__main__"): main,
    }


@pytest.fixture(name="mutmut_logger")
def _mutmut_logger() -> Iterator[logging.Logger]:
    """Hand the ``mutmut`` logger over, and take back each handler a test added to it."""
    logger = logging.getLogger("mutmut")
    before = len(logger.handlers)
    yield logger
    for handler in logger.handlers[before:]:
        logger.removeHandler(handler)
        handler.close()


@pytest.mark.parametrize(
    ("release", "refusal"),
    [
        (_Release(), None),
        (_Release(parameter="mutant"), "the witness cannot install on PytestRunner.run_tests"),
        (
            _Release(table={**_TABLE, ExitStatus(33): Prose("skipped")}),
            "mutmut files exit 33 as 'skipped', not 'no tests'",
        ),
        (_Release(key=Prose("exit_codes")), "the lane cannot read mutmut's own .meta: KeyError"),
        (_Release(suffix=Prose(".data")), "mutmut's .meta files name 0 of the 7 mutants"),
        (_Release(line=Prose("7 judged, 1 killed")), "mutmut printed no count to hold its .meta"),
        (
            _Release(line=Prose("6/7  🎉 4 🫥 0  ⏰ 0  🤔 0  🙁 0  🔇 0  🧙 0")),
            "the lane reads MutmutCounts(killed=4, survived=0, timeout=0, skipped=0)",
        ),
        (_Release(log_to_file=False), "mutmut no longer reads log_to_file"),
        (_Release(log=Prose("elsewhere/mutmut.log")), "mutmut's file log is not mutants/mutmut"),
    ],
    ids=[
        "as pinned",
        "parameter renamed",
        "exit relabelled",
        "meta rekeyed",
        "meta moved",
        "line reshaped",
        "line miscounted",
        "log setting dropped",
        "log moved",
    ],
)
def test_each_fact_a_release_could_move_is_refused_by_name(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    mutmut_logger: logging.Logger,
    release: _Release,
    refusal: Prose | None,
) -> None:
    """Against mutmut as pinned nothing is refused; each fact moved alone is refused, named."""
    _ = mutmut_logger
    monkeypatch.setattr(check_mutmut_witness, "import_module", _stand_ins(release).__getitem__)
    monkeypatch.chdir(tmp_path)
    found = check_mutmut_witness.facts_refused(tmp_path)
    if refusal is None:
        assert found == []
    else:
        assert any(refusal in line for line in found), found


@pytest.mark.parametrize(
    ("listing_move", "refusal"),
    [
        ("called otherwise", "mutmut's run does not look collect_source_file_mutation_data up"),
        ("absent", "mutmut has no collect_source_file_mutation_data for a shard's deal"),
        ("names", "mutmut's listing no longer gives each mutant's data, name and exit"),
        ("checked only", "the first shard of two is dealt"),
    ],
)
def test_each_fact_the_deal_rests_on_is_refused_by_name(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    mutmut_logger: logging.Logger,
    listing_move: _ListingMove,
    refusal: Prose,
) -> None:
    """A run calling its listing otherwise, or a listing gone, reshaped or filtered, is refused."""
    _ = mutmut_logger
    stand_ins = _stand_ins(_Release(), listing_move)
    monkeypatch.setattr(check_mutmut_witness, "import_module", stand_ins.__getitem__)
    monkeypatch.chdir(tmp_path)
    found = check_mutmut_witness.facts_refused(tmp_path)
    assert len(found) == 1, found
    assert found[0][: len(refusal)] == refusal, found


def test_a_lane_check_passing_a_short_tally_is_refused(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, mutmut_logger: logging.Logger
) -> None:
    """A tally check that passes the tally missing a run is a refused fact, not a pass."""
    _ = mutmut_logger

    def passing(_artifacts: Path, _mutants: Path, _line: Prose) -> Prose | None:
        return None

    monkeypatch.setattr(check_mutmut_witness, "import_module", _stand_ins(_Release()).__getitem__)
    monkeypatch.setattr(check_mutmut_witness, "python_witness_refusal", passing)
    monkeypatch.chdir(tmp_path)
    assert check_mutmut_witness.facts_refused(tmp_path) == [
        "the lane passes mutmut's own .meta with a run missing from the tally"
    ]

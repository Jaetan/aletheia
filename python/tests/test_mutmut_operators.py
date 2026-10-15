# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The mutmut operators gate reads the pinned mutmut's answers as the fact, a refusal, or no answer.

``tools/check_mutmut_operators.py`` hands mutmut's operator table a function of
the constructs the Python lane's record calls refusals and a comparison, and
judges what it mutates in each.  The judge is held over planted answers, and
the venv without mutmut by refusing the gate's import of it; what the pinned
mutmut itself answers is the gate's own run in the mutation lane, the one lane
that installs it, as the sibling gates' tools are theirs.
"""

from __future__ import annotations

import importlib
from typing import TYPE_CHECKING, NewType

import pytest

from tools import check_mutmut_operators
from tools.check_mutmut_operators import (
    CONTROL_SOURCE,
    INSTALL_HINT,
    REFUSED_SOURCE,
    MutantNodeText,
    PythonSource,
    check,
    operator_refusal,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from types import ModuleType

    from tools.pin_scope import PinGate

# A module's dotted name, as an import names it.
ModuleName = NewType("ModuleName", str)

# What the table yields for the control comparison.
A_COMPARISON = MutantNodeText("< b")


def test_a_mutation_of_a_refused_construct_is_named_by_its_first_characters() -> None:
    """Each node mutmut mutates in the refused constructs is named, cut at sixty characters."""
    long = MutantNodeText("x" * 70)
    assert operator_refusal([long, MutantNodeText("raise error")], [A_COMPARISON]) == Prose(
        f"mutmut now mutates: {'x' * 60}\nmutmut now mutates: raise error"
    )


def test_a_control_that_yields_nothing_is_a_refusal() -> None:
    """A table that cannot mutate a comparison is not the lane's, whatever it refused."""
    assert operator_refusal([], []) == Prose(
        "the control comparison yields no mutation, so the table is not the one the lane runs"
    )


def test_a_mutated_control_beside_an_untouched_refusal_set_passes() -> None:
    """The fact holds when the refused constructs yield nothing and the comparison does."""
    assert operator_refusal([], [A_COMPARISON]) is None


def _planted(
    refused: list[MutantNodeText], control: list[MutantNodeText]
) -> Callable[[PythonSource], list[MutantNodeText]]:
    """Answer the gate's two sources with ``refused`` and ``control``, and no other source."""

    def answer(source: PythonSource) -> list[MutantNodeText]:
        return {REFUSED_SOURCE: refused, CONTROL_SOURCE: control}[source]

    return answer


def test_a_table_leaving_the_refused_constructs_alone_passes_silently(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Nothing for the refused source and one comparison is the fact: the check passes silently."""
    monkeypatch.setattr(check_mutmut_operators, "mutations_of", _planted([], [A_COMPARISON]))
    assert check() == ExitStatus(0)
    assert capsys.readouterr().out == ""


def test_a_table_that_cannot_mutate_the_comparison_refuses(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A control the table leaves alone is named as a table that is not the lane's."""
    monkeypatch.setattr(check_mutmut_operators, "mutations_of", _planted([], []))
    assert check() == ExitStatus(1)
    assert capsys.readouterr().out == (
        "check-mutmut-operators: the control comparison yields no mutation,"
        " so the table is not the one the lane runs\n"
    )


def _refusing(missing: ModuleName) -> ModuleType:
    """Fail the import of ``missing`` as a venv without it would; import anything else."""
    raise ImportError(name=missing)


def test_a_venv_without_mutmut_is_no_answer(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without mutmut the gate exits 2 and names the extra that installs it."""

    def importer(name: ModuleName) -> ModuleType:
        if name.split(".", 1)[0] == "mutmut":
            return _refusing(name)
        return importlib.import_module(name)

    monkeypatch.setattr(check_mutmut_operators, "import_module", importer)
    assert check() == ExitStatus(2)
    assert capsys.readouterr().out == f"check-mutmut-operators: {INSTALL_HINT}\n"


def test_an_import_that_fails_for_another_package_is_raised(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An import failing for a module the extra does not install is a defect, raised as it is."""

    def importer(_name: ModuleName) -> ModuleType:
        return _refusing(ModuleName("yaml.loader"))

    monkeypatch.setattr(check_mutmut_operators, "import_module", importer)
    with pytest.raises(ImportError) as raised:
        _ = check()
    assert raised.value.name == "yaml.loader"


def test_a_table_that_mutates_a_refused_construct_refuses(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A mutmut that gained an operator for a refused construct re-opens the record's row."""
    monkeypatch.setattr(
        check_mutmut_operators,
        "mutations_of",
        _planted([MutantNodeText("raise error")], [A_COMPARISON]),
    )
    assert check() == ExitStatus(1)
    assert capsys.readouterr().out == "check-mutmut-operators: mutmut now mutates: raise error\n"


def _out_of_scope(_gate: PinGate, _root: Path) -> bool:
    """Answer that the branch moved nothing a gate rests on."""
    return False


def _never_checked() -> ExitStatus:
    """Fail the test if the gate reaches for mutmut."""
    raise AssertionError


def test_a_branch_moving_nothing_the_fact_rests_on_asks_nothing(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Out of scope, the gate passes without asking mutmut."""

    def the_tree() -> Path:
        return tmp_path

    monkeypatch.setattr(check_mutmut_operators, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mutmut_operators, "gate_runs", _out_of_scope)
    monkeypatch.setattr(check_mutmut_operators, "check", _never_checked)
    monkeypatch.setattr("sys.argv", ["check_mutmut_operators"])
    assert check_mutmut_operators.main() == ExitStatus(0)


def test_in_scope_the_gate_s_verdict_is_the_check_s(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """A branch moving the pin gets the check's own exit status."""

    def the_tree() -> Path:
        return tmp_path

    def in_scope(_gate: PinGate, root: Path) -> bool:
        assert root == tmp_path
        return True

    def refusing() -> ExitStatus:
        return ExitStatus(1)

    monkeypatch.setattr(check_mutmut_operators, "git_toplevel", the_tree)
    monkeypatch.setattr(check_mutmut_operators, "gate_runs", in_scope)
    monkeypatch.setattr(check_mutmut_operators, "check", refusing)
    monkeypatch.setattr("sys.argv", ["check_mutmut_operators"])
    assert check_mutmut_operators.main() == ExitStatus(1)


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_mutmut_operators", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_mutmut_operators.main()
    assert stopped.value.code == 2

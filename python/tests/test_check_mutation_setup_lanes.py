# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_mutation_setup_lanes``: each lane's check refuses what it names.

Each check is pointed at files the test plants, the module's paths
monkeypatched to them, and its diagnostics compared whole; where a diagnostic
quotes PyYAML's own message, the gate's part of it is compared.  An input a
check cannot read stops the gate with exit 2, named on stderr.  The Go and
Rust lanes' skips are held by ``test_check_mutation_setup_go_rust.py``, the
C++ lane's two checks by ``test_check_mutation_setup_cpp_lane.py``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, NewType

import pytest
from _gate_exit import stderr_of_exit_2
from _planted_tree import plant

from tools import check_mutation_setup_lanes
from tools._common import RelPath
from tools.check_mutation_setup_lanes import (
    PYTHON_DOC_HARNESS,
    GremlinsMutator,
)
from tools.mutation_go import GO_CONFIG

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

# The bytes of a file a test plants that is no text.
FileBytes = NewType("FileBytes", bytes)
# A YAML scalar as ``go/.gremlins.yaml`` spells it.
YamlScalar = NewType("YamlScalar", str)


# Every input: a file the gate cannot read or parse stops it with exit 2.


@pytest.mark.parametrize(
    ("contents", "reason"),
    [
        pytest.param(None, Prose("No such file or directory"), id="missing"),
        pytest.param(
            FileBytes(b"\xff\xfe"),
            Prose("'utf-8' codec can't decode byte 0xff in position 0: invalid start byte"),
            id="not UTF-8",
        ),
    ],
)
def test_a_file_the_gate_cannot_read_exits_2(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[Prose],
    contents: FileBytes | None,
    reason: Prose,
) -> None:
    """A file missing, or no UTF-8 text, stops the gate naming it and why."""
    path = tmp_path / "input.txt"
    if contents is not None:
        _ = path.write_bytes(contents)
    assert stderr_of_exit_2(capsys, lambda: check_mutation_setup_lanes.read_or_exit(path)) == (
        f"ERROR: cannot read {path}: {reason}\n"
    )


def test_a_directory_read_as_a_file_exits_2(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A directory where a file is read stops the gate as an unreadable file does."""
    assert stderr_of_exit_2(capsys, lambda: check_mutation_setup_lanes.read_or_exit(tmp_path)) == (
        f"ERROR: cannot read {tmp_path}: Is a directory\n"
    )


def test_a_toml_file_the_gate_cannot_parse_exits_2(
    tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A TOML file that does not parse stops the gate with tomllib's reason."""
    path = plant(tmp_path, {RelPath("pyproject.toml"): Prose("[tool.mutmut\n")}) / "pyproject.toml"
    assert stderr_of_exit_2(capsys, lambda: check_mutation_setup_lanes.toml_or_exit(path)) == (
        f"ERROR: cannot read {path}: Expected ']' at the end of a table declaration "
        + "(at line 1, column 13)\n"
    )


# The Python lane runs no doc-example harness.

_STEPS: Final = Prose(f'STEP = ["pytest", "{PYTHON_DOC_HARNESS}"]\n')
_PYTHON_HARNESS_RUN: Final = Prose(
    f"[python/doc-harness] mutmut runs pytest with {PYTHON_DOC_HARNESS}, so every "
    + "mutant's run collects the documents' fences, which no mutant reaches"
)


def _plant_python_lane(
    root: Path, monkeypatch: pytest.MonkeyPatch, pyproject: Prose, steps: Prose | None = _STEPS
) -> None:
    """Plant the run-ci steps, unless ``None``, and ``pyproject.toml``; point the gate there."""
    files = {RelPath("python/pyproject.toml"): pyproject}
    if steps is not None:
        files[RelPath("tools/_ci_steps.py")] = steps
    _ = plant(root, files)
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", root)
    monkeypatch.setattr(
        check_mutation_setup_lanes, "PYPROJECT_PATH", root / "python" / "pyproject.toml"
    )


def test_a_python_lane_without_the_harness_option_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The arguments mutmut runs pytest with, and ``addopts``, without the option are clean."""
    _plant_python_lane(
        tmp_path,
        monkeypatch,
        Prose(
            '[tool.mutmut]\npytest_add_cli_args = ["--ignore=tests/test_x.py"]\n'
            + 'pytest_add_cli_args_test_selection = ["tests/"]\n'
            + '[tool.pytest.ini_options]\naddopts = ["-ra"]\n'
        ),
    )
    assert not check_mutation_setup_lanes.python_lane_runs_no_doc_harness()


@pytest.mark.parametrize(
    "pyproject",
    [
        pytest.param(
            Prose(f'[tool.mutmut]\npytest_add_cli_args = ["{PYTHON_DOC_HARNESS}"]\n'),
            id="mutmut's arguments",
        ),
        pytest.param(
            Prose(
                f'[tool.mutmut]\npytest_add_cli_args_test_selection = ["{PYTHON_DOC_HARNESS}"]\n'
            ),
            id="mutmut's test selection",
        ),
        pytest.param(
            Prose(
                "[tool.mutmut]\n[tool.pytest.ini_options]\n"
                + f'addopts = ["-ra", "{PYTHON_DOC_HARNESS}"]\n'
            ),
            id="the project's addopts",
        ),
    ],
)
def test_the_harness_option_in_what_mutmut_runs_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, pyproject: Prose
) -> None:
    """The option among mutmut's arguments, its test selection or ``addopts`` is named."""
    _plant_python_lane(tmp_path, monkeypatch, pyproject)
    assert check_mutation_setup_lanes.python_lane_runs_no_doc_harness() == [_PYTHON_HARNESS_RUN]


def test_a_python_harness_spelled_another_way_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A run-ci step no longer passing the option is named, not checked against nothing."""
    _plant_python_lane(
        tmp_path,
        monkeypatch,
        Prose("[tool.mutmut]\n"),
        Prose('STEP = ["pytest", "--markdown-fences"]\n'),
    )
    assert check_mutation_setup_lanes.python_lane_runs_no_doc_harness() == [
        f"[python/doc-harness] tools/_ci_steps.py passes no {PYTHON_DOC_HARNESS}: the "
        + "harness is spelled another way now, and this check would name nothing"
    ]


def test_a_python_lane_without_its_steps_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """With no run-ci steps to find the harness in, the gate stops naming the file."""
    _plant_python_lane(tmp_path, monkeypatch, Prose("[tool.mutmut]\n"), None)
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.python_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / 'tools' / '_ci_steps.py'}: No such file or directory\n"
    )


# The Go lane turns on every mutator gremlins ships off.

# The configuration turning on each kind gremlins ships off, spelled here rather
# than built from the gate's list, so a kind the gate stops holding is one these
# tests still plant; the kinds are its lines naming a block.
_ALL_ON: Final = (
    "mutants:\n"
    + "  invert-assignments:\n    enabled: true\n"
    + "  invert-bitwise:\n    enabled: true\n"
    + "  invert-bwassign:\n    enabled: true\n"
    + "  invert-logical:\n    enabled: true\n"
    + "  invert-loopctrl:\n    enabled: true\n"
    + "  remove-self-assignments:\n    enabled: true\n"
)
_SHIPPED_OFF: Final = tuple(
    GremlinsMutator(line.strip().removesuffix(":")) for line in _ALL_ON.splitlines()[1::2]
)
_LOGICAL_ON: Final = "  invert-logical:\n    enabled: true\n"


def _plant_gremlins_text(root: Path, monkeypatch: pytest.MonkeyPatch, text: Prose) -> None:
    """Plant ``go/.gremlins.yaml`` reading ``text``, and point the gate there."""
    _ = plant(root, {RelPath(GO_CONFIG): text})
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", root)


def _plant_gremlins(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    spelled: Mapping[GremlinsMutator, YamlScalar | None],
) -> None:
    """Plant ``go/.gremlins.yaml``, each kind on unless ``spelled``, and ``None`` with no block."""
    blocks = [
        f"  {name}:\n    enabled: {value}\n"
        for name in _SHIPPED_OFF
        if (value := spelled.get(name, YamlScalar("true"))) is not None
    ]
    _plant_gremlins_text(root, monkeypatch, Prose("mutants:\n" + "".join(blocks)))


def _left_off(name: GremlinsMutator) -> Prose:
    """Return the diagnostic for a default-off kind the file does not turn on."""
    return Prose(
        f"[go/mutators] {GO_CONFIG} does not set `enabled: true` under mutants.{name} in "
        + "the nested form this gate reads; gremlins ships the kind off, and only the "
        + "lane's recorded generated count shows what it made"
    )


def _repeats(key: Prose) -> Prose:
    """Return the diagnostic for a file gremlins drops because a mapping repeats ``key``."""
    return Prose(
        f"[go/mutators] {GO_CONFIG} repeats the key {key!r}, which gremlins' YAML reader "
        + "refuses, so gremlins drops it and every mutator it ships off stays off"
    )


@pytest.mark.parametrize(
    "value",
    [YamlScalar("true"), YamlScalar("True"), YamlScalar("TRUE"), YamlScalar("!!bool true")],
    ids=str,
)
def test_every_default_off_mutator_turned_on_passes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, value: YamlScalar
) -> None:
    """Each spelling gremlins reads as true, YAML 1.2's, turns a kind on."""
    _plant_gremlins(tmp_path, monkeypatch, dict.fromkeys(_SHIPPED_OFF, value))
    assert not check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators()


@pytest.mark.parametrize("name", _SHIPPED_OFF, ids=str)
def test_each_default_off_mutator_left_off_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, name: GremlinsMutator
) -> None:
    """Each kind gremlins ships off is held, and only the one left off is named."""
    _plant_gremlins(tmp_path, monkeypatch, {name: YamlScalar("false")})
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        _left_off(name)
    ]


@pytest.mark.parametrize(
    "value",
    [YamlScalar('"true"'), YamlScalar("yes"), YamlScalar("on"), YamlScalar(""), None],
    ids=str,
)
def test_a_kind_gremlins_reads_as_off_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, value: YamlScalar | None
) -> None:
    """A quoted ``"true"``, a YAML 1.1 ``yes`` or ``on``, a null, or no block leaves a kind off."""
    name = GremlinsMutator("invert-logical")
    _plant_gremlins(tmp_path, monkeypatch, {name: value})
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        _left_off(name)
    ]


@pytest.mark.parametrize(
    "text",
    [
        pytest.param(Prose("unleash:\n  timeout-coefficient: 50\n"), id="no mutants block"),
        pytest.param(Prose(""), id="an empty file"),
        pytest.param(Prose("mutants:\n"), id="a null mutants block"),
        pytest.param(Prose("mutants: [invert-logical]\n"), id="a list of mutants"),
        pytest.param(Prose("- mutants\n"), id="a list at the top"),
    ],
)
def test_a_config_turning_on_nothing_names_every_kind(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, text: Prose
) -> None:
    """A file holding no mapping of mutants leaves every default-off kind off."""
    _plant_gremlins_text(tmp_path, monkeypatch, text)
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        _left_off(name) for name in _SHIPPED_OFF
    ]


def test_a_kind_whose_block_is_no_mapping_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A kind given a scalar rather than its block of settings is left off."""
    _plant_gremlins_text(
        tmp_path,
        monkeypatch,
        Prose(_ALL_ON.replace(_LOGICAL_ON, "  invert-logical: true\n")),
    )
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        _left_off(GremlinsMutator("invert-logical"))
    ]


@pytest.mark.parametrize(
    ("text", "key"),
    [
        pytest.param(Prose(_ALL_ON + _LOGICAL_ON), Prose("invert-logical"), id="a kind repeated"),
        pytest.param(
            Prose(
                _ALL_ON.replace(
                    _LOGICAL_ON, "  invert-logical:\n    enabled: false\n    enabled: true\n"
                )
            ),
            Prose("enabled"),
            id="a switch repeated, the last on",
        ),
        pytest.param(
            Prose(
                "unleash:\n  timeout-coefficient: 50\n"
                + _ALL_ON
                + "unleash:\n  timeout-coefficient: 3\n"
            ),
            Prose("unleash"),
            id="a block repeated at the top",
        ),
    ],
)
def test_a_config_gremlins_refuses_for_a_repeated_key_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, text: Prose, key: Prose
) -> None:
    """A key a mapping holds twice, which PyYAML reads past, is a file gremlins drops."""
    _plant_gremlins_text(tmp_path, monkeypatch, text)
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [_repeats(key)]


@pytest.mark.parametrize(
    ("text", "problem"),
    [
        pytest.param(
            Prose(_ALL_ON.replace(_LOGICAL_ON, "  invert-logical:\n    enabled: !!bool yes\n")),
            Prose("'yes' is no YAML 1.2 boolean"),
            id="a 1.1 boolean tagged",
        ),
        pytest.param(
            Prose(_ALL_ON.replace(_LOGICAL_ON, "  invert-logical:\n    enabled: !!bool tRuE\n")),
            Prose("'tRuE' is no YAML 1.2 boolean"),
            id="a boolean in mixed case tagged",
        ),
        pytest.param(Prose("mutants: [\n"), Prose("expected the node content"), id="no YAML"),
    ],
)
def test_a_config_gremlins_cannot_read_is_named(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, text: Prose, problem: Prose
) -> None:
    """A file gremlins' YAML reader refuses is named with the reader's reason, every kind off.

    The reason is PyYAML's, or the gate's own for a boolean spelled as YAML 1.1 does.
    """
    _plant_gremlins_text(tmp_path, monkeypatch, text)
    diagnostics = check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators()
    assert len(diagnostics) == 1
    assert diagnostics[0].startswith(f"[go/mutators] {GO_CONFIG} is no YAML gremlins reads (")
    assert problem in diagnostics[0]
    assert diagnostics[0].endswith(
        "), so gremlins drops it and every mutator it ships off stays off"
    )


def test_a_key_with_a_capital_is_named(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A capitalised twin, which gremlins reads in place of the lowercase key, is named."""
    _plant_gremlins_text(
        tmp_path, monkeypatch, Prose(_ALL_ON + "  Invert-Logical:\n    enabled: false\n")
    )
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        f"[go/mutators] {GO_CONFIG} holds the key 'Invert-Logical': gremlins reads every key "
        + "lowercased, so a key with a capital stands in for the one this gate reads"
    ]


def test_a_second_document_is_left_unread_as_gremlins_leaves_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Gremlins' reader reads the first document alone, so a second turning a kind off is unread."""
    _plant_gremlins_text(
        tmp_path,
        monkeypatch,
        Prose(f"{_ALL_ON}---\nmutants:\n  invert-logical:\n    enabled: false\n"),
    )
    assert not check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators()


def test_a_dotted_key_is_named_in_the_nested_form_s_words(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A kind switched on through a dotted key, which gremlins resolves and this gate does not."""
    name = GremlinsMutator("invert-logical")
    _plant_gremlins_text(
        tmp_path,
        monkeypatch,
        Prose(f"{_ALL_ON.replace(_LOGICAL_ON, '')}mutants.{name}.enabled: true\n"),
    )
    assert check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators() == [
        _left_off(name)
    ]


@pytest.mark.parametrize(
    ("pyproject", "reason"),
    [
        pytest.param(Prose("tool = 1\n"), Prose("its tool is not a mapping"), id="tool"),
        pytest.param(
            Prose("[tool]\nmutmut = 1\n"), Prose("its tool.mutmut is not a mapping"), id="mutmut"
        ),
        pytest.param(
            Prose("[tool]\npytest = 1\n"), Prose("its tool.pytest is not a mapping"), id="pytest"
        ),
        pytest.param(
            Prose("[tool.pytest]\nini_options = 1\n"),
            Prose("its tool.pytest.ini_options is not a mapping"),
            id="ini_options",
        ),
        pytest.param(
            Prose("[tool.mutmut]\npytest_add_cli_args = [1]\n"),
            Prose("its tool.mutmut.pytest_add_cli_args is not a list of strings"),
            id="an argument no string",
        ),
        pytest.param(
            Prose('[tool.mutmut]\npytest_add_cli_args_test_selection = "tests/"\n'),
            Prose("its tool.mutmut.pytest_add_cli_args_test_selection is not a list of strings"),
            id="the selection one string",
        ),
        pytest.param(
            Prose("[tool.pytest.ini_options]\naddopts = [1]\n"),
            Prose("its tool.pytest.ini_options.addopts is not a list of strings"),
            id="an addopts entry no string",
        ),
    ],
)
def test_a_pyproject_of_another_shape_exits_2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    pyproject: Prose,
    reason: Prose,
) -> None:
    """A ``pyproject.toml`` whose levels are not the mappings and lists the gate reads stops it."""
    _plant_python_lane(tmp_path, monkeypatch, pyproject)
    assert stderr_of_exit_2(capsys, check_mutation_setup_lanes.python_lane_runs_no_doc_harness) == (
        f"ERROR: cannot read {tmp_path / 'python' / 'pyproject.toml'}: {reason}\n"
    )


def test_an_addopts_string_is_split_as_pytest_splits_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Pytest reads ``addopts`` as one string too, and the harness option inside it is found."""
    _plant_python_lane(
        tmp_path,
        monkeypatch,
        Prose(f'[tool.mutmut]\n[tool.pytest.ini_options]\naddopts = "-ra {PYTHON_DOC_HARNESS}"\n'),
    )
    assert check_mutation_setup_lanes.python_lane_runs_no_doc_harness() == [_PYTHON_HARNESS_RUN]


def test_a_missing_gremlins_config_exits_2(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Without ``go/.gremlins.yaml`` the check stops the gate, naming the file."""
    monkeypatch.setattr(check_mutation_setup_lanes, "REPO_ROOT", tmp_path)
    assert stderr_of_exit_2(
        capsys, check_mutation_setup_lanes.go_lane_turns_on_the_default_off_mutators
    ) == (f"ERROR: cannot read {tmp_path / GO_CONFIG}: No such file or directory\n")

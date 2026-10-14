# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ format configuration gate refuses each of its three defects, read off canned dumps.

``tools/check_clang_format_config.py`` reads what the pinned clang-format dumps
from ``cpp/.clang-format`` and from the base style, and refuses a dump that is
not the recorded one, a key that restates the base style, and a key the dump
does not carry.  The dumps here are written out, so each refusal is shown on
the defect it is for without starting the tool; the gate itself runs the tool on
every sweep.
"""

from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

import pytest
from _processes import CommandWord

from tools import check_clang_format_config
from tools.check_clang_format_config import (
    ConfigKey,
    DumpText,
    OptionValue,
    config_refusals,
    digest,
    option_values,
    own_keys,
)

from aletheia.common_types import ExitStatus, Prose

# A base style's dump, and a configuration that changes one option of it and
# restates none.
_BASE = DumpText("---\nLanguage: Cpp\nIndentWidth: 2\nBraceWrapping:\n  AfterClass: false\n...\n")
_EFFECTIVE = DumpText(
    "---\nLanguage: Cpp\nIndentWidth: 4\nBraceWrapping:\n  AfterClass: false\n...\n"
)
_CONFIG = Prose("# a comment\nLanguage: Cpp\nBasedOnStyle: LLVM\nIndentWidth: 4\n")


def _recorded(monkeypatch: pytest.MonkeyPatch, dump: DumpText) -> None:
    """Make ``dump`` the recorded configuration."""
    monkeypatch.setattr(check_clang_format_config, "RECORDED_DIGEST", digest(dump))


def test_an_option_value_carries_its_nested_lines() -> None:
    """A nested option is read whole, so a change inside it moves its value."""
    values = option_values(_BASE)
    assert values[ConfigKey("IndentWidth")] == OptionValue("2")
    assert values[ConfigKey("BraceWrapping")] == OptionValue("\n  AfterClass: false")


def test_the_file_s_keys_are_its_top_level_lines() -> None:
    """Comments and nested lines are not keys the file sets."""
    nested = Prose(_CONFIG + "BraceWrapping:\n  AfterClass: true\n")
    assert own_keys(nested) == [
        ConfigKey("Language"),
        ConfigKey("BasedOnStyle"),
        ConfigKey("IndentWidth"),
        ConfigKey("BraceWrapping"),
    ]


def test_a_configuration_that_decides_every_key_and_is_recorded_passes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The recorded dump of a file whose every key moves a value raises nothing."""
    _recorded(monkeypatch, _EFFECTIVE)
    assert not config_refusals(_CONFIG, _EFFECTIVE, _BASE)


def test_a_dump_other_than_the_recorded_one_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    """A release that moves an option the file leaves to the base style is caught."""
    _recorded(monkeypatch, _BASE)
    refusals = config_refusals(_CONFIG, _EFFECTIVE, _BASE)
    assert len(refusals) == 1
    assert refusals[0].startswith("the effective configuration is not the recorded one")


def test_a_key_restating_the_base_style_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    """A key whose value the base style already gives is named."""
    _recorded(monkeypatch, _EFFECTIVE)
    restating = Prose(_CONFIG + "BraceWrapping:\n  AfterClass: false\n")
    assert config_refusals(restating, _EFFECTIVE, _BASE) == [
        Prose("these keys restate the base style: BraceWrapping")
    ]


def test_the_language_and_the_base_style_are_never_restatements(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``Language`` equals the base style's by necessity, and ``BasedOnStyle`` names it."""
    _recorded(monkeypatch, _BASE)
    config = Prose("Language: Cpp\nBasedOnStyle: LLVM\n")
    assert not config_refusals(config, _BASE, _BASE)


def test_a_key_the_dump_does_not_carry_is_refused(monkeypatch: pytest.MonkeyPatch) -> None:
    """An alias the tool maps to another name is named, and the base-style directive is not."""
    _recorded(monkeypatch, _EFFECTIVE)
    aliased = Prose(_CONFIG + "DerivePointerBinding: false\n")
    assert config_refusals(aliased, _EFFECTIVE, _BASE) == [
        Prose("the tool does not dump these keys under that name: DerivePointerBinding")
    ]


def test_a_venv_without_clang_format_cannot_reach_the_claims(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """With no binary beside the interpreter, the gate exits 2 rather than passing."""
    monkeypatch.setattr(sys, "executable", str(tmp_path / "python"))
    assert check_clang_format_config.check(tmp_path) == 2


@dataclass
class _Dumper:
    """Answers the gate's two dumps as clang-format does, from canned configurations."""

    cpp_dir: Path
    effective: DumpText
    asked: list[list[CommandWord]] = field(default_factory=list)

    def answer(
        self, cmd: list[CommandWord], *, cwd: Path | None = None, check: bool = False
    ) -> subprocess.CompletedProcess[Prose]:
        """Dump the base style when asked for it by name, else the effective configuration."""
        assert cwd == self.cpp_dir
        assert check
        self.asked.append(cmd)
        dumped = _BASE if "--style=LLVM" in cmd else self.effective
        return subprocess.CompletedProcess(cmd, 0, Prose(dumped), Prose(""))


def _venv(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, effective: DumpText) -> _Dumper:
    """Return a stand-in for a venv's clang-format, over a ``cpp/`` holding ``_CONFIG``."""
    bin_dir = tmp_path / "venv" / "bin"
    bin_dir.mkdir(parents=True)
    _ = (bin_dir / "clang-format").write_text("", encoding="utf-8")
    monkeypatch.setattr(sys, "executable", str(bin_dir / "python"))
    cpp_dir = tmp_path / "cpp"
    cpp_dir.mkdir()
    _ = (cpp_dir / ".clang-format").write_text(_CONFIG, encoding="utf-8")
    dumper = _Dumper(cpp_dir, effective)
    monkeypatch.setattr(check_clang_format_config, "run_capture", dumper.answer)
    return dumper


def test_a_recorded_configuration_passes_silently(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The venv's binary dumps the file's configuration and the base style's; nothing is said."""
    _recorded(monkeypatch, _EFFECTIVE)
    dumper = _venv(tmp_path, monkeypatch, _EFFECTIVE)
    assert check_clang_format_config.check(dumper.cpp_dir) == ExitStatus(0)
    binary = CommandWord(str(tmp_path / "venv" / "bin" / "clang-format"))
    assert dumper.asked == [[binary, "--dump-config"], [binary, "--style=LLVM", "--dump-config"]]
    assert capsys.readouterr().out == ""


def test_a_moved_configuration_is_refused_and_printed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A dump other than the recorded one is refused, and the configuration in force is shown."""
    _recorded(monkeypatch, _BASE)
    dumper = _venv(tmp_path, monkeypatch, _EFFECTIVE)
    assert check_clang_format_config.check(dumper.cpp_dir) == ExitStatus(1)
    assert capsys.readouterr().out == (
        "check-clang-format-config: the effective configuration is not the recorded one:"
        + f" recorded {digest(_BASE)}, measured {digest(_EFFECTIVE)}\n"
        + f"the configuration now in force:\n{_EFFECTIVE}\n"
    )


def test_a_restating_file_is_refused_without_the_configuration(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A recorded dump with a restated key names the keys and prints no configuration."""
    _recorded(monkeypatch, _EFFECTIVE)
    dumper = _venv(tmp_path, monkeypatch, _EFFECTIVE)
    _ = (dumper.cpp_dir / ".clang-format").write_text(
        _CONFIG
        + "Language: Cpp\nBraceWrapping:\n  AfterClass: false\nDerivePointerBinding: x\n"
        + "Gone: y\n",
        encoding="utf-8",
    )
    assert check_clang_format_config.check(dumper.cpp_dir) == ExitStatus(1)
    assert capsys.readouterr().out == (
        "check-clang-format-config: these keys restate the base style: BraceWrapping\n"
        + "check-clang-format-config: the tool does not dump these keys under that name:"
        + " DerivePointerBinding Gone\n"
    )


def test_the_refusal_names_every_restated_key(monkeypatch: pytest.MonkeyPatch) -> None:
    """Two restated keys are both named, one space apart."""
    _recorded(monkeypatch, _BASE)
    restating = Prose("IndentWidth: 2\nBraceWrapping:\n  AfterClass: false\n")
    assert config_refusals(restating, _BASE, _BASE) == [
        Prose("these keys restate the base style: IndentWidth BraceWrapping")
    ]


def test_without_a_binary_the_gate_says_where_it_looked(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The refusal names the path it expected and how to fill it."""
    monkeypatch.setattr(sys, "executable", str(tmp_path / "python"))
    assert check_clang_format_config.check(tmp_path) == ExitStatus(2)
    assert capsys.readouterr().out == (
        f"check-clang-format-config: no clang-format at {tmp_path / 'clang-format'};"
        + " install the venv's [dev]\n"
    )


@pytest.mark.parametrize("given", [None, "elsewhere"])
def test_the_gate_holds_the_tree_s_file_unless_told_another(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, given: Prose | None
) -> None:
    """With no option the tree's ``cpp/`` is held; ``--cpp-dir`` names another."""
    held: list[Path] = []

    def the_tree() -> Path:
        return tmp_path

    def holding(cpp_dir: Path) -> ExitStatus:
        held.append(cpp_dir)
        return ExitStatus(1)

    monkeypatch.setattr(check_clang_format_config, "git_toplevel", the_tree)
    monkeypatch.setattr(check_clang_format_config, "check", holding)
    argv = ["check_clang_format_config"] + ([] if given is None else ["--cpp-dir", given])
    monkeypatch.setattr("sys.argv", argv)
    assert check_clang_format_config.main() == ExitStatus(1)
    assert held == [tmp_path / "cpp" if given is None else Path(given)]


def test_the_gate_refuses_an_argument_it_does_not_take(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An argument the gate does not take stops it before it reads anything."""
    monkeypatch.setattr("sys.argv", ["check_clang_format_config", "--unknown"])
    with pytest.raises(SystemExit) as stopped:
        _ = check_clang_format_config.main()
    assert stopped.value.code == 2

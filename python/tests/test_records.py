# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run records live where ``ALETHEIA_CI_OUTPUT`` says, or beside the checkout, never inside it.

``tools._records.records_dir`` is the one reading of the place every tool
writes its run records to: the variable's path when it is set, refused unless
absolute and outside the checkout, since a relative one names a different
directory from each place a tool runs in and one inside would be listed with
the tree, and ``aletheia-ci-output`` beside the checkout when it is unset.
``tools._records.probe_records`` is the folder a checkout's probe runs keep
their record in, ``probes/<the checkout directory's name>`` there, so checkouts
of distinct directory names sharing the place keep apart records.
``python/.venv/bin/python -m tools._records`` prints the place for the checkout
it runs in, ``python/.venv/bin/python -m tools._records probes`` that folder,
and either exits 2 naming why when it cannot, printing nothing a shell would
read as one.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from tools._common import CommandWord, EnvName, EnvValue
from tools._records import UnusableRecordsDirError, main, probe_records, records_dir

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from aletheia.common_types import ExitStatus

# A checkout's root, absolute as every caller's is.
_CHECKOUT = Path("/work/aletheia")


def test_unset_names_the_directory_beside_the_checkout() -> None:
    """With the variable unset the records live in ``aletheia-ci-output`` beside the checkout."""
    assert records_dir(_CHECKOUT, {}) == Path("/work/aletheia-ci-output")


def test_set_names_the_variable_s_path() -> None:
    """An absolute value outside the checkout is the place."""
    environ = {EnvName("ALETHEIA_CI_OUTPUT"): EnvValue("/runner/temp/records")}
    assert records_dir(_CHECKOUT, environ) == Path("/runner/temp/records")


@pytest.mark.parametrize("value", ["records", "./records", "../aletheia-ci-output", ""])
def test_a_relative_value_is_refused_naming_the_variable_and_the_value(value: EnvValue) -> None:
    """A relative value, the empty one included, is refused rather than read against a cwd."""
    with pytest.raises(UnusableRecordsDirError) as refusal:
        _ = records_dir(_CHECKOUT, {EnvName("ALETHEIA_CI_OUTPUT"): value})
    assert "ALETHEIA_CI_OUTPUT" in str(refusal.value)
    assert repr(value) in str(refusal.value)


@pytest.mark.parametrize(
    "value",
    ["/work/aletheia", "/work/aletheia/tools/ci-output", "/work/aletheia/../aletheia/records"],
)
def test_a_value_inside_the_checkout_is_refused_naming_the_variable_the_value_and_the_checkout(
    value: EnvValue,
) -> None:
    """A place in the checkout, the checkout itself included, is refused: the tree would list it."""
    with pytest.raises(UnusableRecordsDirError) as refusal:
        _ = records_dir(_CHECKOUT, {EnvName("ALETHEIA_CI_OUTPUT"): value})
    assert str(refusal.value) == (
        f"ALETHEIA_CI_OUTPUT names {value!r}, inside the checkout /work/aletheia;"
        + " it must name a place outside it"
    )


@pytest.mark.parametrize("value", ["/work/aletheia-ci-output", "/work/aletheia2", "/work"])
def test_a_value_beside_or_above_the_checkout_is_the_place(value: EnvValue) -> None:
    """A place whose path only starts with the checkout's characters, or holds it, is not in it."""
    assert records_dir(_CHECKOUT, {EnvName("ALETHEIA_CI_OUTPUT"): value}) == Path(value)


def test_a_value_reaching_the_checkout_through_a_link_is_refused(tmp_path: Path) -> None:
    """A place outside the checkout by its spelling but inside it through a link is refused."""
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    (tmp_path / "link").symlink_to(checkout)
    with pytest.raises(UnusableRecordsDirError):
        _ = records_dir(
            checkout, {EnvName("ALETHEIA_CI_OUTPUT"): EnvValue(str(tmp_path / "link" / "records"))}
        )


def test_a_checkout_named_through_a_link_refuses_a_value_inside_it(tmp_path: Path) -> None:
    """A checkout named by a link refuses a place inside it spelled by its own path."""
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    (tmp_path / "link").symlink_to(checkout)
    with pytest.raises(UnusableRecordsDirError):
        _ = records_dir(
            tmp_path / "link", {EnvName("ALETHEIA_CI_OUTPUT"): EnvValue(str(checkout / "records"))}
        )


def test_a_checkout_s_probe_records_are_its_own_folder_under_probes() -> None:
    """A checkout's probe records lie in ``probes/<its directory's name>`` in the place by it."""
    assert probe_records(_CHECKOUT, {}) == Path("/work/aletheia-ci-output/probes/aletheia")


def test_checkouts_sharing_the_records_directory_keep_apart_probe_records() -> None:
    """Two checkouts given one records directory get a folder each, named for the checkout."""
    environ = {EnvName("ALETHEIA_CI_OUTPUT"): EnvValue("/runner/temp/records")}
    folders = {probe_records(Path("/work") / name, environ) for name in ("aletheia", "move")}
    assert folders == {
        Path("/runner/temp/records/probes/aletheia"),
        Path("/runner/temp/records/probes/move"),
    }


def test_the_probe_records_of_a_relative_value_are_refused() -> None:
    """A relative value is refused for the probe records as for the records directory."""
    with pytest.raises(UnusableRecordsDirError) as refusal:
        _ = probe_records(_CHECKOUT, {EnvName("ALETHEIA_CI_OUTPUT"): EnvValue("records")})
    assert str(refusal.value) == (
        "ALETHEIA_CI_OUTPUT names 'records', a relative path; it must name an absolute one"
    )


def _run(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
    checkout: Path,
    *words: CommandWord,
) -> tuple[ExitStatus, Prose, Prose]:
    """Run the ``tools._records`` command with ``words`` in ``checkout``: its exit, out and err."""

    def toplevel(_start: Path | None = None) -> Path:
        return checkout

    monkeypatch.setattr("tools._records.git_toplevel", toplevel)
    monkeypatch.setattr(sys, "argv", ["_records", *words])
    status = main()
    out, err = capsys.readouterr()
    return status, Prose(out), Prose(err)


def test_the_command_prints_the_default_beside_its_checkout(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Unset, the command prints the directory beside the checkout it runs in, and exits 0."""
    monkeypatch.delenv("ALETHEIA_CI_OUTPUT", raising=False)
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout")
    assert (status, out, err) == (0, f"{tmp_path / 'aletheia-ci-output'}\n", "")


def test_the_command_prints_the_variable_s_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Set, the command prints the variable's path, and exits 0."""
    monkeypatch.setenv("ALETHEIA_CI_OUTPUT", str(tmp_path / "elsewhere"))
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout")
    assert (status, out, err) == (0, f"{tmp_path / 'elsewhere'}\n", "")


def test_the_command_refuses_a_relative_value_on_stderr(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A relative value exits 2 with the refusal on stderr and nothing on stdout."""
    monkeypatch.setenv("ALETHEIA_CI_OUTPUT", "records")
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout")
    assert (status, out) == (2, "")
    assert err == (
        "records: ALETHEIA_CI_OUTPUT names 'records', a relative path;"
        + " it must name an absolute one\n"
    )


def test_the_command_prints_the_checkout_s_probe_records_beside_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Unset, ``probes`` prints the checkout's folder under the directory beside it, and exits 0."""
    monkeypatch.delenv("ALETHEIA_CI_OUTPUT", raising=False)
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout", CommandWord("probes"))
    assert (status, out, err) == (0, f"{tmp_path / 'aletheia-ci-output/probes/checkout'}\n", "")


def test_the_command_prints_the_checkout_s_probe_records_where_the_variable_says(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Set, ``probes`` prints the checkout's folder under the variable's path, and exits 0."""
    monkeypatch.setenv("ALETHEIA_CI_OUTPUT", str(tmp_path / "elsewhere"))
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout", CommandWord("probes"))
    assert (status, out, err) == (0, f"{tmp_path / 'elsewhere/probes/checkout'}\n", "")


def test_the_command_refuses_the_probe_records_of_a_relative_value_on_stderr(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """``probes`` with a relative value exits 2 with the refusal on stderr, nothing on stdout."""
    monkeypatch.setenv("ALETHEIA_CI_OUTPUT", "records")
    status, out, err = _run(monkeypatch, capsys, tmp_path / "checkout", CommandWord("probes"))
    assert (status, out) == (2, "")
    assert err == (
        "records: ALETHEIA_CI_OUTPUT names 'records', a relative path;"
        + " it must name an absolute one\n"
    )


def test_the_command_refuses_a_value_inside_the_checkout_on_stderr(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A value inside the checkout exits 2 with the refusal on stderr and nothing on stdout."""
    checkout = tmp_path / "checkout"
    monkeypatch.setenv("ALETHEIA_CI_OUTPUT", str(checkout / "records"))
    status, out, err = _run(monkeypatch, capsys, checkout)
    assert (status, out) == (2, "")
    assert err == (
        f"records: ALETHEIA_CI_OUTPUT names {str(checkout / 'records')!r}, inside the checkout"
        + f" {checkout}; it must name a place outside it\n"
    )


def test_the_command_outside_a_checkout_exits_2_saying_so(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """Where git names no checkout the command exits 2 with ``git_toplevel``'s reason on stderr."""

    def no_checkout(start: Path | None = None) -> Path:
        message = f"not inside a git work tree: {start}"
        raise RuntimeError(message)

    monkeypatch.delenv("ALETHEIA_CI_OUTPUT", raising=False)
    monkeypatch.setattr("tools._records.git_toplevel", no_checkout)
    monkeypatch.setattr(sys, "argv", ["_records"])
    assert main() == 2
    out, err = capsys.readouterr()
    assert out == ""
    assert err == f"records: not inside a git work tree: {Path.cwd()}\n"


def test_the_command_says_what_it_does_when_asked(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """``--help`` describes the command and its word and exits 0, asking git nothing."""
    # Wide enough that no line of the help is wrapped.
    monkeypatch.setenv("COLUMNS", "200")
    monkeypatch.setattr(sys, "argv", ["_records", "--help"])
    with pytest.raises(SystemExit) as stop:
        _ = main()
    assert stop.value.code == 0
    out = capsys.readouterr().out
    assert "\nPrint where this checkout's run records live.\n" in out
    assert " probes: print the folder this checkout's probe runs keep their record in\n" in out


def test_the_command_refuses_an_argument_other_than_probes(monkeypatch: pytest.MonkeyPatch) -> None:
    """The command takes only the word probes, so any other exits 2 before git is asked anything."""

    def asked(_start: Path | None = None) -> Path:
        message = "git asked for the checkout"
        raise AssertionError(message)

    monkeypatch.setattr("tools._records.git_toplevel", asked)
    monkeypatch.setattr(sys, "argv", ["_records", "stray"])
    with pytest.raises(SystemExit) as stop:
        _ = main()
    assert stop.value.code == 2

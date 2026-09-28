# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``aletheia template <file>.xlsx``: the spreadsheet route's first step, with no Python.

The subcommand writes the blank workbook ``create_template`` writes. Filled in,
that workbook drives ``aletheia check --excel`` to a verdict, which is the whole
technician route from the command line. Every failure is an operational error,
exit 2 with one ``Error:`` line: a path that exists (left as it was), a parent
directory that does not, one that cannot be written, and an install without the
``[excel]`` extra, which the message names.
"""

from __future__ import annotations

import os
import sys
from typing import TYPE_CHECKING

import pytest
from _cli_check_helpers import report, run_check, skip_without_ffi
from _excel_helpers import ENGINE_RPM_ROW, append_rows, sheet_headers

from aletheia import cli
from aletheia.excel_loader import CHECKS_HEADERS, DBC_HEADERS, WHEN_THEN_HEADERS

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.excel_loader import CellValue

# RPM raw 0x2710 = 10000, times 0.25 = 2500 rpm: under the 8000 limit, so the
# filled-in template's one check passes and the run exits 0.
_LOG = "(0.000000) can0 100#1027000000000000\n"
_RPM_LIMIT_ROW: list[CellValue] = [
    "RPM limit",
    "RPM",
    "never_exceeds",
    "8000",
    None,
    None,
    None,
    "safety",
]


def test_the_template_is_the_workbook_the_loaders_read(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """The file written holds the three sheets, each headed by the columns its loader reads."""
    path = tmp_path / "checks.xlsx"
    assert cli.main(["template", str(path)]) == 0
    assert capsys.readouterr().out == f"Template written to {path}\n"
    assert sheet_headers(path) == {
        "DBC": DBC_HEADERS,
        "Checks": CHECKS_HEADERS,
        "When-Then": WHEN_THEN_HEADERS,
    }


def test_the_filled_in_template_runs_its_checks(tmp_path: Path) -> None:
    """One signal and one check typed into the written template run to a passing verdict."""
    skip_without_ffi()
    workbook = tmp_path / "checks.xlsx"
    assert cli.main(["template", str(workbook)]) == 0
    append_rows(workbook, "DBC", [ENGINE_RPM_ROW])
    append_rows(workbook, "Checks", [_RPM_LIMIT_ROW])
    log_path = tmp_path / "drive.log"
    log_path.write_text(_LOG, encoding="utf-8")

    result = run_check(["--excel", str(workbook), str(log_path)])
    assert result.returncode == 0, report(result)
    assert "1 checks" in result.stdout, report(result)


def test_an_existing_path_is_refused_and_left_as_it_was(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A path that exists exits 2 naming it, and its bytes are not touched."""
    path = tmp_path / "checks.xlsx"
    path.write_bytes(b"not a workbook")
    assert cli.main(["template", str(path)]) == 2
    assert capsys.readouterr().err == f"Error: File already exists: {path}\n"
    assert path.read_bytes() == b"not a workbook"


def test_a_missing_parent_directory_exits_two(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A path under a directory that does not exist is an operational error."""
    path = tmp_path / "missing" / "checks.xlsx"
    assert cli.main(["template", str(path)]) == 2
    assert capsys.readouterr().err.startswith("Error: ")
    assert not path.parent.exists()


@pytest.mark.skipif(os.geteuid() == 0, reason="root writes through a read-only mode")
def test_a_directory_that_cannot_be_written_exits_two(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """A parent the user may not write into is an operational error, not a traceback."""
    parent = tmp_path / "read-only"
    parent.mkdir(mode=0o500)
    try:
        assert cli.main(["template", str(parent / "checks.xlsx")]) == 2
        assert "Permission denied" in capsys.readouterr().err
        assert not any(parent.iterdir())
    finally:
        parent.chmod(0o700)


def test_an_install_without_the_excel_extra_names_it(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """With openpyxl absent the command exits 2 and says which extra installs it."""
    monkeypatch.setitem(sys.modules, "openpyxl", None)
    monkeypatch.delitem(sys.modules, "aletheia.excel_loader")
    path = tmp_path / "checks.xlsx"
    assert cli.main(["template", str(path)]) == 2
    assert capsys.readouterr().err == (
        "Error: openpyxl is not installed; install it with pip install 'aletheia[excel]'\n"
    )
    assert not path.exists()


@pytest.mark.parametrize(
    ("module", "error"),
    [
        ("can", "python-can is not installed; install it with pip install 'aletheia[can]'"),
        ("openpyxl", "openpyxl is not installed; install it with pip install 'aletheia[excel]'"),
        ("yaml", "PyYAML is not installed; install it with pip install 'aletheia[yaml]'"),
    ],
)
def test_each_optional_extra_is_named_by_its_install(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    module: str,
    error: str,
) -> None:
    """A missing optional module, or one of its submodules, names the extra that installs it."""

    def missing(_path: str | Path) -> None:
        raise ImportError(name=f"{module}.sub")

    monkeypatch.setattr(cli, "_lazy_create_template", lambda: missing)
    assert cli.main(["template", str(tmp_path / "checks.xlsx")]) == 2
    assert capsys.readouterr().err == f"Error: {error}\n"


def test_an_import_error_from_anything_else_is_not_swallowed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """An import that fails for a module no extra provides is a defect, raised as it is."""

    def broken(_path: str | Path) -> None:
        raise ImportError(name="aletheia.not_an_extra")

    monkeypatch.setattr(cli, "_lazy_create_template", lambda: broken)
    with pytest.raises(ImportError) as raised:
        cli.main(["template", str(tmp_path / "checks.xlsx")])
    assert raised.value.name == "aletheia.not_an_extra"

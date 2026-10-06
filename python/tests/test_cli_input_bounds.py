# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A DBC past one of the kernel's bounds stops the CLI with its path in front of the kernel's words.

``aletheia validate`` loads a DBC through the kernel by one of two routes: a
``.dbc`` text through ``parse_dbc_text``, a workbook's assembled DBC through
``parse_dbc``.  On either, a DBC past a bound exits with code 2 and one line,
worded as every other failure to parse a DBC file is: ``Failed to parse DBC
file '<path>':`` and then the kernel's message, which names the command, the
field, the observed value and the limit.
"""

from __future__ import annotations

import contextlib
import io
from typing import TYPE_CHECKING, Literal, NamedTuple

from _dbc_helpers import dbc, message, signal

from aletheia import limits
from aletheia.cli import main
from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

    from aletheia.types import DBCDefinition


class _Run(NamedTuple):
    """What ``aletheia validate`` answered: its exit status, and what it wrote to stderr."""

    status: ExitStatus
    stderr: Prose


def _validate(flag: Literal["--dbc", "--excel"], path: Path) -> _Run:
    """Run ``aletheia validate`` on the DBC source ``flag`` names."""
    printed = io.StringIO()
    with contextlib.redirect_stderr(printed):
        status = ExitStatus(main(["validate", flag, str(path)]))
    return _Run(status, Prose(printed.getvalue()))


def test_a_text_past_a_bound_names_its_path(tmp_path: Path) -> None:
    """A ``.dbc`` text whose version is one character past its bound, through ``parse_dbc_text``."""
    limit = limits.MAX_STRING_LENGTH_CHARACTERS
    path = tmp_path / "long_version.dbc"
    version = "z" * (limit + 1)
    path.write_text(
        f'VERSION "{version}"\nNS_:\nBS_:\nBU_: ECU\nBO_ 100 M: 8 ECU\n', encoding="utf-8"
    )
    kernel = f"ParseDBCText: version string: string length {limit + 1} exceeds limit {limit}"
    assert _validate("--dbc", path) == (2, f"Error: Failed to parse DBC file '{path}': {kernel}\n")


def test_a_workbook_past_a_bound_names_its_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A workbook's DBC whose version is one character past its bound, through ``parse_dbc``.

    The workbook loader stands in for one whose DBC carries a version longer
    than a spreadsheet cell can hold.
    """
    limit = limits.MAX_STRING_LENGTH_CHARACTERS
    over = dbc([message(256, "M", [signal("S")])], version="z" * (limit + 1))

    def load(_path: Path) -> DBCDefinition:
        """Read any workbook as the DBC past the bound."""
        return over

    monkeypatch.setattr("aletheia.cli._lazy_load_dbc_from_excel", lambda: load)
    path = tmp_path / "long_version.xlsx"
    path.write_bytes(b"")
    kernel = f"ParseDBC: version string: string length {limit + 1} exceeds limit {limit}"
    assert _validate("--excel", path) == (
        2,
        f"Error: Failed to parse DBC file '{path}': {kernel}\n",
    )

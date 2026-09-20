# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The ratchet record is read whole or refused by name, and a pasted row reads back.

A record that cannot be read is a gate that cannot run, so every malformed
row comes back as the reason, never as a traceback or as a row keyed on an
empty string; and the row a diagnostic prints for pasting is the row the
record then reads, backslashes and quotes included.
"""

from __future__ import annotations

from pathlib import Path
from typing import NamedTuple

import pytest
import yaml

from tools._common import RelPath
from tools._ratchet import CanonicalText, RowKey, as_row, read_ratchet_rows


class _Record(NamedTuple):
    """A record written for one test: the repository root it sits under, and its path there."""

    repo: Path
    path: Path


def _record(tmp_path: Path, body: str) -> _Record:
    """Write a record under ``tmp_path``, which stands for the repository root."""
    path = Path("record.yaml")
    (tmp_path / path).write_text(body, encoding="utf-8")
    return _Record(tmp_path, path)


def test_identical_rows_add_their_counts(tmp_path: Path) -> None:
    """Two rows naming one thing are one key carrying both counts."""
    rows = "  - {file: a.cpp, text: 'for (;;)', count: 2}\n  - {file: a.cpp, text: 'for (;;)'}\n"
    repo, record = _record(tmp_path, f"loops:\n{rows}")
    expected = {RowKey(RelPath("a.cpp"), CanonicalText("for (;;)")): 3}
    assert read_ratchet_rows(repo, record, "loops") == expected


@pytest.mark.parametrize(
    ("body", "named"),
    [
        ("loops:\n  - {file: a.cpp, text: t, count: abc}\n", "count"),
        ("loops:\n  - {file: a.cpp, text: t, count: 0}\n", "count"),
        ("loops:\n  - {file: a.cpp, text: t, count: true}\n", "count"),
        ("loops:\n  - {text: t, count: 1}\n", "file"),
        ("loops:\n  - {file: a.cpp, count: 1}\n", "text"),
    ],
)
def test_a_malformed_row_is_refused_by_name(tmp_path: Path, body: str, named: str) -> None:
    """The reason names the field that could not be read."""
    repo, record = _record(tmp_path, body)
    result = read_ratchet_rows(repo, record, "loops")
    assert isinstance(result, str)
    assert named in result


@pytest.mark.parametrize(
    "text",
    [
        "while (i < n && text[i] != '\\n')",
        'const auto s = std::string{"quoted"};',
        "for (std::size_t i = 0; i < n; ++i)",
    ],
)
def test_a_pasted_row_reads_back_as_the_text_it_names(text: str) -> None:
    """The row a diagnostic prints is the row the record then reads."""
    document = yaml.safe_load("rows:\n" + as_row(RelPath("a.cpp"), CanonicalText(text), 1))
    assert document == {"rows": [{"file": "a.cpp", "text": text, "count": 1}]}

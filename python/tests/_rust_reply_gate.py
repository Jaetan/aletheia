# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate run over the Rust crate with one text of a file planted.

A Rust gate test writes a file's code as its case writes it and reads what the
gate then reports: each line the grammar cannot parse, each set the Rust reader
cannot read and each line comparing a word outside the functions it reads, or
else each divergence from ``replyText``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    ReplyPlace,
    check_reply_places,
    read_reply_tables,
)
from tools._reply_places_rust import RUST_RESPONSE, RustLine, RustText, rust_reader

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest

# How the gate ends its report of a line the grammar cannot parse.
UNPARSED = Prose("is not Rust tree-sitter-rust parses")


def planted_in(
    monkeypatch: pytest.MonkeyPatch, path: Path, written: RustText, planted: RustText
) -> list[Prose]:
    """Return what the gate reports with ``written``, standing once in ``path``, planted.

    The crate's other files are read as they stand.
    """
    source = path.read_text(encoding="utf-8")
    assert source.count(written) == 1
    text = RustText(source.replace(written, planted))

    def read(read_path: Path) -> RustText:
        return text if read_path == path else RustText(read_path.read_text(encoding="utf-8"))

    monkeypatch.setattr("tools._reply_places_rust._rust_source", read)
    agda = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    tables = read_reply_tables(agda, (rust_reader(frozenset()),))
    return tables if isinstance(tables, list) else check_reply_places(tables, frozenset())


def unparsed(found: list[Prose]) -> list[Prose]:
    """Return each report of a line tree-sitter-rust cannot parse."""
    return [each for each in found if each.endswith(UNPARSED)]


def at_place(found: list[Prose], place: ReplyPlace) -> list[Prose]:
    """Return, sorted, what the gate names at ``place``, its lead cut."""
    lead = f"reply place {place}: "
    return sorted(Prose(each.removeprefix(lead)) for each in found if each.startswith(lead))


def named_at(
    monkeypatch: pytest.MonkeyPatch,
    plant: tuple[RustText, RustText],
    place: ReplyPlace,
    path: Path = RUST_RESPONSE,
) -> list[Prose]:
    """Return, sorted, what the gate names at ``place`` with ``plant`` planted in ``path``.

    ``plant`` is a text standing once in the file and what it is planted as,
    which leaves the file Rust the grammar parses, so no case reads a tree the
    grammar recovered from.
    """
    found = planted_in(monkeypatch, path, *plant)
    assert unparsed(found) == []
    return at_place(found, place)


def line_of(path: Path, text: RustText) -> RustLine:
    """Return the number of the one line of ``path`` that ``text`` opens, stripped."""
    lines = path.read_text(encoding="utf-8").split("\n")
    found = [RustLine(n) for n, line in enumerate(lines, start=1) if line.strip().startswith(text)]
    assert len(found) == 1, found
    return found[0]

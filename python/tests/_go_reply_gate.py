# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate run over the Go package with one text of a reader file planted.

A Go gate test writes a reader's code as its case writes it and reads what the
gate then reports: each line the grammar cannot parse, each set the Go reader
cannot read and each line comparing a word outside the lines it reads, or else
each divergence from ``replyText``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    GoText,
    ReplyPlace,
    check_reply_places,
    read_reply_tables,
)
from tools._reply_places_go import GO_RESPONSE, go_reader

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


def reported(
    monkeypatch: pytest.MonkeyPatch, path: Path, written: GoText, planted: GoText
) -> list[Prose]:
    """Return what the gate reports with ``written`` planted as ``planted`` in ``path``.

    ``written`` stands once in the file; the package's other files are read as
    they stand.
    """
    source = path.read_text(encoding="utf-8")
    assert source.count(written) == 1
    text = GoText(source.replace(written, planted))

    def source_of(read: Path) -> GoText:
        return text if read == path else GoText(read.read_text(encoding="utf-8"))

    monkeypatch.setattr("tools._reply_places_go._go_source", source_of)
    tables = read_reply_tables(
        AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8")), (go_reader(frozenset()),)
    )
    return tables if isinstance(tables, list) else check_reply_places(tables, frozenset())


# How the gate ends its report of a line the grammar cannot parse.
UNPARSED = Prose("is not Go tree-sitter-go parses")


def unparsed(found: list[Prose]) -> list[Prose]:
    """Return each report of a line tree-sitter-go cannot parse."""
    return [each for each in found if each.endswith(UNPARSED)]


def named_in(
    monkeypatch: pytest.MonkeyPatch,
    path: Path,
    plant: tuple[GoText, GoText],
    place: ReplyPlace,
) -> list[Prose]:
    """Return, sorted, what the gate names at ``place`` with ``plant`` planted in ``path``.

    ``plant`` is a text standing once in the file and what it is planted as,
    which leaves the file Go the grammar parses, so no case reads a tree the
    grammar recovered from.
    """
    lead = f"reply place {place}: "
    found = reported(monkeypatch, path, *plant)
    assert unparsed(found) == []
    return sorted(Prose(each.removeprefix(lead)) for each in found if each.startswith(lead))


def named_at(
    monkeypatch: pytest.MonkeyPatch, written: GoText, planted: GoText, place: ReplyPlace
) -> list[Prose]:
    """Return, sorted, what the gate names at ``place`` with ``written`` planted as ``planted``.

    ``written`` stands once in the Go responses.
    """
    return named_in(monkeypatch, GO_RESPONSE, (written, planted), place)

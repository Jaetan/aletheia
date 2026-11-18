# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate refuses a ``replyText`` word that is not identifier-shaped.

The Go and Rust readers' word comparisons are told from the rest of a reader
file by their literal's shape, which every word ``replyText`` writes has, so the
gate holds the table to it: a word of another shape is named with its place,
read through the gate's own parser of the reply proof.
"""

from __future__ import annotations

import pytest

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    BindingReader,
    ReaderSets,
    ReplyTables,
    ReplyWord,
    read_reply_tables,
)

from aletheia.common_types import Prose

# The row whose last word each case rewrites, as the reply proof writes it.
_BYTE_ORDER = '("little_endian" ∷ "big_endian" ∷ [])'
_PLACE = "dbc/messages/signals/byteOrder"


def test_the_reply_proof_as_written_holds_identifier_shaped_words() -> None:
    """Every word of ``replyText`` has the shape the readers' comparisons are read by."""
    tables = read_reply_tables(AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8")), ())
    assert isinstance(tables, ReplyTables), tables


def _reader(name: Prose) -> BindingReader:
    """Stand in a binding's reader that reads nothing and names itself."""

    def read(_unread: list[Prose]) -> ReaderSets:
        return ReaderSets(name, Prose("table"), {}, {})

    return read


def test_each_binding_read_is_reported_as_it_is_read(capsys: pytest.CaptureFixture[Prose]) -> None:
    """Reading the tables reports on stderr before the first binding and as each one is read."""
    text = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    tables = read_reply_tables(text, (_reader(Prose("go")), _reader(Prose("rust"))))
    assert isinstance(tables, ReplyTables), tables
    assert capsys.readouterr().err == (
        "progress: 0/2 bindings read\nprogress: 1/2 bindings read\nprogress: 2/2 bindings read\n"
    )


@pytest.mark.parametrize(
    "word",
    [
        pytest.param(ReplyWord("big-endian"), id="a dash"),
        pytest.param(ReplyWord(""), id="the empty text"),
        pytest.param(ReplyWord("2nd"), id="a digit first"),
        pytest.param(ReplyWord("big endian"), id="a space"),
    ],
)
def test_a_word_of_another_shape_is_refused_with_its_place(word: ReplyWord) -> None:
    """A ``replyText`` word that is not identifier-shaped is named, the rest of the row read."""
    text = AGDA_REPLY_RANGE.read_text(encoding="utf-8")
    assert text.count(_BYTE_ORDER) == 1
    planted = AgdaText(text.replace(_BYTE_ORDER, f'("little_endian" ∷ "{word}" ∷ [])'))
    assert read_reply_tables(planted, ()) == [
        Prose(
            f"replyText row {_PLACE}: '{word}' does not match "
            + "[A-Za-z_][A-Za-z0-9_]*, a reply word's shape"
        )
    ]

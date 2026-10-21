# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
r"""A DBC is held to the DBC character set, its names to the identifier rules, on both load routes.

A string holds printable ASCII but ``"`` and ``\\``, plus TAB, LF and CR; a name is an
ASCII C identifier, not a DBC keyword, at most 128 characters, decided as it is read, and
refused with its code where it starts; a DBC text is scanned for its character set before it
is parsed.  Every row is the kernel's reply to one command.
"""

from __future__ import annotations

import json
from typing import Final, Literal, NamedTuple, NewType

import pytest
from _dbc_helpers import dbc, message, signal
from _kernel_rows import (
    CodePoint,
    Column,
    Command,
    FieldName,
    Index,
    KernelMessage,
    Keyword,
    Line,
    Located,
    NameLength,
    kernel_reply,
    refusal,
)

from aletheia.codes import ErrorCode
from aletheia.common_types import Prose
from aletheia.types import DBCDefinition, dump_json

# A DBC text, as a file holds it.
DBCText = NewType("DBCText", str)
# The text whose first character a position names.
Marker = NewType("Marker", str)
# A text written into a signal's name or unit.
EditedText = NewType("EditedText", str)


class TextRefusal(NamedTuple):
    """One DBC text and the kernel's refusal of it."""

    label: Prose
    text: DBCText
    code: ErrorCode
    message: KernelMessage
    located: Located


class SignalEdit(NamedTuple):
    """A text written into the base DBC's one signal."""

    key: Literal["name", "unit"]
    value: EditedText


class JSONRefusal(NamedTuple):
    """One edit of the base DBC and the kernel's refusal of the edited DBC."""

    label: Prose
    edit: SignalEdit
    code: ErrorCode
    message: KernelMessage
    located: Located


_BASE_TEXT: Final = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: N\n\nBO_ 1 M: 8 N\n SG_ S : 0|8@1+ (1,0) [0|1] "u" N\n\n'
)
_BASE: Final = DBCText(_BASE_TEXT)
_OUTSIDE: Final = "is outside the DBC character set"


def _at(text: DBCText, marker: Marker) -> tuple[Line, Column]:
    """Locate the first character of ``marker`` in ``text``: its line and column, counted from 1."""
    index = text.index(marker)
    return Line(text.count("\n", 0, index) + 1), Column(index - text.rfind("\n", 0, index))


def _keyword_row(label: Prose, text: DBCText, keyword: Keyword, marker: Marker) -> TextRefusal:
    """Build the text route's refusal of ``keyword`` used as a name, located where it starts.

    ``marker`` is the text from the name on, unique in ``text``: the keyword alone
    may occur earlier as the keyword of a line.
    """
    assert marker.startswith(keyword), (keyword, marker)
    assert text.count(marker) == 1, (keyword, marker)
    line, column = _at(text, marker)
    return TextRefusal(
        label,
        text,
        ErrorCode.DBC_KEYWORD_NAME,
        KernelMessage(
            f"ParseDBCText: identifier '{keyword}' at line {line}, column {column} is a DBC keyword"
        ),
        {"line": line, "column": column, "keyword": keyword},
    )


def _scan_row() -> TextRefusal:
    text = DBCText(_BASE_TEXT + 'CM_ "café";\n')
    line, column = _at(text, Marker("é"))
    return TextRefusal(
        Prose("a non-ASCII character in a comment, found by the scan"),
        text,
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            f"ParseDBCText: character at line {line}, column {column} (code point 233) " + _OUTSIDE
        ),
        {"line": line, "column": column, "code_point": CodePoint(233)},
    )


def _digit_led_row() -> TextRefusal:
    """Build the refusal of a digit-led word where a name stands, located where it starts."""
    text = DBCText(_BASE_TEXT.replace(" SG_ S :", " SG_ 1S :"))
    line, column = _at(text, Marker("1S :"))
    return TextRefusal(
        Prose("a signal name starting with a digit"),
        text,
        ErrorCode.PARSE_INVALID_IDENTIFIER,
        KernelMessage(
            f"ParseDBCText: identifier at line {line}, column {column}: '1S' is not a valid DBC "
            + "identifier (must start with letter or '_', followed by alphanumerics or '_')"
        ),
        {"line": line, "column": column},
    )


def _long_name_row() -> TextRefusal:
    long_name = "S" * 129
    text = DBCText(_BASE_TEXT.replace(" SG_ S :", f" SG_ {long_name} :"))
    line, column = _at(text, Marker(long_name))
    return TextRefusal(
        Prose("a signal name of 129 characters"),
        text,
        ErrorCode.INPUT_BOUND_EXCEEDED,
        KernelMessage(
            f"ParseDBCText: identifier at line {line}, column {column}: "
            + "identifier length 129 exceeds limit 128"
        ),
        {
            "line": line,
            "column": column,
            "bound_kind": "identifier_length",
            "observed": NameLength(129),
            "limit": NameLength(128),
        },
    )


def _bad_attribute_row() -> TextRefusal:
    text = DBCText(_BASE_TEXT + 'BA_DEF_ SG_ "1abc" INT 0 1;\n')
    line, column = _at(text, Marker("1abc"))
    return TextRefusal(
        Prose("an attribute name that is not an identifier"),
        text,
        ErrorCode.PARSE_INVALID_IDENTIFIER,
        KernelMessage(
            f"ParseDBCText: identifier at line {line}, column {column}: '1abc' is not a valid DBC "
            + "identifier (must start with letter or '_', followed by alphanumerics or '_')"
        ),
        {"line": line, "column": column},
    )


_REFUSED_TEXTS: Final = (
    _scan_row(),
    TextRefusal(
        Prose("a doubled quote, which the grammar reads as one quote"),
        DBCText(_BASE_TEXT + 'CM_ "a""b";\n'),
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            f"ParseDBCText: comment text: character at index 1 (code point 34) {_OUTSIDE}"
        ),
        {"field": FieldName("comment text"), "index": Index(1), "code_point": CodePoint(34)},
    ),
    _keyword_row(
        Prose("a keyword as a signal name"),
        DBCText(_BASE_TEXT.replace(" SG_ S :", " SG_ BO_ :")),
        Keyword("BO_"),
        Marker("BO_ :"),
    ),
    _long_name_row(),
    _digit_led_row(),
    _keyword_row(
        Prose("a keyword as the multiplexed signal of an SG_MUL_VAL_ line"),
        DBCText(_BASE_TEXT + "SG_MUL_VAL_ 1 CM_ S 0-0;\n"),
        Keyword("CM_"),
        Marker("CM_ S 0-0"),
    ),
    _keyword_row(
        Prose("a keyword as the signal of a SIG_VALTYPE_ line"),
        DBCText(_BASE_TEXT + "SIG_VALTYPE_ 1 VAL_ : 1;\n"),
        Keyword("VAL_"),
        Marker("VAL_ :"),
    ),
    _keyword_row(
        Prose("a keyword as a sender of a BO_TX_BU_ line naming no message"),
        DBCText(_BASE_TEXT + "BO_TX_BU_ 99 : CM_;\n"),
        Keyword("CM_"),
        Marker("CM_;"),
    ),
    _bad_attribute_row(),
    _keyword_row(
        Prose("a keyword as an attribute name"),
        DBCText(_BASE_TEXT + 'BA_DEF_ SG_ "CM_" INT 0 1;\n'),
        Keyword("CM_"),
        Marker('CM_" INT'),
    ),
)

_REFUSED_EDITS: Final = (
    JSONRefusal(
        Prose("a non-ASCII character in a signal name"),
        SignalEdit("name", EditedText("S€")),
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            "ParseDBC: message 'M', signal 'S€': signal name: character at index 1 "
            + f"(code point 8364) {_OUTSIDE}"
        ),
        {"field": FieldName("signal name"), "index": Index(1), "code_point": CodePoint(8364)},
    ),
    JSONRefusal(
        Prose("a keyword as a signal name"),
        SignalEdit("name", EditedText("BO_")),
        ErrorCode.DBC_KEYWORD_NAME,
        KernelMessage("ParseDBC: message 'M', signal 'BO_': signal name: 'BO_' is a DBC keyword"),
        {"field": FieldName("signal name"), "keyword": Keyword("BO_")},
    ),
    JSONRefusal(
        Prose("a signal name starting with a digit"),
        SignalEdit("name", EditedText("1S")),
        ErrorCode.PARSE_INVALID_IDENTIFIER,
        KernelMessage(
            "ParseDBC: message 'M', signal '1S': signal name: '1S' is not a valid DBC "
            + "identifier (must start with letter or '_', followed by alphanumerics or '_')"
        ),
        {"field": FieldName("signal name")},
    ),
    JSONRefusal(
        Prose("a signal name of 129 characters"),
        SignalEdit("name", EditedText("S" * 129)),
        ErrorCode.INPUT_BOUND_EXCEEDED,
        KernelMessage(
            f"ParseDBC: message 'M', signal '{'S' * 129}': signal name: "
            + "identifier length 129 exceeds limit 128"
        ),
        {
            "field": FieldName("signal name"),
            "bound_kind": "identifier_length",
            "observed": NameLength(129),
            "limit": NameLength(128),
        },
    ),
    JSONRefusal(
        Prose("a quote in a unit"),
        SignalEdit("unit", EditedText('a"b')),
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            f"ParseDBC: signal text field: character at index 1 (code point 34) {_OUTSIDE}"
        ),
        {"field": FieldName("signal text field"), "index": Index(1), "code_point": CodePoint(34)},
    ),
    JSONRefusal(
        Prose("a backspace in a unit"),
        SignalEdit("unit", EditedText("a\bb")),
        ErrorCode.DBC_INVALID_CHARACTER,
        KernelMessage(
            f"ParseDBC: signal text field: character at index 1 (code point 8) {_OUTSIDE}"
        ),
        {"field": FieldName("signal text field"), "index": Index(1), "code_point": CodePoint(8)},
    ),
)


def _text_command(text: DBCText) -> Command:
    return Command(
        json.dumps({"type": "command", "command": "parseDBCText", "text": text}).encode()
    )


def _edited_command(edit: SignalEdit) -> Command:
    """Build the base DBC, one signal of one message, with ``edit`` written into the signal."""
    definition: DBCDefinition = dbc([message(1, "M", [signal("S", unit="u")])])
    definition["messages"][0]["signals"][0][edit.key] = edit.value
    return Command(
        dump_json({"type": "command", "command": "parseDBC", "dbc": definition}).encode()
    )


@pytest.mark.parametrize("row", _REFUSED_TEXTS, ids=[row.label for row in _REFUSED_TEXTS])
def test_a_text_outside_the_character_set_or_naming_a_keyword_is_refused(row: TextRefusal) -> None:
    """The text route refuses the character, the keyword or the length, each located."""
    assert kernel_reply(_text_command(row.text)) == refusal(row.code, row.message, row.located)


@pytest.mark.parametrize("row", _REFUSED_EDITS, ids=[row.label for row in _REFUSED_EDITS])
def test_a_dbc_outside_the_character_set_or_naming_a_keyword_is_refused(row: JSONRefusal) -> None:
    """The JSON route refuses the same character, keyword and length, naming the field."""
    assert kernel_reply(_edited_command(row.edit)) == refusal(row.code, row.message, row.located)

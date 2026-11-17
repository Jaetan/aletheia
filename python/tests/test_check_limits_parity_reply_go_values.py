# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads the Go status place from the one block of its values.

``replyStatus`` is a struct of one string field, ``word``, whose values the Go
responses declare in one ``var`` block: the words of that block are the Go
reader's set at ``status``.  A value given its word anywhere else could hold a
word the block does not, so a line of the package building one outside the
block, converting a value to the type, aliasing it, constraining a type
parameter to it, declaring an unnamed struct of its one field, or reaching that
field outside ``fieldStatus`` is named at the place where it stands, as is a
block or a declaration the gate cannot read.
"""

from __future__ import annotations

import pytest
from _go_reply_gate import named_at

from tools._reply_places import GoLine, GoText, ReplyPlace
from tools._reply_places_go import GO_RESPONSE

from aletheia.common_types import Prose

_STATUS = ReplyPlace("status")
_WHERE = "go/aletheia/json_response.go"
# The function the stray code stands before, which reads no status.
_ANCHOR = GoText("func readTimestamp(")
_ACK = GoText('statusAck        = replyStatus{"ack"}')
_ERROR = GoText('\tstatusError      = replyStatus{"error"}\n')
_DECLARATION = GoText("type replyStatus struct{ word string }")
_BUILDS = Prose("builds a replyStatus outside its block")
_CONVERTS = Prose("converts a value to replyStatus")


def _line_of(text: GoText) -> GoLine:
    """Return the number of the one line of the Go responses ``text`` opens, stripped."""
    lines = GO_RESPONSE.read_text(encoding="utf-8").split("\n")
    found = [GoLine(n) for n, line in enumerate(lines, start=1) if line.strip().startswith(text)]
    assert len(found) == 1, found
    return found[0]


# Each case: the text it plants over, the plant, and what the gate names at the place.
_READ = [
    pytest.param(_ANCHOR, _ANCHOR, [], id="status as the block writes it"),
    pytest.param(
        GoText(f"\t{_ACK}\n"),
        GoText(""),
        [Prose("'ack' is in replyText only")],
        id="a value dropped",
    ),
    pytest.param(
        _ERROR,
        GoText(_ERROR + '\tstatusBogus = replyStatus{"bogus"}\n'),
        [Prose("'bogus' is in the Go reader only")],
        id="a value added",
    ),
    pytest.param(
        _DECLARATION,
        GoText("type replyStatus struct{ word, other string }"),
        [Prose(f"{_WHERE}:replyStatus is not declared once as {_DECLARATION!r}")],
        id="a declaration of two fields",
    ),
    pytest.param(
        _DECLARATION,
        GoText('type replyStatus struct{ word string `json:"word"` }'),
        [Prose(f"{_WHERE}:replyStatus is not declared once as {_DECLARATION!r}")],
        id="a declaration whose field carries a tag",
    ),
    pytest.param(
        _ANCHOR,
        GoText(f'var (\n\tstatusOther = replyStatus{{"other"}}\n)\n\n{_ANCHOR}'),
        [Prose(f"{_WHERE}:replyStatus: 2 var blocks declare its values, not one")],
        id="a second block",
    ),
    pytest.param(
        _ANCHOR,
        GoText(f"var (\n\tstrayCount = 1\n)\n\n{_ANCHOR}"),
        [],
        id="a block of other values",
    ),
]


@pytest.mark.parametrize(("written", "planted", "named"), _READ)
def test_the_gate_reads_the_status_words_from_their_one_block(
    monkeypatch: pytest.MonkeyPatch, written: GoText, planted: GoText, named: list[Prose]
) -> None:
    """With ``written`` planted as ``planted``, the gate names ``named`` at the status place."""
    assert named_at(monkeypatch, written, planted, _STATUS) == named


@pytest.mark.parametrize(
    "value",
    [
        pytest.param(GoText('statusAck        = replyStatus{word: "ack"}'), id="a keyed field"),
        pytest.param(GoText('statusAck, statusAlso = replyStatus{"ack"}'), id="two names"),
        pytest.param(GoText('statusAck replyStatus = replyStatus{"ack"}'), id="a declared type"),
        pytest.param(GoText('statusAck        = otherStatus{"ack"}'), id="another type"),
    ],
)
def test_a_value_of_no_one_word_is_named_at_its_line(
    monkeypatch: pytest.MonkeyPatch, value: GoText
) -> None:
    """A value of the block other than one name and one value of a word is named at its line."""
    refusal = f"{_WHERE}:{_line_of(_ACK)}: {value!r} is not one name and one replyStatus of a word"
    assert named_at(monkeypatch, _ACK, value, _STATUS) == [Prose(refusal)]


# Each case: a line of a function standing before the anchor, and what it does.
_IN_A_FUNCTION = [
    pytest.param(GoText('_ = replyStatus{"bogus"}'), _BUILDS, id="a value built"),
    pytest.param(GoText('_ = []replyStatus{{"bogus"}}'), _BUILDS, id="a value built in a slice"),
    pytest.param(GoText("_ = replyStatus(other)"), _CONVERTS, id="a text converted"),
    pytest.param(GoText("_ = (replyStatus)(other)"), _CONVERTS, id="a text converted in parens"),
    pytest.param(GoText("_ = []replyStatus(others)"), _CONVERTS, id="a slice converted"),
    pytest.param(
        GoText('_ = struct{ word string }{"bogus"}'),
        Prose("declares an unnamed struct a replyStatus is assigned from"),
        id="an unnamed struct of its field",
    ),
    pytest.param(
        GoText("_ = statusAck.word"),
        Prose("reaches the word of a value outside fieldStatus"),
        id="its field reached",
    ),
]


@pytest.mark.parametrize(("line", "what"), _IN_A_FUNCTION)
def test_a_value_given_its_word_in_a_function_is_named_at_its_line(
    monkeypatch: pytest.MonkeyPatch, line: GoText, what: Prose
) -> None:
    """A line of a function that could give a status its word is named at the status place."""
    stray = f"func strayValues(other string, others []string) {{\n\t{line}\n}}\n\n"
    assert named_at(monkeypatch, _ANCHOR, GoText(stray + _ANCHOR), _STATUS) == [
        Prose(f"{_WHERE}:{_line_of(_ANCHOR) + 1}: {line!r} {what}")
    ]


@pytest.mark.parametrize(
    ("declaration", "what"),
    [
        pytest.param(
            GoText("type statusAlias = replyStatus"), Prose("aliases replyStatus"), id="an alias"
        ),
        pytest.param(
            GoText("func pick[T ~replyStatus](t T) T { return t }"),
            Prose("constrains a type parameter to replyStatus"),
            id="a type parameter",
        ),
    ],
)
def test_a_declaration_giving_a_status_its_word_is_named_at_its_line(
    monkeypatch: pytest.MonkeyPatch, declaration: GoText, what: Prose
) -> None:
    """A top-level declaration that could give a status its word is named at the status place."""
    planted = GoText(f"{declaration}\n\n{_ANCHOR}")
    assert named_at(monkeypatch, _ANCHOR, planted, _STATUS) == [
        Prose(f"{_WHERE}:{_line_of(_ANCHOR)}: {declaration!r} {what}")
    ]

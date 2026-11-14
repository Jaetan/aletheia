# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate refuses a word a Go reader file compares outside the lines its rows read.

A reader file's line comparing a word, an ``==``, ``!=``, ``<``, ``<=``, ``>``
or ``>=`` beside a string literal, a ``case`` holding one, a literal key of a
composite literal, or a ``strings`` call or ``slices.Contains`` comparing its
first argument with anything but literals of no word, is reported at its line
unless it is a line a mapped row reads or a line of a switch or a select of a
function ``GO_UNTAGGED`` names.
A literal is read as the compiler reads its escapes, one it cannot read counting
as a word.  A literal inside a comment or a string, a rune beside ``==``, a
literal no comparison holds and a literal whose text is not identifier-shaped,
as no reply word is, compare no word.  A place ``GO_UNTAGGED`` reads past that ``replyText`` has a
row for is a divergence.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType

import pytest
from _go_reply_gate import UNPARSED, reported, unparsed

from tools import check_limits_parity
from tools._reply_places import REPO_ROOT, GoLine, GoSymbol, GoText, ReplyPlace
from tools._reply_places_go import GO_DBC, GO_REPLY_SHAPE, GO_RESPONSE, go_untagged_rows

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

# The index of a line of a stray reader's body, from 0.
_BodyLine = NewType("_BodyLine", int)

# The function each reader file holds a stray reader before, which no row names.
_ANCHORS = {
    GO_RESPONSE: GoText("func readTimestamp("),
    GO_DBC: GoText("func parseAttribute("),
    GO_REPLY_SHAPE: GoText("func fieldStatus("),
}
_STRAY = GoSymbol("strayReader")
_HOLDS = GoText('if status == "holds" {')
_CLOSE = GoText("}")


def _breach(path: Path, number: GoLine, line: GoText) -> Prose:
    """Return the gate's report of a word ``line`` compares at ``number`` of ``path``."""
    return Prose(
        f"{path.relative_to(REPO_ROOT)}:{number}: {line.strip()!r} "
        + "compares a word outside the lines GO_REPLY_TEXT reads"
    )


def _line_of(path: Path, text: GoText) -> GoLine:
    """Return the number of the one line of ``path`` that ``text`` opens, stripped."""
    lines = path.read_text(encoding="utf-8").split("\n")
    found = [GoLine(n) for n, line in enumerate(lines, start=1) if line.strip().startswith(text)]
    assert len(found) == 1, found
    return found[0]


def _with_stray(
    monkeypatch: pytest.MonkeyPatch, path: Path, body: tuple[GoText, ...]
) -> list[Prose]:
    """Return what the gate reports with a function holding ``body`` planted in ``path``.

    The function stands before the file's anchor, each line of ``body`` one of its
    own, its first line right after the function's opening line.
    """
    anchor = _ANCHORS[path]
    lines = "".join(f"\t{line}\n" for line in body)
    planted = GoText(f"func {_STRAY}(status string) {{\n{lines}}}\n\n{anchor}")
    return reported(monkeypatch, path, anchor, planted)


def _stray_line(path: Path, at: _BodyLine) -> GoLine:
    """Return the number of the line at ``at`` in the body of a stray planted in ``path``."""
    return GoLine(_line_of(path, _ANCHORS[path]) + 1 + at)


def _planted_after(
    monkeypatch: pytest.MonkeyPatch, path: Path, written: GoText, stray: GoText
) -> tuple[list[Prose], Prose]:
    """Return what the gate reports with ``stray`` planted on the line after ``written``.

    ``written`` is one whole line of ``path``; the stray opens a block closed on
    the line after it.  The second value is the report of a word ``stray``
    compares at its line.
    """
    planted = GoText(f"{written}\n\t{stray}\n\t}}")
    number = GoLine(_line_of(path, GoText(written.strip())) + 1)
    return reported(monkeypatch, path, written, planted), _breach(path, number, stray)


# Each case: a stray's body and the index of the line in it the gate reports.
_COMPARED = [
    pytest.param((_HOLDS, _CLOSE), _BodyLine(0), id="== literal"),
    pytest.param((GoText('if status != "holds" {'), _CLOSE), _BodyLine(0), id="!= literal"),
    pytest.param((GoText('if "holds" == status {'), _CLOSE), _BodyLine(0), id="literal =="),
    pytest.param((GoText('if "holds" != status {'), _CLOSE), _BodyLine(0), id="literal !="),
    pytest.param((GoText("if status == `holds` {"), _CLOSE), _BodyLine(0), id="== raw string"),
    pytest.param(
        (GoText('if status == "holds" || status == "fails" {'), _CLOSE),
        _BodyLine(0),
        id="two comparisons on one line",
    ),
    pytest.param(
        (GoText("switch {"), GoText('case strings.Contains(status, "holds"):'), _CLOSE),
        _BodyLine(1),
        id="case holding a literal",
    ),
    pytest.param(
        (GoText("switch status {"), GoText('case "holds", "fails":'), _CLOSE),
        _BodyLine(1),
        id="case of literals",
    ),
    pytest.param(
        (GoText("select {"), GoText('case words <- "holds":'), _CLOSE),
        _BodyLine(1),
        id="select case sending a literal",
    ),
    pytest.param(
        (GoText("switch status {"), GoText('case "holds",'), GoText('"fails":'), _CLOSE),
        _BodyLine(2),
        id="case literal on a line of its own",
    ),
    pytest.param(
        (GoText('_ = map[string]int{"holds": 1}[status]'),),
        _BodyLine(0),
        id="map literal keyed by literals",
    ),
    pytest.param(
        (GoText("_ = map[string]int{"), GoText('"holds": 1,'), GoText("}[status]")),
        _BodyLine(1),
        id="map literal key on a line of its own",
    ),
    *(
        pytest.param((GoText(f'_ = strings.{call}(status, "holds")'),), _BodyLine(0), id=call)
        for call in (
            "EqualFold",
            "HasPrefix",
            "HasSuffix",
            "TrimPrefix",
            "TrimSuffix",
            "CutPrefix",
            "CutSuffix",
            "Cut",
            "Compare",
            "Contains",
            "Index",
        )
    ),
    pytest.param(
        (GoText('_ = slices.Contains([]string{"holds", "fails"}, status)'),),
        _BodyLine(0),
        id="slices.Contains over a literal slice",
    ),
    pytest.param(
        (GoText('_ = slices.Contains(words, "holds")'),), _BodyLine(0), id="slices.Contains a word"
    ),
    pytest.param(
        (GoText("_ = slices.Contains(runes, 'h')"),), _BodyLine(0), id="slices.Contains a word rune"
    ),
    pytest.param(
        (GoText("_ = slices.Contains(runes, '\\\"')"),),
        _BodyLine(0),
        id="slices.Contains a rune escaping a double quote",
    ),
    pytest.param(
        (GoText("_ = strings.HasPrefix(status, prefix)"),),
        _BodyLine(0),
        id="strings call comparing with no literal",
    ),
    pytest.param(
        (GoText('_ = strings.EqualFold("-", status)'),),
        _BodyLine(0),
        id="strings call comparing a sign with no literal",
    ),
    pytest.param(
        (GoText('_ = strings.HasPrefix(status, "-"+prefix)'),),
        _BodyLine(0),
        id="strings call comparing with a sum",
    ),
    pytest.param(
        (GoText(r'_ = strings.HasPrefix(status, "\x68olds")'),),
        _BodyLine(0),
        id="strings call comparing with an escaped word",
    ),
    *(
        pytest.param(
            (GoText(f'if status {op} "holds" {{'), _CLOSE), _BodyLine(0), id=f"{op} literal"
        )
        for op in ("<", "<=", ">", ">=")
    ),
    *(
        pytest.param(
            (GoText(f'if "holds" {op} status {{'), _CLOSE), _BodyLine(0), id=f"literal {op}"
        )
        for op in ("<", "<=", ">", ">=")
    ),
    *(
        pytest.param((GoText(f'if status == "{text}" {{'), _CLOSE), _BodyLine(0), id=f"== {text}")
        for text in (
            r"\x68olds",
            r"hol\x64s",
            r"\u0068olds",
            r"\U00000068olds",
            r"\150olds",
            r"\q",
            r"\'",
            r"\400",
            r"\05",
            r"\uD800",
            r"\uDFFF",
            r"\U00110000",
        )
    ),
    pytest.param(
        (GoText('_ = strings.HasPrefix(word(status), "holds")'),),
        _BodyLine(0),
        id="strings call holding a call",
    ),
    pytest.param(
        (GoText('_ = strings.HasPrefix(status+"-", "holds")'),),
        _BodyLine(0),
        id="strings call with a word after a text that is not one",
    ),
    pytest.param(
        (GoText('if status == "_atom2" {'), _CLOSE),
        _BodyLine(0),
        id="== a word opening with _ and holding a digit",
    ),
    pytest.param(
        (GoText("_ = `first"), GoText("second`"), _HOLDS, _CLOSE),
        _BodyLine(2),
        id="after a raw string over two lines",
    ),
]


@pytest.mark.parametrize("path", list(_ANCHORS))
@pytest.mark.parametrize(("body", "at"), _COMPARED)
def test_a_word_compared_where_no_row_reads_is_reported_at_its_line(
    monkeypatch: pytest.MonkeyPatch, path: Path, body: tuple[GoText, ...], at: _BodyLine
) -> None:
    """Each form of a word comparison in a function no row names is reported once, at its line."""
    breach = _breach(path, _stray_line(path, at), body[at])
    assert _with_stray(monkeypatch, path, body).count(breach) == 1


# Each case: a stray's line that compares no word.
_UNCOMPARED = [
    pytest.param(GoText("if status[0] == '\"' {"), id="rune"),
    pytest.param(GoText('_ = status // status == "holds"'), id="literal in a comment"),
    pytest.param(GoText('_ = "status == \\"holds\\": case"'), id="literal in a string"),
    pytest.param(GoText('_ = `status == "holds"`'), id="literal in a raw string"),
    pytest.param(GoText('holds := "holds"'), id="literal assigned"),
    pytest.param(GoText('_ = m["holds"]'), id="literal key looked up"),
    pytest.param(GoText('_, _ = fieldWord(m, path, "status", "holds")'), id="fieldWord call"),
    pytest.param(GoText('if status == "" {'), id="== the empty text"),
    pytest.param(GoText('if status != "" {'), id="!= the empty text"),
    pytest.param(GoText('if "" == status {'), id="the empty text =="),
    pytest.param(GoText('_, _ = strings.CutPrefix(status, "-")'), id="strings call cutting a sign"),
    pytest.param(GoText('if status == "2nd" {'), id="== a text opening with a digit"),
    pytest.param(GoText('if status != "a-b" {'), id="!= a text holding a dash"),
    pytest.param(GoText("if status == `a b` {"), id="== a raw text holding a space"),
    pytest.param(GoText('switch status { case "", "-": }'), id="case of texts that are not words"),
    pytest.param(GoText('_ = map[string]int{"-": 1}[status]'), id="map keyed by a sign"),
    pytest.param(
        GoText('digits, negative := strings.CutPrefix(n.String(), "-")'),
        id="strings call cutting a sign from a call's text",
    ),
    pytest.param(GoText("_ = strings.HasPrefix(status, `-`)"), id="strings call with a raw sign"),
    pytest.param(GoText('_ = slices.Contains(words, "-")'), id="slices.Contains a sign"),
    pytest.param(GoText("_ = slices.Contains(runes, '-')"), id="slices.Contains a sign rune"),
    pytest.param(
        GoText('_ = strings.TrimLeft(status, " \\t\\r\\n")'), id="strings call trimming space"
    ),
    *(
        pytest.param(GoText(f'_ = strings.{call}(status, "holds")'), id=f"{call} takes a cutset")
        for call in ("Trim", "TrimLeft", "TrimRight")
    ),
    pytest.param(GoText("_ = slices.Contains(runes, '\\'')"), id="slices.Contains a quote rune"),
    pytest.param(GoText('_ = strings.HasPrefix(join(a, b), "-")'), id="a sign after a call"),
    pytest.param(
        GoText('_ = strings.HasPrefix(pick[string, int](a), "-")'), id="a sign after a generic call"
    ),
    pytest.param(
        GoText('_ = strings.HasPrefix(pair{a, b}.first, "-")'),
        id="a sign after a composite literal",
    ),
    pytest.param(
        GoText('_ = strings.HasPrefix(status, "-",)'), id="a sign before a trailing comma"
    ),
    pytest.param(GoText("if status[0] == 'h' {"), id="== a word rune"),
    pytest.param(GoText('if status < "-" {'), id="< a sign"),
    pytest.param(GoText('ch <- "holds"'), id="a word sent on a channel"),
    pytest.param(GoText(r"if status == `\x68olds` {"), id="== a raw text as written"),
    *(
        pytest.param(GoText(f'if status == "{text}" {{'), id=f"== {text}")
        for text in (
            r"\n",
            r"\a\b\f\r\t\v\\",
            r"\"",
            r"\x2d",
            r"a\x2f",
            r"\u002d",
            r"\U0000002d",
            r"\055",
            r"\377",
            r"\uD7FF",
            r"\uE000",
            r"\U0010FFFF",
        )
    ),
]


@pytest.mark.parametrize("line", _UNCOMPARED)
def test_a_line_comparing_no_word_is_not_reported(
    monkeypatch: pytest.MonkeyPatch, line: GoText
) -> None:
    """A literal no comparison holds, or a rune, a comment or a string's text, is no breach.

    A line opening a block has it closed on the next, so the grammar parses the file.
    """
    breach = _breach(GO_RESPONSE, _stray_line(GO_RESPONSE, _BodyLine(0)), line)
    found = _with_stray(monkeypatch, GO_RESPONSE, (line, _CLOSE) if line.endswith("{") else (line,))
    assert unparsed(found) == []
    assert breach not in found


def test_the_rows_compare_their_words_on_the_lines_they_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A mapped row's call and mapping are no breach."""
    anchor = _ANCHORS[GO_RESPONSE]
    found = reported(monkeypatch, GO_RESPONSE, anchor, anchor)
    for path, text in (
        (GO_DBC, GoText('case "little_endian":')),
        (GO_RESPONSE, GoText('if word == "error" {')),
        (GO_RESPONSE, GoText('case "fails":')),
        (GO_RESPONSE, GoText('case "holds":')),
    ):
        assert _breach(path, _line_of(path, text), text) not in found


def test_a_mapped_row_naming_no_function_its_file_defines_reads_no_line(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A mapped row whose function is not defined is reported, and reads no line of the file."""
    opening = GoText("func parseAttrTarget(")
    found = reported(monkeypatch, GO_DBC, opening, GoText("func readTarget("))
    case = GoText('case "nodeMsg":')
    lines = enumerate(GO_DBC.read_text(encoding="utf-8").split("\n"), start=1)
    after = _line_of(GO_DBC, opening)
    number = GoLine(next(n for n, line in lines if n > after and line.strip() == case))
    assert any(each.endswith("json_dbc.go:parseAttrTarget is not defined") for each in found)
    assert _breach(GO_DBC, number, case) in found


def test_a_comparison_in_a_mapped_rows_function_off_its_lines_is_reported(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A mapped row reads its call's lines and its mapping's, not the rest of its function."""
    written = GoText('\tindex, err := fieldUint64(r, path, "property_index")')
    stray = GoText('if path == "results" {')
    found, breach = _planted_after(monkeypatch, GO_RESPONSE, written, stray)
    assert breach in found


@pytest.mark.parametrize(
    ("body", "compared"),
    [
        pytest.param(
            (
                GoText("switch status {"),
                GoText('case "holds":'),
                _CLOSE,
                GoText("select {"),
                GoText('case words <- "holds":'),
                _CLOSE,
                GoText("switch any(status).(type) {"),
                GoText("case string:"),
                GoText('_ = status == "holds"'),
                _CLOSE,
                _HOLDS,
                _CLOSE,
            ),
            _BodyLine(10),
            id="beside a switch, a select and a type switch",
        ),
        pytest.param((_HOLDS, _CLOSE), _BodyLine(0), id="in a function holding neither"),
    ],
)
def test_a_function_go_untagged_names_is_read_past_at_its_switches_and_selects_alone(
    monkeypatch: pytest.MonkeyPatch, body: tuple[GoText, ...], compared: _BodyLine
) -> None:
    """A word compared in a switch or a select of a function ``GO_UNTAGGED`` names is no breach.

    The one the function compares at ``compared``, outside them, is the gate's one report.
    """
    untagged = {ReplyPlace("issues/code"): (GO_RESPONSE, _STRAY)}
    monkeypatch.setattr("tools._reply_places_go.GO_UNTAGGED", untagged)
    line = _stray_line(GO_RESPONSE, compared)
    found = _with_stray(monkeypatch, GO_RESPONSE, body)
    assert found == [_breach(GO_RESPONSE, line, body[compared])]


def test_a_function_go_untagged_names_and_no_file_defines_is_reported(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``GO_UNTAGGED`` naming a function its file does not define is reported."""
    untagged = {ReplyPlace("issues/code"): (GO_RESPONSE, GoSymbol("noSuchReader"))}
    monkeypatch.setattr("tools._reply_places_go.GO_UNTAGGED", untagged)
    anchor = _ANCHORS[GO_RESPONSE]
    assert Prose(
        "GO_UNTAGGED names go/aletheia/json_response.go:noSuchReader, not defined"
    ) in reported(monkeypatch, GO_RESPONSE, anchor, anchor)


def test_a_reader_file_the_package_lacks_is_reported_and_the_rest_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A reader file the package does not hold is reported, and the files after it still read."""
    missing = GO_RESPONSE.with_name("no_such_reader.go")
    monkeypatch.setattr("tools._reply_places_go.GO_READER_FILES", (missing, GO_RESPONSE))
    found = _with_stray(monkeypatch, GO_RESPONSE, (_HOLDS, _CLOSE))
    assert Prose("go/aletheia/no_such_reader.go is no file of the Go package") in found
    assert _breach(GO_RESPONSE, _stray_line(GO_RESPONSE, _BodyLine(0)), _HOLDS) in found


def test_the_lines_comparing_a_word_are_reported_in_their_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A comparing call and an ``==`` on the line after it are reported in their lines' order."""
    body = (GoText("_ = strings.HasPrefix(status, prefix)"), _HOLDS, _CLOSE)
    found = _with_stray(monkeypatch, GO_RESPONSE, body)
    breaches = [
        _breach(GO_RESPONSE, _stray_line(GO_RESPONSE, _BodyLine(at)), body[at]) for at in (0, 1)
    ]
    assert [each for each in found if each in breaches] == breaches


# A place `replyText` has a row for, and a function of the Go responses no row
# reads.
_ROWED = ReplyPlace("status")
_PASSED = GoSymbol("parseResponse")


def test_a_place_go_untagged_reads_past_is_a_divergence_once_reply_text_has_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``GO_UNTAGGED`` naming a place ``replyText`` has a row for is named; another is not."""
    monkeypatch.setattr("tools._reply_places_go.GO_UNTAGGED", {_ROWED: (GO_RESPONSE, _PASSED)})
    divergence = Prose(
        "reply place status: replyText has a row, so go/aletheia/json_response.go:parseResponse, "
        + "which GO_UNTAGGED reads past, reads a tag place; name it in GO_REPLY_TEXT"
    )
    assert go_untagged_rows([_ROWED, ReplyPlace("type")]) == [divergence]
    assert go_untagged_rows([ReplyPlace("type")]) == []


def test_the_gate_reports_a_place_go_untagged_reads_past_that_reply_text_has(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate exits 1 naming a ``GO_UNTAGGED`` place ``replyText`` has a row for."""
    monkeypatch.setattr("tools._reply_places_go.GO_UNTAGGED", {_ROWED: (GO_RESPONSE, _PASSED)})
    monkeypatch.setattr("sys.argv", ["check_limits_parity"])
    assert check_limits_parity.main() == 1
    assert "which GO_UNTAGGED reads past, reads a tag place" in capsys.readouterr().err


@pytest.mark.parametrize(
    "line",
    [
        pytest.param(GoText("if status == {"), id="an operand missing"),
        pytest.param(GoText("_ = len(status"), id="a parenthesis missing"),
        *(
            pytest.param(GoText(f'if status == "{text}" {{'), id=f"an escape {text} cut short")
            for text in (r"\x6", r"\u02d", r"\U000002d")
        ),
    ],
)
def test_a_line_the_grammar_cannot_parse_is_refused_at_it(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], line: GoText
) -> None:
    """A file holding a line tree-sitter-go cannot parse is refused there, and the gate exits 2."""
    number = _stray_line(GO_RESPONSE, _BodyLine(0))
    refusal = Prose(f"go/aletheia/json_response.go:{number}: {line!r} {UNPARSED}")
    assert unparsed(_with_stray(monkeypatch, GO_RESPONSE, (line, _CLOSE))) == [refusal]
    monkeypatch.setattr("sys.argv", ["check_limits_parity"])
    assert check_limits_parity.main() == 2
    assert f"check-limits-parity: {refusal}\n" in capsys.readouterr().err


def test_a_comparison_is_shown_without_its_comment(monkeypatch: pytest.MonkeyPatch) -> None:
    """A reported line is shown as its code reads, a comment on it blanked."""
    found = _with_stray(monkeypatch, GO_RESPONSE, (GoText(f"{_HOLDS} // the one word"), _CLOSE))
    assert _breach(GO_RESPONSE, _stray_line(GO_RESPONSE, _BodyLine(0)), _HOLDS) in found

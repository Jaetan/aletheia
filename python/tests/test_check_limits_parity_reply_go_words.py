# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads each Go word-call place from its call and any mapping of its word.

``readVerdict`` hands a property result's type and status to ``fieldWord``,
``parseStreamWarning`` a warning's kind and ``readSeverity`` an issue's
severity, and ``fieldWord`` refuses every other word, so each call's words are
the Go reader's set at its place.  ``readVerdict`` maps the status it binds in
a ``switch`` on it, ``readSeverity`` the severity in a chain of tests of it:
each word the mapping compares is one the call awaits, and the mapping's last
arm, the ``default`` or the code after the tests, reads the awaited words no
other arm names and the words of the arms giving its value, which must be one
word, the row's last, or none.  A word added to a call or dropped from it, a
call the gate cannot find, an arm naming a word the call refuses, a last arm
reading another word or several, or a mapping the gate cannot read is named at
the place, and the lines each mapped row reads are recorded.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _go_reply_gate import named_at

from tools._reply_places import GoLine, GoText, ReplyPlace
from tools._reply_places_go import GO_DBC, GO_RESPONSE, go_mapped_sites

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_TYPE = (ReplyPlace("results/type"),)
_STATUS = (ReplyPlace("results/status <property>"),)
_KIND = (ReplyPlace("warnings/kind"),)
_SEVERITY = (ReplyPlace("issues/severity"), ReplyPlace("warnings/severity"))
_TYPE_CALL = GoText('fieldWord(r, path, "type", "property")')
_READ_VERDICT_CALL = GoText('fieldWord(r, path, "status", "fails", "holds", "unresolved")')
_KIND_CALL = GoText('fieldWord(w, path, "kind", "uncached_atom")')
_READ_SEVERITY_CALL = GoText('fieldWord(issue, path, "severity", "error", "warning")')
_HOLDS = GoText('\tcase "holds":\n\t\tverdict = Holds\n')
_DEFAULT = GoText("\tdefault:\n\t\tverdict = Unresolved\n")
_UNRESOLVED = '\tcase "unresolved":\n\t\tverdict = Unresolved\n'
_ERROR = GoText('\tif word == "error" {\n\t\treturn SeverityError, nil\n\t}\n')
_WARNING = '\tif word == "warning" {\n\t\treturn SeverityWarning, nil\n\t}\n'
_FALL_THROUGH = GoText("\treturn SeverityWarning, nil\n")
_IN_VERDICT = "go/aletheia/json_response.go:readVerdict: "
_IN_SEVERITY = "go/aletheia/json_response.go:readSeverity: "

# Each case: the places it reads, the source it plants over, the plant, and what
# the gate names at each place.
_CASES = [
    pytest.param(_TYPE, _TYPE_CALL, _TYPE_CALL, [], id="type as written"),
    pytest.param(
        _TYPE,
        _TYPE_CALL,
        GoText('fieldWord(r, path, "type", "property", "verdict")'),
        [Prose("'verdict' is in the Go reader only")],
        id="type with a word added",
    ),
    pytest.param(
        _TYPE,
        _TYPE_CALL,
        GoText('fieldWord(r, path, "type", "verdict")'),
        [Prose("'property' is in replyText only"), Prose("'verdict' is in the Go reader only")],
        id="type with its word replaced",
    ),
    pytest.param(
        _TYPE,
        _TYPE_CALL,
        GoText('fieldWord(r, path, "kind", "property")'),
        [Prose(_IN_VERDICT + "no fieldWord call at 'type'")],
        id="type read by no call",
    ),
    pytest.param(
        _STATUS, _READ_VERDICT_CALL, _READ_VERDICT_CALL, [], id="status as readVerdict writes it"
    ),
    pytest.param(
        _STATUS,
        _READ_VERDICT_CALL,
        GoText('fieldWord(r, path, "status", "fails", "holds")'),
        [Prose("'unresolved' is in replyText only")],
        id="status with unresolved dropped from fieldWord",
    ),
    pytest.param(
        _STATUS,
        _READ_VERDICT_CALL,
        GoText('fieldWord(r, path, "status", "fails", "holds", "unresolved", "bogus")'),
        [
            Prose(
                _IN_VERDICT
                + "the default of the switch on status reads 'bogus', 'unresolved' alike"
            )
        ],
        id="status with a word added to fieldWord",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "held":\n\t\tverdict = Holds\n'),
        [
            Prose(
                _IN_VERDICT
                + "the switch on status names 'held', which no fieldWord call at 'status' awaits"
            )
        ],
        id="status with a case naming a word the call refuses",
    ),
    pytest.param(
        _STATUS,
        _DEFAULT,
        GoText(_UNRESOLVED + "\tdefault:\n\t\tverdict = Holds\n"),
        [Prose("the Go reader's last arm names 'holds', not 'unresolved'")],
        id="status with a default reading holds",
    ),
    pytest.param(
        _STATUS,
        _DEFAULT,
        GoText(_UNRESOLVED + _DEFAULT),
        [],
        id="status with a default sharing the unresolved case's value",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText(""),
        [
            Prose(
                _IN_VERDICT
                + "the default of the switch on status reads 'holds', 'unresolved' alike"
            )
        ],
        id="status with a default reading two words",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText(_UNRESOLVED),
        [
            Prose(
                _IN_VERDICT
                + "the default of the switch on status reads 'holds', 'unresolved' alike"
            )
        ],
        id="status with a shared default reading another word",
    ),
    pytest.param(
        _STATUS,
        GoText("switch status {"),
        GoText("switch strings.ToLower(status) {"),
        [Prose(_IN_VERDICT + "maps status in no switch on it and no chain of tests of it")],
        id="status mapped by no switch on it",
    ),
    pytest.param(
        _STATUS,
        GoText("switch status {"),
        GoText("mapped := status\n\tswitch mapped {"),
        [Prose(_IN_VERDICT + "maps status in no switch on it and no chain of tests of it")],
        id="status copied and its copy mapped",
    ),
    pytest.param(
        _STATUS,
        GoText("switch status {"),
        GoText('status = "holds"\n\tswitch status {'),
        [Prose(_IN_VERDICT + "uses status other than to map it")],
        id="status given another word before its switch",
    ),
    pytest.param(
        _STATUS,
        _DEFAULT,
        GoText(_UNRESOLVED),
        [Prose(_IN_VERDICT + "the switch on status does not end in default")],
        id="status with a switch not ending in default",
    ),
    pytest.param(
        _STATUS,
        GoText('\tcase "fails":\n\t\tverdict = Fails\n' + _HOLDS + _DEFAULT),
        GoText(""),
        [Prose(_IN_VERDICT + "the switch on status does not end in default")],
        id="status with an empty switch",
    ),
    pytest.param(
        _STATUS,
        GoText('"status", "fails"'),
        GoText('"state", "fails"'),
        [Prose(_IN_VERDICT + "no fieldWord call at 'status'")],
        id="status read by no fieldWord call",
    ),
    pytest.param(
        _STATUS,
        _TYPE_CALL,
        GoText('fieldWord(r, path, "status", "property")'),
        [Prose(_IN_VERDICT + "reads 'status' with fieldWord 2 times, not once")],
        id="status read by two fieldWord calls",
    ),
    pytest.param(
        _STATUS,
        GoText("status, err := fieldWord("),
        GoText("_, err := fieldWord("),
        [Prose(_IN_VERDICT + "binds the word fieldWord reads at 'status' to no variable")],
        id="status bound to the blank identifier",
    ),
    pytest.param(
        _STATUS,
        GoText('fieldUint64(r, path, "property_index")'),
        GoText("fieldUint64(r, path, status)"),
        [Prose(_IN_VERDICT + "uses status other than to map it")],
        id="status used outside its switch",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "holds":\n\t\tother = Holds\n'),
        [
            Prose(
                _IN_VERDICT
                + "the arms of the switch on status give their values in more than one way"
            )
        ],
        id="status with a case assigning another variable",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "holds":\n\t\tverdict = Holds\n\t\tfallthrough\n'),
        [Prose(_IN_VERDICT + repr("verdict = Holds\n\t\tfallthrough") + " gives no one value")],
        id="status with a case falling through",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText("\tcase holdsWord:\n\t\tverdict = Holds\n"),
        [Prose(_IN_VERDICT + "'case holdsWord:' is not a case of string literals on one line")],
        id="status with a case naming no literal",
    ),
    pytest.param(
        _STATUS,
        _READ_VERDICT_CALL,
        GoText('fieldWord(r, path, /* the key */ "status", "fails", "holds", "unresolved")'),
        [],
        id="status with a comment among fieldWord's arguments",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase\n\t\t"holds":\n\t\tverdict = Holds\n'),
        [Prose(_IN_VERDICT + "'case' is not a case of string literals on one line")],
        id="status with a case written over two lines",
    ),
    pytest.param(
        _STATUS,
        _READ_VERDICT_CALL,
        GoText('fieldWord(r, path, "status", "fails", "holds", unresolved()...)'),
        [Prose(_IN_VERDICT + "a fieldWord call holds a call of its own")],
        id="status read by a call holding a call",
    ),
    pytest.param(
        _STATUS,
        _TYPE_CALL,
        GoText('fieldWord(r, path, typeKey, "property")'),
        [
            Prose(
                _IN_VERDICT
                + 'fieldWord(r, path, typeKey, "property") names no literal key or no word'
            )
        ],
        id="status beside a call at a key that is no literal",
    ),
    pytest.param(
        _STATUS,
        _TYPE_CALL,
        GoText('fieldWord(r, path, "type")'),
        [Prose(_IN_VERDICT + 'fieldWord(r, path, "type") names no literal key or no word')],
        id="status beside a call awaiting no word",
    ),
    pytest.param(
        _STATUS,
        _READ_VERDICT_CALL,
        GoText('fieldWord(r, path, "status", "fails", "holds", unresolvedWord)'),
        [
            Prose(
                _IN_VERDICT
                + 'fieldWord(r, path, "status", "fails", "holds", unresolvedWord) '
                + "awaits a word that is not a literal"
            )
        ],
        id="status awaiting a word that is no literal",
    ),
    pytest.param(
        _STATUS,
        GoText("func readVerdict("),
        GoText("func readVerdicts("),
        [Prose("go/aletheia/json_response.go:readVerdict is not defined")],
        id="status read by a function the file does not define",
    ),
    pytest.param(
        _STATUS,
        GoText("status, err := fieldWord("),
        GoText("var status, err = fieldWord("),
        [],
        id="status bound by a var declaration",
    ),
    pytest.param(
        _STATUS,
        GoText("status, err := fieldWord("),
        GoText("status, err = fieldWord("),
        [],
        id="status bound by an assignment",
    ),
    pytest.param(
        _STATUS,
        GoText("status, err := fieldWord("),
        GoText("status, err += fieldWord("),
        [Prose(_IN_VERDICT + "binds the word fieldWord reads at 'status' to no variable")],
        id="status added to",
    ),
    pytest.param(
        _STATUS,
        GoText("switch status {"),
        GoText("switch index := index; status {"),
        [Prose(_IN_VERDICT + "maps status in no switch on it and no chain of tests of it")],
        id="status switched on after a statement",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "holds":\n\t\tverdict := Holds\n'),
        [Prose(_IN_VERDICT + "'verdict := Holds' gives no one value")],
        id="status with a case declaring a variable",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "holds":\n\t\tverdict = Holds, Fails\n'),
        [Prose(_IN_VERDICT + "'verdict = Holds, Fails' gives no one value")],
        id="status with a case assigning two values",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        GoText('\tcase "holds":\n\t\tverdict = holds\n'),
        [Prose(_IN_VERDICT + "'verdict = holds' gives no one value")],
        id="status with a case assigning an unexported name",
    ),
    pytest.param(_KIND, _KIND_CALL, _KIND_CALL, [], id="kind as written"),
    pytest.param(
        _KIND,
        _KIND_CALL,
        GoText('fieldWord(w, path, "kind", "uncached_atom", "stale_atom")'),
        [Prose("'stale_atom' is in the Go reader only")],
        id="kind with a word added",
    ),
    pytest.param(
        _KIND,
        _KIND_CALL,
        GoText('fieldWord(w, path, "kind", "stale_atom")'),
        [
            Prose("'stale_atom' is in the Go reader only"),
            Prose("'uncached_atom' is in replyText only"),
        ],
        id="kind with its word replaced",
    ),
    pytest.param(
        _SEVERITY,
        _READ_SEVERITY_CALL,
        _READ_SEVERITY_CALL,
        [],
        id="severity as readSeverity writes it",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText(
            '\tif word == "error" {\n\t\treturn SeverityError, nil\n\t} else {\n'
            + _FALL_THROUGH
            + "\t}\n"
        ),
        [Prose(_IN_SEVERITY + "maps word in no switch on it and no chain of tests of it")],
        id="severity tested with an else",
    ),
    pytest.param(
        _SEVERITY,
        _ERROR,
        GoText('\tif path := path; word == "error" {\n\t\treturn SeverityError, nil\n\t}\n'),
        [Prose(_IN_SEVERITY + "maps word in no switch on it and no chain of tests of it")],
        id="severity tested after a statement",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText(_WARNING.replace("==", "!=") + "\treturn SeverityWarning, nil\n"),
        [Prose(_IN_SEVERITY + "maps word in no switch on it and no chain of tests of it")],
        id="severity tested by an inequality",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText(_WARNING.replace("==", "<") + "\treturn SeverityWarning, nil\n"),
        [Prose(_IN_SEVERITY + "maps word in no switch on it and no chain of tests of it")],
        id="severity tested by an ordering",
    ),
    pytest.param(
        _SEVERITY,
        _ERROR,
        GoText('\tcopied := word\n\tif copied == "error" {\n\t\treturn SeverityError, nil\n\t}\n'),
        [Prose(_IN_SEVERITY + "maps word in no switch on it and no chain of tests of it")],
        id="severity copied and its copy tested",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText("\t{\n" + _ERROR + _FALL_THROUGH + "\t}\n"),
        [Prose(_IN_SEVERITY + repr("return SeverityWarning, nil\n\t}") + " gives no one value")],
        id="severity tested in a block of its own",
    ),
    pytest.param(
        _SEVERITY,
        _FALL_THROUGH,
        GoText("\treturn severityWarning, nil\n"),
        [Prose(_IN_SEVERITY + "'return severityWarning, nil' gives no one value")],
        id="severity with a last arm returning an unexported name",
    ),
    pytest.param(
        _SEVERITY,
        _FALL_THROUGH,
        GoText("\treturn SeverityWarning, err\n"),
        [Prose(_IN_SEVERITY + "'return SeverityWarning, err' gives no one value")],
        id="severity with a last arm returning an error",
    ),
    pytest.param(
        _SEVERITY,
        _FALL_THROUGH,
        GoText("\t// The one other word.\n" + _FALL_THROUGH),
        [],
        id="severity with a comment before its last arm",
    ),
    pytest.param(
        _SEVERITY,
        _READ_SEVERITY_CALL,
        GoText('fieldWord(issue, path, "severity", "error")'),
        [Prose("'warning' is in replyText only")],
        id="severity with warning dropped from fieldWord",
    ),
    pytest.param(
        _SEVERITY,
        _READ_SEVERITY_CALL,
        GoText('fieldWord(issue, path, "severity", "error", "warning", "fatal")'),
        [Prose(_IN_SEVERITY + "the code after the tests of word reads 'fatal', 'warning' alike")],
        id="severity with a word added to fieldWord",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText(_WARNING + "\treturn SeverityError, nil\n"),
        [Prose("the Go reader's last arm names 'error', not 'warning'")],
        id="severity with a last arm reading error",
    ),
    pytest.param(
        _SEVERITY,
        GoText(_ERROR + _FALL_THROUGH),
        GoText(_ERROR + _WARNING + _FALL_THROUGH),
        [],
        id="severity with both words tested",
    ),
    pytest.param(
        _SEVERITY,
        _ERROR,
        GoText('\tif word == "error" {\n\t\tseverity = SeverityError\n\t}\n'),
        [
            Prose(
                _IN_SEVERITY
                + "the arms of the tests of word give their values in more than one way"
            )
        ],
        id="severity with a test assigning its value",
    ),
    pytest.param(
        _SEVERITY,
        _READ_SEVERITY_CALL,
        GoText(f"strings.ToLower({_READ_SEVERITY_CALL})"),
        [Prose(_IN_SEVERITY + "binds the word fieldWord reads at 'severity' to no variable")],
        id="severity bound to no variable",
    ),
]


@pytest.mark.parametrize(("places", "written", "planted", "named"), _CASES)
def test_the_gate_names_at_each_place_what_the_call_and_its_mapping_read_amiss(
    monkeypatch: pytest.MonkeyPatch,
    places: tuple[ReplyPlace, ...],
    written: GoText,
    planted: GoText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted``, the gate names ``named`` at each place."""
    for place in places:
        assert named_at(monkeypatch, written, planted, place) == named


def _dbc_sites() -> set[tuple[Path, GoLine]]:
    """Return the line of each DBC reader's call and those of its switch, to its closing brace."""
    numbered = list(enumerate(GO_DBC.read_text(encoding="utf-8").split("\n"), start=1))
    lines: set[GoLine] = set()
    for function in (
        "readByteOrder",
        "parseSignalPresence",
        "parseCommentTarget",
        "parseAttribute",
        "readAttrScope",
        "parseAttrType",
        "parseAttrValue",
        "parseAttrTarget",
    ):
        opening = next(n for n, line in numbered if line.startswith(f"func {function}("))
        at = next(n for n, line in numbered if n > opening and ":= fieldWord(" in line)
        head = next(n for n, line in numbered if n > at and line.startswith("\tswitch "))
        end = next(n for n, line in numbered if n > head and line == "\t}")
        lines |= {GoLine(at), *map(GoLine, range(head, end + 1))}
    return {(GO_DBC, line) for line in lines}


def test_the_mapped_rows_record_the_lines_of_their_calls_and_mappings() -> None:
    """Each mapped row reads its call's line and its mapping's, from its head to its last line."""
    numbered = list(enumerate(GO_RESPONSE.read_text(encoding="utf-8").split("\n"), start=1))

    def first(text: GoText, after: GoLine) -> GoLine:
        return next(
            GoLine(n) for n, line in numbered if n > after and line.strip().startswith(text)
        )

    top = GoLine(0)
    switch = first(GoText("switch status {"), top)
    tests = first(GoText('if word == "error" {'), top)
    expected = {
        first(GoText('status, err := fieldWord(r, path, "status"'), top),
        *range(switch, first(GoText("}"), switch) + 1),
        first(GoText('word, err := fieldWord(issue, path, "severity"'), top),
        *range(tests, first(GoText("return SeverityWarning, nil"), tests) + 1),
    }
    assert go_mapped_sites() == {(GO_RESPONSE, GoLine(n)) for n in expected} | _dbc_sites()

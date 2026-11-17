# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads a Rust word place from a call and its mapping.

``read_verdict`` hands a property result's status to ``field_word``, which
refuses every other word, ``read_issue`` an issue's severity and
``read_signal`` a signal's byte order and presence, ``read_comment`` a
comment target's kind and ``read_attribute`` an attribute's kind, then maps the
word through ``verdict``, ``severity``, ``byte_order``, ``presence``,
``comment_target`` or ``attribute``: the call's words are
the Rust reader's set at its place, each literal arm of the mapping is one of
them, and the mapping's ``_`` arm reads the awaited words no other arm names
and the words of the arms building its variant, which must be one word, the
row's last, or none.  Each call hands its word, ``?`` after it, to the mapping
as its first argument, which the mapping's ``word`` takes, or through a
``let`` whose name the caller uses once more, as that argument; a caller
building its value another way is refused.  A word added to the call or
dropped from it, an arm naming a word the call refuses, or a ``_``
arm reading another word or several is named at the place.  A reader
file's literal compared outside the functions the rows name is reported at its
line when its text, read as the compiler reads its escapes, is
identifier-shaped, as every reply word is, or cannot be read, and passed over
otherwise; a comparing call is reported unless it compares with literals of no
word alone, and a mapping holding such a call compares a word outside its
patterns.  A mapping or a call of another shape is refused where it stands, as
is a line the grammar cannot parse.
"""

from __future__ import annotations

from typing import NamedTuple

import pytest
from _rust_reply_gate import at_place, named_at, planted_in, unparsed

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    ReplyPlace,
    ReplyTables,
    read_reply_tables,
)
from tools._reply_places_rust import RUST_DECODE, RUST_RESPONSE, RustText, rust_reader

from aletheia.common_types import Prose

_STATUS = (ReplyPlace("results/status <property>"),)
_SEVERITY = (ReplyPlace("issues/severity"), ReplyPlace("warnings/severity"))
_STATUS_CALL = RustText('field_word(result, path, "status", &["fails", "holds", "unresolved"])')
_SEVERITY_CALL = RustText('field_word(issue, path, "severity", &["error", "warning"])')
_STATUS_BINDING = RustText(f"let status = {_STATUS_CALL}?;")
_STATUS_HANDED = RustText("verdict: verdict(status),")
_SEVERITY_HANDED = RustText(f"severity({_SEVERITY_CALL}?)")
_HOLDS = RustText('"holds" => Verdict::Holds,')
_VERDICT_LAST = RustText("_ => Verdict::Unresolved,")
_SEVERITY_LAST = RustText("_ => IssueSeverity::Warning,")
_IN_VERDICT = "rust/src/response.rs:read_verdict: "
_IN_ISSUE = "rust/src/response.rs:read_issue: "
_VERDICT_HEAD = RustText("fn verdict(word: &str) -> Verdict")
_CALL_SHAPE = "a field_word call holds a call of its own, or no literal key and words"
_STATUS_UNHANDED = (
    "does not hand the word field_word reads at 'status' to verdict, "
    + "as its first argument or through a let"
)
_STATUS_MISUSED = "uses status other than once, as the first argument of verdict"


class _Refused(NamedTuple):
    """A mapping or a call of a shape the gate refuses, and why it does at the status place."""

    name: Prose
    written: RustText
    planted: RustText
    why: Prose


# Each mapping or call of a shape the gate refuses: a name, the source it plants
# over, the plant, and why the gate refuses it at the status place.
_REFUSED_MAPPINGS = tuple(
    _Refused(Prose(name), written, planted, Prose(why))
    for name, written, planted, why in (
        (
            "status with its mapping defined twice",
            RustText("fn verdict("),
            RustText("fn verdict(word: &str) -> Verdict {\n    Verdict::Holds\n}\n\nfn verdict("),
            "verdict is defined 2 times, not once",
        ),
        (
            "status with a mapping not taking the word first",
            _VERDICT_HEAD,
            RustText("fn verdict(name: &str) -> Verdict"),
            "verdict: does not take the word first, as word: &str",
        ),
        (
            "status with a mapping taking the word mutably",
            _VERDICT_HEAD,
            RustText("fn verdict(word: &mut str) -> Verdict"),
            "verdict: does not take the word first, as word: &str",
        ),
        (
            "status with a mapping taking the word borrowed apart",
            _VERDICT_HEAD,
            RustText("fn verdict(word: & str) -> Verdict"),
            "verdict: does not take the word first, as word: &str",
        ),
        (
            "status with a mapping taking a pointer",
            _VERDICT_HEAD,
            RustText("fn verdict(word: *const str) -> Verdict"),
            "verdict: does not take the word first, as word: &str",
        ),
        (
            "status with a mapping matching on the word in parentheses",
            RustText('    match word {\n        "fails"'),
            RustText('    match (word) {\n        "fails"'),
            "verdict: is not one match on word returning a type of its own",
        ),
        (
            "status with a mapping matching no arm",
            RustText(
                '    match word {\n        "fails" => Verdict::Fails,\n'
                + '        "holds" => Verdict::Holds,\n        _ => Verdict::Unresolved,\n    }'
            ),
            RustText("    match word {}"),
            "verdict: its match's last arm is not _",
        ),
        (
            "status read by a call of two arguments",
            _STATUS_CALL,
            RustText('field_word("status", &["fails", "holds", "unresolved"])'),
            _CALL_SHAPE,
        ),
        (
            "status with an arm building a variant of no ASCII capital",
            _HOLDS,
            RustText('"holds" => Verdict::Ölds,'),
            "verdict: the arm '\"holds\"' builds 0 variants of Verdict, not one",
        ),
        (
            "status read by a call awaiting a cast array",
            _STATUS_CALL,
            RustText(
                'field_word(result, path, "status", ["fails", "holds", "unresolved"] as [&str; 3])'
            ),
            _CALL_SHAPE,
        ),
        (
            "status with a mapping returning a borrow",
            _VERDICT_HEAD,
            RustText("fn verdict(word: &str) -> &'static Verdict"),
            "verdict: is not one match on word returning a type of its own",
        ),
        (
            "status with a mapping returning a lowercase type",
            _VERDICT_HEAD,
            RustText("fn verdict(word: &str) -> verdict"),
            "verdict: is not one match on word returning a type of its own",
        ),
        (
            "status with a mapping returning nothing",
            _VERDICT_HEAD,
            RustText("fn verdict(word: &str)"),
            "verdict: is not one match on word returning a type of its own",
        ),
        (
            "status with a mapping holding a second match",
            _VERDICT_LAST,
            RustText("_ => match 0 { _ => Verdict::Unresolved },"),
            "verdict: is not one match on word returning a type of its own",
        ),
        (
            "status with a mapping using the word in an arm",
            _HOLDS,
            RustText('"holds" => { let _ = word; Verdict::Holds }'),
            "verdict: uses word other than to match on it",
        ),
        (
            "status with an arm of a byte string",
            _HOLDS,
            RustText('b"holds" => Verdict::Holds,'),
            "verdict: the arm 'b\"holds\"' is neither _ nor string literals joined by |",
        ),
        (
            "status with an arm of an escaped word",
            _HOLDS,
            RustText('"\\x68olds" => Verdict::Holds,'),
            "verdict: the arm '\"\\\\x68olds\"' is neither _ nor string literals joined by |",
        ),
        (
            "status with an arm under a guard",
            _HOLDS,
            RustText('"holds" if true => Verdict::Holds,'),
            "verdict: the arm '\"holds\" if true' is neither _ nor string literals joined by |",
        ),
        (
            "status with an arm under an attribute",
            _HOLDS,
            RustText('#[cfg(x)] "holds" => Verdict::Holds,'),
            "verdict: the arm '#[cfg(x)] \"holds\"' is neither _ nor string literals joined by |",
        ),
        (
            "status with an arm building two variants",
            _HOLDS,
            RustText('"holds" => Verdict::Holds.max(Verdict::Fails),'),
            "verdict: the arm '\"holds\"' builds 2 variants of Verdict, not one",
        ),
        (
            "status with an arm building none",
            _HOLDS,
            RustText('"holds" => Default::default(),'),
            "verdict: the arm '\"holds\"' builds 0 variants of Verdict, not one",
        ),
        (
            "status with an arm naming a variant without its type's path",
            _HOLDS,
            RustText('"holds" => Verdict(Holds),'),
            "verdict: the arm '\"holds\"' builds 0 variants of Verdict, not one",
        ),
        (
            "status with an arm naming a word twice",
            _HOLDS,
            RustText('"holds" | "holds" => Verdict::Holds,'),
            "verdict: its match names a word twice",
        ),
        (
            "status read by a call holding a call",
            _STATUS_CALL,
            RustText('field_word(result, (path), "status", &["fails", "holds", "unresolved"])'),
            _CALL_SHAPE,
        ),
        (
            "status read by a call at a key of a name",
            _STATUS_CALL,
            RustText('field_word(result, path, STATUS, &["fails", "holds", "unresolved"])'),
            _CALL_SHAPE,
        ),
        (
            "status read by a call awaiting a mutable array",
            _STATUS_CALL,
            RustText('field_word(result, path, "status", &mut ["fails", "holds", "unresolved"])'),
            _CALL_SHAPE,
        ),
        (
            "status read by a call awaiting a slice of a name",
            _STATUS_CALL,
            RustText('field_word(result, path, "status", &STATUSES)'),
            _CALL_SHAPE,
        ),
        (
            "status read by a call awaiting a name",
            _STATUS_CALL,
            RustText('field_word(result, path, "status", &["fails", "holds", UNRESOLVED])'),
            'field_word(result, path, "status", &["fails", "holds", UNRESOLVED]) '
            + "awaits a word that is not a literal",
        ),
        (
            "status read by a call awaiting no word",
            _STATUS_CALL,
            RustText('field_word(result, path, "status", &[])'),
            'field_word(result, path, "status", &[]) awaits a word that is not a literal',
        ),
    )
)

# Each case: the places it reads, the source it plants over, the plant, and what
# the gate names at each place.
_CASES = [
    pytest.param(_STATUS, _STATUS_CALL, _STATUS_CALL, [], id="status as written"),
    pytest.param(
        _STATUS,
        _STATUS_CALL,
        RustText('field_word(result, path, "status", &["fails", "holds"])'),
        [Prose("'unresolved' is in replyText only")],
        id="status with unresolved dropped from the call",
    ),
    pytest.param(
        _STATUS,
        _STATUS_CALL,
        RustText('field_word(result, path, "status", &["fails", "holds", "unresolved", "bogus"])'),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'bogus', 'unresolved' alike")],
        id="status with a word added to the call",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"held" => Verdict::Holds,'),
        [Prose(_IN_VERDICT + "verdict names 'held', which no field_word call at 'status' awaits")],
        id="status with an arm naming a word the call refuses",
    ),
    pytest.param(
        _STATUS,
        _VERDICT_LAST,
        RustText('"unresolved" => Verdict::Unresolved,\n        _ => Verdict::Holds,'),
        [Prose("the Rust reader's last arm names 'holds', not 'unresolved'")],
        id="status with a last arm reading holds",
    ),
    pytest.param(
        _STATUS,
        _VERDICT_LAST,
        RustText('"unresolved" => Verdict::Unresolved,\n        _ => Verdict::Unresolved,'),
        [],
        id="status with a last arm sharing the unresolved arm's variant",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" | "unresolved" => Verdict::Unresolved,'),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'holds', 'unresolved' alike")],
        id="status with a last arm sharing a two-word arm's variant",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText(""),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'holds', 'unresolved' alike")],
        id="status with a last arm reading two words",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"unresolved" => Verdict::Unresolved,'),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'holds', 'unresolved' alike")],
        id="status with a shared last arm reading another word",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" => Verdict::Unresolved,\n        "unresolved" => Verdict::Unresolved,'),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'holds', 'unresolved' alike")],
        id="status with a last arm sharing the variant of two arms",
    ),
    pytest.param(
        _STATUS,
        RustText("fn verdict("),
        RustText("fn verdict_of("),
        [Prose(_IN_VERDICT + "verdict is not defined")],
        id="status with its mapping undefined",
    ),
    pytest.param(
        _STATUS,
        _VERDICT_LAST,
        RustText('"unresolved" => Verdict::Unresolved,'),
        [Prose(_IN_VERDICT + "verdict: its match's last arm is not _")],
        id="status with a mapping whose last arm is not _",
    ),
    pytest.param(
        _STATUS,
        RustText('"status", &["fails"'),
        RustText('"state", &["fails"'),
        [Prose(_IN_VERDICT + "no field_word call at 'status'")],
        id="status read by no call",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" => { let _ = "-".eq("holds"); Verdict::Holds }'),
        [Prose(_IN_VERDICT + "verdict: compares a word other than in its match's patterns")],
        id="status with a mapping arm comparing a word in a call",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" => { let _ = "-".eq("+"); Verdict::Holds }'),
        [],
        id="status with a mapping arm comparing a sign in a call",
    ),
    pytest.param(_SEVERITY, _SEVERITY_CALL, _SEVERITY_CALL, [], id="severity as written"),
    pytest.param(
        _SEVERITY,
        _SEVERITY_CALL,
        RustText('field_word(issue, path, "severity", &["error"])'),
        [Prose("'warning' is in replyText only")],
        id="severity with warning dropped from the call",
    ),
    pytest.param(
        _SEVERITY,
        _SEVERITY_CALL,
        RustText('field_word(issue, path, "severity", &["error", "warning", "fatal"])'),
        [Prose(_IN_ISSUE + "the _ arm of severity reads 'fatal', 'warning' alike")],
        id="severity with a word added to the call",
    ),
    pytest.param(
        _SEVERITY,
        _SEVERITY_LAST,
        RustText('"warning" => IssueSeverity::Warning,\n        _ => IssueSeverity::Error,'),
        [Prose("the Rust reader's last arm names 'error', not 'warning'")],
        id="severity with a last arm reading error",
    ),
    pytest.param(
        _SEVERITY,
        RustText('"error" => IssueSeverity::Error,'),
        RustText(
            '"error" => IssueSeverity::Warning,\n        "warning" => IssueSeverity::Warning,'
        ),
        [Prose(_IN_ISSUE + "the _ arm of severity reads 'error', 'warning' alike")],
        id="severity with a last arm sharing the variant of two arms",
    ),
    *(
        pytest.param(_STATUS, written, planted, [Prose(_IN_VERDICT + why)], id=name)
        for name, written, planted, why in _REFUSED_MAPPINGS
    ),
    pytest.param(
        _STATUS,
        _VERDICT_HEAD,
        RustText("fn verdict<'a>(word: &'a str) -> Verdict"),
        [],
        id="status with a mapping taking the word at a lifetime",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" | "unresolved" => Verdict::Holds,'),
        [],
        id="status with an arm of two words",
    ),
    pytest.param(
        _STATUS,
        RustText('"fails" => Verdict::Fails,\n        "holds" => Verdict::Holds,'),
        RustText('"fails" | "holds" | "unresolved" => Verdict::Holds,'),
        [],
        id="status with an arm of three words",
    ),
    pytest.param(
        _STATUS,
        RustText("fn verdict("),
        RustText(
            "#[cfg(test)]\nfn verdict(word: &str) -> Verdict {\n    Verdict::Holds\n}\n\n"
            + "fn verdict("
        ),
        [],
        id="status with a second mapping in a test item",
    ),
    pytest.param(
        _STATUS,
        RustText('    match word {\n        "fails"'),
        RustText('    #[cfg(test)]\n    let _ = word;\n    match word {\n        "fails"'),
        [],
        id="status with a mapping using the word in a test item",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(
            "#[cfg(test)]\n"
            + '    let _ = field_word(result, path, "status", &["bogus"]);\n'
            + f"    {_STATUS_BINDING}"
        ),
        [],
        id="status read by a second call in a test item",
    ),
    pytest.param(
        _STATUS,
        _HOLDS,
        RustText('"holds" => { let _ = Other::Thing; Verdict::Holds }'),
        [],
        id="status with an arm naming another type's variant",
    ),
    pytest.param(
        _STATUS,
        RustText('"holds" => Verdict::Holds,\n        _ => Verdict::Unresolved,'),
        RustText(
            '"unresolved" => Verdict::Unresolved,\n        "holds" => Verdict::Unresolved,\n'
            + "        _ => Verdict::Unresolved,"
        ),
        [Prose(_IN_VERDICT + "the _ arm of verdict reads 'holds', 'unresolved' alike")],
        id="status with two arms building the last arm's variant",
    ),
    pytest.param(
        _STATUS,
        _STATUS_CALL,
        RustText(f"crate::reply_shape::{_STATUS_CALL}"),
        [],
        id="status read by a call through its path",
    ),
    pytest.param(
        _STATUS,
        _STATUS_CALL,
        RustText('field_word(result, path, "status", &["fails", "holds", "unresolved",])'),
        [],
        id="status read by a call with a trailing comma",
    ),
    pytest.param(
        _STATUS,
        _STATUS_HANDED,
        RustText("verdict: Verdict::Holds,"),
        [Prose(_IN_VERDICT + _STATUS_MISUSED)],
        id="status unused, its verdict built another way",
    ),
    pytest.param(
        _STATUS,
        _STATUS_HANDED,
        RustText("verdict: Verdict::from_word(status),"),
        [Prose(_IN_VERDICT + _STATUS_MISUSED)],
        id="status handed to another function",
    ),
    pytest.param(
        _STATUS,
        _STATUS_HANDED,
        RustText("verdict: verdict(status, Verdict::Holds),"),
        [],
        id="status handed to its mapping first, beside another argument",
    ),
    pytest.param(
        _STATUS,
        _STATUS_HANDED,
        RustText("verdict: verdict(Verdict::Holds, status),"),
        [Prose(_IN_VERDICT + _STATUS_MISUSED)],
        id="status handed to its mapping after another argument",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(f'{_STATUS_BINDING}\n    let status = "holds";'),
        [Prose(_IN_VERDICT + _STATUS_MISUSED)],
        id="status shadowed after the read",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(f'{_STATUS_BINDING}\n    let r#status = "holds";'),
        [Prose(_IN_VERDICT + _STATUS_MISUSED)],
        id="status shadowed by its raw name",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(f"let r#status = {_STATUS_CALL}?;"),
        [],
        id="status bound by its raw name",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(
            f"let status = match {_STATUS_CALL} {{\n"
            + '        Ok(word) => word,\n        Err(_) => "holds",\n    };'
        ),
        [Prose(_IN_VERDICT + _STATUS_UNHANDED)],
        id="status bound with its refusal read as holds",
    ),
    pytest.param(
        _STATUS,
        _STATUS_BINDING,
        RustText(f"for status in {_STATUS_CALL}? {{}}"),
        [Prose(_IN_VERDICT + _STATUS_UNHANDED)],
        id="status bound by a loop",
    ),
    pytest.param(
        _SEVERITY,
        _SEVERITY_HANDED,
        RustText(f"{{\n        {_SEVERITY_CALL}?;\n        IssueSeverity::Error\n    }}"),
        [
            Prose(
                _IN_ISSUE
                + "does not hand the word field_word reads at 'severity' to severity, "
                + "as its first argument or through a let"
            )
        ],
        id="severity read and its value built another way",
    ),
    pytest.param(
        _SEVERITY,
        _SEVERITY_HANDED,
        RustText(f"{{\n        let word = {_SEVERITY_CALL}?;\n        severity(word)\n    }}"),
        [],
        id="severity handed through a let",
    ),
]


def _reported(monkeypatch: pytest.MonkeyPatch, written: RustText, planted: RustText) -> list[Prose]:
    """Return each set the Rust reader cannot read, or else each divergence, with a plant.

    The plant writes ``written`` as ``planted`` in the Rust responses.
    """
    return planted_in(monkeypatch, RUST_RESPONSE, written, planted)


@pytest.mark.parametrize(("places", "written", "planted", "named"), _CASES)
def test_the_gate_names_at_each_place_what_the_call_and_its_mapping_read_amiss(
    monkeypatch: pytest.MonkeyPatch,
    places: tuple[ReplyPlace, ...],
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted``, the gate names ``named`` at each place.

    Every plant leaves the file Rust the grammar parses.
    """
    reported = _reported(monkeypatch, written, planted)
    assert unparsed(reported) == []
    for place in places:
        assert at_place(reported, place) == named


_BYTE_ORDER = ReplyPlace("dbc/messages/signals/byteOrder")
_PRESENCE = ReplyPlace("dbc/messages/signals/presence")
_IN_SIGNAL = "rust/src/dbc/decode.rs:read_signal: "
_BYTE_ORDER_WORDS = RustText('&["little_endian", "big_endian"],')
_PRESENCE_CALL = RustText('field_word(signal, path, "presence", &["always", "multiplexed"])')
_PRESENCE_ARGUMENTS = RustText(f"{_PRESENCE_CALL}?,\n            signal,\n            path,")
_PRESENCE_READ = RustText(f"presence: presence(\n            {_PRESENCE_ARGUMENTS}\n        )?,")
_PRESENCE_UNHANDED = (
    "does not hand the word field_word reads at 'presence' to presence, "
    + "as its first argument or through a let"
)


def _presence_bound(handed: RustText) -> RustText:
    """Return a signal's presence read into a ``let`` and handed to ``presence`` as ``handed``."""
    return RustText(
        f"presence: {{\n            let word = {_PRESENCE_CALL}?;\n"
        + f"            presence({handed})?\n        }},"
    )


@pytest.mark.parametrize(
    ("place", "written", "planted", "named"),
    [
        pytest.param(_BYTE_ORDER, _BYTE_ORDER_WORDS, _BYTE_ORDER_WORDS, [], id="byte order"),
        pytest.param(
            _BYTE_ORDER,
            _BYTE_ORDER_WORDS,
            RustText('&["little_endian"],'),
            [Prose("'big_endian' is in replyText only")],
            id="byte order with big_endian dropped from the call",
        ),
        pytest.param(
            _BYTE_ORDER,
            RustText('"little_endian" => ByteOrder::LittleEndian,'),
            RustText('"little_endian" => ByteOrder::BigEndian,'),
            [
                Prose(
                    _IN_SIGNAL + "the _ arm of byte_order reads 'big_endian', 'little_endian' alike"
                )
            ],
            id="byte order with its last arm sharing the little_endian arm's variant",
        ),
        pytest.param(
            _PRESENCE, _PRESENCE_READ, _PRESENCE_READ, [], id="presence handed first of three"
        ),
        pytest.param(
            _PRESENCE,
            _PRESENCE_ARGUMENTS,
            RustText(f"signal,\n            {_PRESENCE_CALL}?,\n            path,"),
            [Prose(_IN_SIGNAL + _PRESENCE_UNHANDED)],
            id="presence handed second",
        ),
        pytest.param(
            _PRESENCE,
            _PRESENCE_ARGUMENTS,
            RustText(
                f"match {_PRESENCE_CALL} {{\n                Ok(word) => word,\n"
                + '                Err(_) => "always",\n            },\n'
                + "            signal,\n            path,"
            ),
            [Prose(_IN_SIGNAL + _PRESENCE_UNHANDED)],
            id="presence handed first with its refusal read as always",
        ),
        pytest.param(
            _PRESENCE,
            _PRESENCE_READ,
            _presence_bound(RustText("word, signal, path")),
            [],
            id="presence handed first through a let",
        ),
        pytest.param(
            _PRESENCE,
            _PRESENCE_READ,
            _presence_bound(RustText("signal, word, path")),
            [Prose(_IN_SIGNAL + "uses word other than once, as the first argument of presence")],
            id="presence handed second through a let",
        ),
    ],
)
def test_a_signal_word_reaches_its_mapping_as_its_first_argument(
    monkeypatch: pytest.MonkeyPatch,
    place: ReplyPlace,
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted`` in the DBC decoder, the gate names ``named``.

    A mapping taking the word first may take the object and its path after it,
    so ``presence`` reads the word ``read_signal`` hands it beside the keys a
    multiplexed signal carries; a word handed in any other position is refused,
    as is one whose refusal the caller reads as a word.
    """
    assert named_at(monkeypatch, (written, planted), place, RUST_DECODE) == named


_TARGET_KIND = ReplyPlace("dbc/comments/target/kind")
_ATTRIBUTE_KIND = ReplyPlace("dbc/attributes/kind")
_TARGET_WORDS = RustText('&["network", "node", "message", "signal", "envVar"],')
_TARGET_HANDED = RustText("comment_target(kind, target, place)")
_ATTRIBUTE_HANDED = RustText("attribute(kind, name, attribute_entry, path)")
_IN_COMMENT = "rust/src/dbc/decode.rs:read_comment: "
_IN_ATTRIBUTE = "rust/src/dbc/decode.rs:read_attribute: "
_TARGET_MISUSED = "uses kind other than once, as the first argument of comment_target"
_ATTRIBUTE_MISUSED = "uses kind other than once, as the first argument of attribute"


@pytest.mark.parametrize(
    ("place", "written", "planted", "named"),
    [
        pytest.param(_TARGET_KIND, _TARGET_HANDED, _TARGET_HANDED, [], id="target kind"),
        pytest.param(
            _TARGET_KIND,
            _TARGET_WORDS,
            RustText('&["network", "node", "message", "signal"],'),
            [Prose("'envVar' is in replyText only")],
            id="target kind with envVar dropped from the call",
        ),
        pytest.param(
            _TARGET_KIND,
            RustText('"network" => Ok(CommentTarget::Network),'),
            RustText('"network" => Ok(CommentTarget::EnvVar { env_var: String::new() }),'),
            [Prose(_IN_COMMENT + "the _ arm of comment_target reads 'envVar', 'network' alike")],
            id="target kind with its last arm sharing the network arm's variant",
        ),
        pytest.param(
            _TARGET_KIND,
            _TARGET_HANDED,
            RustText("comment_target(target, kind, place)"),
            [Prose(_IN_COMMENT + _TARGET_MISUSED)],
            id="target kind handed second",
        ),
        pytest.param(
            _ATTRIBUTE_KIND, _ATTRIBUTE_HANDED, _ATTRIBUTE_HANDED, [], id="attribute kind"
        ),
        pytest.param(
            _ATTRIBUTE_KIND,
            RustText('&["definition", "default", "assignment"],'),
            RustText('&["definition", "default"],'),
            [Prose("'assignment' is in replyText only")],
            id="attribute kind with assignment dropped from the call",
        ),
        pytest.param(
            _ATTRIBUTE_KIND,
            RustText('"default" => Ok(Attribute::Default {'),
            RustText('"default" => Ok(Attribute::Assignment {'),
            [Prose(_IN_ATTRIBUTE + "the _ arm of attribute reads 'assignment', 'default' alike")],
            id="attribute kind with its last arm sharing the default arm's variant",
        ),
        pytest.param(
            _ATTRIBUTE_KIND,
            _ATTRIBUTE_HANDED,
            RustText("attribute(&kind, name, attribute_entry, path)"),
            [Prose(_IN_ATTRIBUTE + _ATTRIBUTE_MISUSED)],
            id="attribute kind handed borrowed",
        ),
    ],
)
def test_a_dbc_kind_reaches_its_mapping_through_a_let(
    monkeypatch: pytest.MonkeyPatch,
    place: ReplyPlace,
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted`` in the DBC decoder, the gate names ``named``.

    ``read_comment`` reads a comment target's kind in the closure reading the
    target, and ``read_attribute`` an attribute's kind before its name, each
    into a ``let`` handed to its mapping first: a word dropped from the call, a
    last arm sharing another arm's variant, or the word handed in another
    position or borrowed is named at the place.
    """
    assert named_at(monkeypatch, (written, planted), place, RUST_DECODE) == named


def test_the_mappings_compare_their_words_where_the_gate_reads_them() -> None:
    """The literal arms of ``verdict`` and ``severity`` are no word compared outside a read set."""
    agda = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    tables = read_reply_tables(agda, (rust_reader(frozenset()),))
    assert isinstance(tables, ReplyTables), tables


# A function of the Rust responses no row names, before which a stray reader is planted.
_STRAY_ANCHOR = RustText("fn is_ack(")


@pytest.mark.parametrize(
    ("line", "compares"),
    [
        pytest.param(RustText('if word == "holds" {}'), True, id="== a word"),
        pytest.param(RustText('if word != "_atom2" {}'), True, id="!= a word opening with _"),
        pytest.param(RustText('if r#"holds"# == word {}'), True, id="a raw word =="),
        pytest.param(RustText('let "holds" = word else { return };'), True, id="let a word"),
        pytest.param(
            RustText('match word { "holds" | "fails" => {} _ => {} }'), True, id="arms of words"
        ),
        pytest.param(RustText('if word == "" {}'), False, id="== the empty text"),
        pytest.param(RustText('if "-" != word {}'), False, id="a sign !="),
        pytest.param(RustText('if word == "2nd" {}'), False, id="== a text opening with a digit"),
        pytest.param(
            RustText('let "a b" = word else { return };'), False, id="let a text holding a space"
        ),
        pytest.param(
            RustText('match word { "" | "-" => {} _ => {} }'), False, id="arms of texts no word"
        ),
        pytest.param(RustText('if word.starts_with("holds") {}'), True, id="starts_with a word"),
        pytest.param(RustText('if word.ne("holds") {}'), True, id="ne a word"),
        pytest.param(RustText('if word.ends_with("holds") {}'), True, id="ends_with a word"),
        pytest.param(
            RustText('if word.strip_prefix("holds").is_some() {}'), True, id="strip_prefix a word"
        ),
        pytest.param(
            RustText('if word.strip_suffix("holds").is_some() {}'), True, id="strip_suffix a word"
        ),
        pytest.param(RustText('if word.eq("-".trim()) {}'), True, id="eq a sign's method"),
        pytest.param(RustText("if word.starts_with(prefix) {}"), True, id="starts_with no literal"),
        pytest.param(RustText("if word.starts_with('h') {}"), True, id="starts_with a word char"),
        pytest.param(RustText('if "-".eq(word) {}'), True, id="a sign eq no literal"),
        pytest.param(RustText('if word.eq("-") {}'), False, id="eq a sign"),
        pytest.param(RustText('if word.starts_with("-") {}'), False, id="starts_with a sign"),
        pytest.param(RustText('if word.ends_with(r"-") {}'), False, id="ends_with a raw sign"),
        pytest.param(
            RustText("if word.strip_prefix('-').is_some() {}"), False, id="strip_prefix a sign char"
        ),
        pytest.param(
            RustText(r'if word.eq_ignore_ascii_case("\x68olds") {}'),
            True,
            id="eq_ignore_ascii_case an escaped word",
        ),
        pytest.param(RustText(r'if word == r"\x68olds" {}'), False, id="== a raw text as written"),
        pytest.param(RustText('if word == "hol\\\n        ds" {}'), True, id="== a word continued"),
        pytest.param(RustText('if word == "\\\n        -" {}'), False, id="== a sign continued"),
        pytest.param(
            RustText('if word == "hol\\\n \t\r\n        ds" {}'),
            True,
            id="== a word continued past every white space",
        ),
        pytest.param(RustText('if word == &"holds" {}'), True, id="== a borrowed word"),
        pytest.param(
            RustText('if word ==\n        /* the word */ "holds" {}'),
            True,
            id="== a word after a comment",
        ),
        pytest.param(RustText(r'if word == "\-" {}'), True, id="== an escape Rust reads as none"),
        pytest.param(RustText('if word != b"holds" {}'), True, id="!= a byte word"),
        pytest.param(RustText('if word == c"holds" {}'), True, id="== a C word"),
        pytest.param(RustText('if word.len() == "holds".len() {}'), True, id="== a word's method"),
        pytest.param(RustText('if let "holds" = word {}'), True, id="if let a word"),
        pytest.param(
            RustText('match word { "holds" if true => {} _ => {} }'),
            True,
            id="a guarded arm of a word",
        ),
        pytest.param(RustText('let _ = matches!(word, "holds");'), True, id="matches! a word"),
        pytest.param(RustText("let _ = matches!(word, Some(_));"), True, id="matches! no word"),
        pytest.param(RustText('assert!(word == "holds");'), True, id="== a word in a macro"),
        pytest.param(RustText('assert!(word.eq("holds"));'), True, id="eq a word in a macro"),
        pytest.param(
            RustText(r"if word.starts_with('\x68') {}"), True, id="starts_with an escaped word char"
        ),
        pytest.param(RustText("if word.starts_with(b'h') {}"), True, id="starts_with a byte char"),
        pytest.param(
            RustText('if word.starts_with(("-")) {}'), True, id="starts_with a sign in parentheses"
        ),
        pytest.param(RustText('if word.eq("-", other) {}'), True, id="eq a sign and a name"),
        pytest.param(RustText('if word.eq(sign("-")) {}'), True, id="eq a call of a sign"),
        pytest.param(
            RustText('if "holds"\n        == "fails" {}'), True, id="two words compared once"
        ),
        pytest.param(RustText("if ch == 'h' {}"), False, id="== a word char"),
        pytest.param(RustText(r"if word.starts_with('\'') {}"), False, id="starts_with a quote"),
        pytest.param(
            RustText('if word.starts_with("-",) {}'), False, id="starts_with a sign, a comma after"
        ),
        pytest.param(RustText('if word.eq("-", "+") {}'), False, id="eq two signs"),
        pytest.param(RustText("let _ = word.eq;"), False, id="eq not called"),
        pytest.param(RustText('if word. eq("holds") {}'), False, id="eq a word after a space"),
        pytest.param(RustText('let _ = matches !(word, "holds");'), False, id="matches ! apart"),
        pytest.param(RustText('// if word == "holds" {}'), False, id="a comparison in a comment"),
        pytest.param(
            RustText('let _ = "word == \\"holds\\"";'), False, id="a comparison in a string"
        ),
        pytest.param(
            RustText('let _ = r#"word == "holds""#;'), False, id="a comparison in a raw string"
        ),
        pytest.param(RustText("if word == HOLDS {}"), False, id="== a constant"),
        *(
            pytest.param(RustText(f'if word == "{text}" {{}}'), True, id=f"== {text}")
            for text in (
                r"\x68olds",
                r"hol\x64s",
                r"\u{68}olds",
                r"\u{000068}olds",
                r"\q",
                r"\x80",
                r"\u{000002d}",
                r"\u{D800}",
                r"\u{DFFF}",
                r"\u{110000}",
            )
        ),
        *(
            pytest.param(RustText(f'if word == "{text}" {{}}'), False, id=f"== {text}")
            for text in (
                r"\n",
                r"\r",
                r"\t",
                r"\\",
                r"\0",
                r"\'",
                r"\"",
                r"\x2d",
                r"a\x2f",
                r"\x7f",
                r"\u{2d}",
                r"\u{00002d}",
                r"\u{D7FF}",
                r"\u{E000}",
                r"\u{10FFFF}",
            )
        ),
    ],
)
def test_a_literal_compared_where_no_row_reads_is_reported_when_it_is_word_shaped(
    monkeypatch: pytest.MonkeyPatch, line: RustText, *, compares: bool
) -> None:
    """A stray reader's word comparison is the one breach named; another changes nothing."""
    unplanted = _reported(monkeypatch, _STRAY_ANCHOR, _STRAY_ANCHOR)
    lines = RUST_RESPONSE.read_text(encoding="utf-8").split("\n")
    at = [number for number, text in enumerate(lines, start=1) if text.startswith(_STRAY_ANCHOR)]
    assert len(at) == 1, at
    breach = Prose(
        f"rust/src/response.rs:{at[0] + 1}: {line.split(chr(10))[0]!r} "
        + "compares a word outside the lines RUST_REPLY_TEXT reads"
    )
    planted = RustText(f"fn stray_reader(word: &str) {{\n    {line}\n}}\n\n{_STRAY_ANCHOR}")
    assert _reported(monkeypatch, _STRAY_ANCHOR, planted) == ([breach] if compares else unplanted)


def test_a_word_compared_in_a_test_item_is_read_past(monkeypatch: pytest.MonkeyPatch) -> None:
    """A reader file's ``#[cfg(test)]`` item is no part of the library, nor its comparisons."""
    unplanted = _reported(monkeypatch, _STRAY_ANCHOR, _STRAY_ANCHOR)
    planted = RustText(
        '#[cfg(test)]\nfn stray_reader(word: &str) {\n    if word == "holds" {}\n}\n\n'
        + _STRAY_ANCHOR
    )
    assert _reported(monkeypatch, _STRAY_ANCHOR, planted) == unplanted

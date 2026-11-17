# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads the Rust status place from the words one method gives an enum.

``ReplyStatus::word`` gives each variant of ``ReplyStatus``, declared once and
deriving traits that give no word, its own word in one match on ``self``; the
words are the Rust reader's set at the place.  A second declaration, an
attribute that could give a word, a variant that is not a unit, a method of
another shape and a method outside an impl of the enum are named at the place,
as is each line of the library that could give a variant a second word or
reach its word: a pattern of a variant outside the method, ``word`` reached
outside it and ``field_status``, an import of the variants and another impl
naming the enum.  A line of a file of a test module is no part of the library.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _rust_reply_gate import line_of, named_at

from tools._reply_places import REPO_ROOT, ReplyPlace
from tools._reply_places_rust import RUST_REPLY_SHAPE, RUST_RESPONSE, RUST_SOURCE, RustText

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_STATUS = ReplyPlace("status")
_WHERE = "rust/src/reply_shape.rs:ReplyStatus::word: "
_DERIVE = RustText("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub(crate) enum ReplyStatus")
_ERROR_VARIANT = RustText("    Error,\n}")
_ERROR_ARM = RustText('ReplyStatus::Error => "error",')
_ACK_ARM = RustText('ReplyStatus::Ack => "ack",')
_HOLDER = RustText("impl ReplyStatus {\n    /// The word the kernel writes")
_GIVER = RustText("pub(crate) fn word(self) -> &'static str {")
_UNSHAPED = Prose(
    _WHERE + "its body is not one match on self, each arm one variant giving one literal"
)
_OWN_WORD = Prose(_WHERE + "its arms do not give each variant of ReplyStatus its own word")
_NOT_A_UNIT = Prose(_WHERE + "a variant of ReplyStatus is not a unit variant without an attribute")
_NO_IMPL = Prose(
    "rust/src/reply_shape.rs: field_status is not defined once, "
    + "or word is no method of an impl of ReplyStatus"
)


@pytest.mark.parametrize(
    ("path", "written", "planted", "named"),
    [
        pytest.param(RUST_REPLY_SHAPE, _GIVER, _GIVER, [], id="as written"),
        pytest.param(
            RUST_RESPONSE,
            RustText("fn is_ack("),
            RustText("pub(crate) enum ReplyStatus {\n    Success,\n}\n\nfn is_ack("),
            [Prose("ReplyStatus is not declared once, in rust/src/reply_shape.rs")],
            id="declared twice",
        ),
        pytest.param(
            RUST_RESPONSE,
            RustText("fn is_ack("),
            RustText("enum ReplyStatus<T> {\n    Of(T),\n}\n\nfn is_ack("),
            [],
            id="a generic enum of the name beside it",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText(
                "#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]\n"
                + "pub(crate) enum ReplyStatus"
            ),
            [
                Prose(
                    _WHERE
                    + "#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)] "
                    + "on ReplyStatus could give it a word"
                )
            ],
            id="deriving a trait that could give a word",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText(
                "#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n#[repr(u8)]\n"
                + "pub(crate) enum ReplyStatus"
            ),
            [Prose(_WHERE + "#[repr(u8)] on ReplyStatus could give it a word")],
            id="another attribute",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText("#[derive(Debug, Clone, Copy, PartialEq, Eq,)]\npub(crate) enum ReplyStatus"),
            [],
            id="deriving with a trailing comma",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText("#[derive(Debug Clone, Copy, PartialEq, Eq)]\npub(crate) enum ReplyStatus"),
            [
                Prose(
                    _WHERE
                    + "#[derive(Debug Clone, Copy, PartialEq, Eq)] "
                    + "on ReplyStatus could give it a word"
                )
            ],
            id="deriving two traits with no comma between",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText("#[derive (Debug, Clone, Copy, PartialEq, Eq)]\npub(crate) enum ReplyStatus"),
            [
                Prose(
                    _WHERE
                    + "#[derive (Debug, Clone, Copy, PartialEq, Eq)] "
                    + "on ReplyStatus could give it a word"
                )
            ],
            id="derive written apart from its parenthesis",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText(
                "#[repr(u8)]\n/// A status.\n#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n"
                + "pub(crate) enum ReplyStatus"
            ),
            [Prose(_WHERE + "#[repr(u8)] on ReplyStatus could give it a word")],
            id="an attribute before a doc comment",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText(
                "#[repr(u8)]\n#[non_exhaustive]\n#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n"
                + "pub(crate) enum ReplyStatus"
            ),
            [Prose(_WHERE + "#[repr(u8)] on ReplyStatus could give it a word")],
            id="two other attributes",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _DERIVE,
            RustText(
                "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]\n"
                + "pub(crate) enum ReplyStatus"
            ),
            [],
            id="deriving every trait that gives no word",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_VARIANT,
            RustText("    Error = 5,\n}"),
            [_NOT_A_UNIT],
            id="a variant with a value",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_VARIANT,
            RustText("    #[default]\n    Error,\n}"),
            [_NOT_A_UNIT],
            id="a variant with an attribute",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_VARIANT,
            RustText("    Error(u8),\n}"),
            [_NOT_A_UNIT],
            id="a variant holding a value",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_VARIANT,
            RustText("    error,\n}"),
            [_NOT_A_UNIT],
            id="a variant of a lowercase name",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _GIVER,
            RustText("pub(crate) fn spelling(self) -> &'static str {"),
            [Prose(_WHERE + "not defined once")],
            id="its method undefined",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_ARM,
            RustText('ReplyStatus::Error => "ack",'),
            [_OWN_WORD],
            id="two variants given one word",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_ARM,
            RustText(""),
            [_OWN_WORD],
            id="a variant given no word",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_ARM,
            RustText('Self::Error => "error",'),
            [],
            id="an arm naming the variant through Self",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_ARM,
            RustText('ReplyStatus::Error => return "error",'),
            [_UNSHAPED],
            id="an arm returning",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ERROR_ARM,
            RustText('ReplyStatus {} => "error",'),
            [_UNSHAPED],
            id="an arm of a struct pattern",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ACK_ARM,
            RustText('ReplyStatus::Ack => word_of(ReplyStatus::Ack, "ack"),'),
            [_UNSHAPED],
            id="an arm giving a call",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            RustText("        match self {"),
            RustText(
                "        if false {\n            return ACK;\n        }\n        match self {"
            ),
            [_UNSHAPED],
            id="a return beside the match",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            RustText("        match self {"),
            RustText(
                "        let _ = |never: std::convert::Infallible| match never {};\n"
                + "        match self {"
            ),
            [_UNSHAPED],
            id="a second match, of no arm",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ACK_ARM,
            RustText('ReplyStatus::Ack => if true { "ack" } else { "acked" },'),
            [_UNSHAPED],
            id="an arm giving two literals",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ACK_ARM,
            RustText('ReplyStatus::Ack => b"ack",'),
            [_UNSHAPED],
            id="an arm giving a byte string",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ACK_ARM,
            RustText("ReplyStatus::Ack => ACK,"),
            [_UNSHAPED],
            id="an arm giving a constant",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            RustText("        match self {"),
            RustText('        let _ = "x";\n        match self {'),
            [_UNSHAPED],
            id="a literal beside the match",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            RustText("        match self {"),
            RustText("        match (self) {"),
            [_UNSHAPED],
            id="a match on another value",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _ACK_ARM,
            RustText('ReplyStatus::Ack => match 0 { _ => "ack" },'),
            [_UNSHAPED],
            id="a second match",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _HOLDER,
            RustText("impl Statuses {\n    /// The word the kernel writes"),
            [_NO_IMPL],
            id="its method in an impl of another type",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            _HOLDER,
            RustText(
                "impl From<ReplyStatus> for u8 {\n    fn from(_: ReplyStatus) -> u8 {\n        0\n"
                + "    }\n}\n\nimpl Statuses {\n    /// The word the kernel writes"
            ),
            [_NO_IMPL],
            id="its method in an impl of another type beside an impl naming it",
        ),
        pytest.param(
            RUST_REPLY_SHAPE,
            RustText("pub(crate) fn field_status("),
            RustText("pub(crate) fn read_status("),
            [_NO_IMPL],
            id="its reader undefined",
        ),
    ],
)
def test_the_gate_names_at_the_status_place_what_the_enum_and_its_method_read_amiss(
    monkeypatch: pytest.MonkeyPatch,
    path: Path,
    written: RustText,
    planted: RustText,
    named: list[Prose],
) -> None:
    """With ``written`` planted as ``planted`` in ``path``, the gate names ``named`` at status."""
    assert named_at(monkeypatch, (written, planted), _STATUS, path) == named


# The line of a file that a stray's code is planted before, by file: the
# responses, a file of the library no reader reads, a file of a test module,
# and, in the enum's module, a line outside its impl and a line inside it.
_RESPONSE = (RUST_RESPONSE, RustText("fn is_ack("))
_LOG = (RUST_SOURCE / "log.rs", RustText("use std::fmt;"))
_TESTS = (RUST_SOURCE / "response" / "tests.rs", RustText("use super::*;"))
_CRATE_TESTS = (RUST_SOURCE / "tests.rs", RustText("use super::*;"))
_OUTSIDE = (RUST_REPLY_SHAPE, RustText("/// The status at `key`, one of `expected`"))
_INSIDE = (RUST_REPLY_SHAPE, _GIVER)
_REACH = Prose("reaches word outside field_status")
_SECOND = Prose("matches on a ReplyStatus outside word, which could give it a second word")
_IMPORT = Prose("imports the variants of ReplyStatus, which a pattern could name bare")
_IMPL = Prose("implements for ReplyStatus beside the impl holding word")


@pytest.mark.parametrize(
    ("at", "line", "what"),
    [
        pytest.param(_RESPONSE, RustText("let _ = status.word();"), _REACH, id="word called"),
        pytest.param(
            _RESPONSE,
            RustText("let _ = (status.word(), status.word());"),
            _REACH,
            id="word called twice on a line",
        ),
        pytest.param(
            _RESPONSE, RustText("let _ = ReplyStatus::word(status);"), _REACH, id="word by path"
        ),
        pytest.param(
            _RESPONSE,
            RustText('let _ = match status { ReplyStatus::Ack => "acked", _ => "" };'),
            _SECOND,
            id="a variant in an arm",
        ),
        pytest.param(
            _RESPONSE,
            RustText("let _ = matches!(status, ReplyStatus::Ack | ReplyStatus::Error);"),
            _SECOND,
            id="a variant before a | in a macro",
        ),
        pytest.param(
            _RESPONSE,
            RustText('let _ = match status { ReplyStatus::Ack if true => "", _ => "" };'),
            _SECOND,
            id="a variant under a guard",
        ),
        pytest.param(
            _RESPONSE,
            RustText('let _ = match status { ReplyStatus::Not_A1 => "", _ => "" };'),
            _SECOND,
            id="a variant named with a digit and an underscore",
        ),
        pytest.param(
            _RESPONSE,
            RustText("use crate::reply_shape::ReplyStatus::{Ack, Error};"),
            _IMPORT,
            id="its variants imported",
        ),
        pytest.param(
            _RESPONSE,
            RustText("use crate::reply_shape::ReplyStatus::*;"),
            _IMPORT,
            id="its variants imported whole",
        ),
        pytest.param(
            _RESPONSE,
            RustText("let _ = stringify!(ReplyStatus::* | Ack);"),
            _IMPORT,
            id="its variants imported whole before a | in a macro",
        ),
        pytest.param(
            _RESPONSE,
            RustText("impl Default for ReplyStatus { fn default() -> Self { Self::Ack } }"),
            _IMPL,
            id="another impl",
        ),
        pytest.param(
            _LOG,
            RustText('const _: fn(ReplyStatus) -> &str = |s| match s { ReplyStatus::Ack => "" };'),
            _SECOND,
            id="a variant in an arm of another file",
        ),
        pytest.param(
            _OUTSIDE,
            RustText("impl From<ReplyStatus> for Statuses { fn from(_: ReplyStatus) -> Self {} }"),
            _IMPL,
            id="another impl naming it in the enum's module",
        ),
        pytest.param(
            _INSIDE,
            RustText("pub(crate) fn spelled(self) -> &'static str { Self::word(self) }"),
            _REACH,
            id="word through Self beside the method",
        ),
        pytest.param(
            _INSIDE,
            RustText(
                "pub(crate) fn acked(self) -> bool { matches!(self, Self::Ack | Self::Error) }"
            ),
            _SECOND,
            id="a variant through Self beside the method",
        ),
    ],
)
def test_a_line_that_could_give_a_variant_a_second_word_is_named_at_its_line(
    monkeypatch: pytest.MonkeyPatch, at: tuple[Path, RustText], line: RustText, what: Prose
) -> None:
    """A line of the library that could give a status another word is named at the place."""
    path, anchor = at
    number = line_of(path, anchor)
    where = path.relative_to(REPO_ROOT)
    named = named_at(monkeypatch, (anchor, RustText(f"{line}\n{anchor}")), _STATUS, path)
    assert named == [Prose(f"{where}:{number}: {line!r} {what}")]


@pytest.mark.parametrize(
    ("at", "line"),
    [
        pytest.param(
            _TESTS,
            RustText('const _: fn(ReplyStatus) -> &str = |s| match s { ReplyStatus::Ack => "" };'),
            id="a variant in an arm of a test module",
        ),
        pytest.param(
            _CRATE_TESTS,
            RustText('const _: fn(ReplyStatus) -> &str = |s| match s { ReplyStatus::Ack => "" };'),
            id="a variant in an arm of the crate's test module",
        ),
        pytest.param(
            _OUTSIDE,
            RustText("impl Statuses { fn of(self) -> &'static str { Self::word(self) } }"),
            id="word through Self in an impl of another type",
        ),
        pytest.param(
            _OUTSIDE,
            RustText("impl Statuses { fn of(s: ReplyStatus) {} }"),
            id="an impl of another type taking a status",
        ),
        pytest.param(
            _OUTSIDE,
            RustText(
                "impl Statuses { fn acked(self) -> bool { "
                + "matches!(self, Self::Ack | Self::Error) } }"
            ),
            id="a variant through Self in an impl of another type",
        ),
        pytest.param(
            _RESPONSE,
            RustText("impl Verdict { fn spelled(self) -> &'static str { Self::word(self) } }"),
            id="word through Self in another file's impl",
        ),
    ],
)
def test_a_line_that_gives_no_status_a_word_is_not_named(
    monkeypatch: pytest.MonkeyPatch, at: tuple[Path, RustText], line: RustText
) -> None:
    """A test module's line, or another type's ``Self``, gives no status a word."""
    path, anchor = at
    assert named_at(monkeypatch, (anchor, RustText(f"{line}\n{anchor}")), _STATUS, path) == []


# The end of the impl holding `word` and the head of `field_status` after it,
# planted as a `field_status` of that impl reaching `word` through `Self`, the
# function after renamed; and the lines of that function reaching `word`.
_READER_AFTER_IMPL = RustText(
    "    }\n}\n\n/// The status at `key`, one of `expected`, any other refused with the words\n"
    + "/// quoted as [`field_word`] refuses: the one reader of a status's word.\n"
    + "pub(crate) fn field_status("
)
_READER_IN_IMPL = RustText(
    "    }\n\n    pub(crate) fn field_status(self) -> &'static str {\n        Self::word(self)\n"
    + "    }\n}\n\npub(crate) fn read_status("
)
_READING = (
    RustText("if let Some(&found) = expected.iter().find(|status| status.word() == word)"),
    RustText("let spellings: Vec<&str>"),
)


def test_the_reader_reaching_word_through_self_in_its_impl_is_not_named(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``field_status``, a method of the impl holding ``word``, reaches it through ``Self``.

    Only the renamed function's lines reaching ``word`` are named, in one report.
    """
    planted = (
        RUST_REPLY_SHAPE.read_text(encoding="utf-8")
        .replace(_READER_AFTER_IMPL, _READER_IN_IMPL)
        .split("\n")
    )
    reaching = [
        f"rust/src/reply_shape.rs:{n}: {line.strip()!r} {_REACH}"
        for n, line in enumerate(planted, start=1)
        if line.strip().startswith(_READING)
    ]
    assert len(reaching) == len(_READING)
    named = named_at(monkeypatch, (_READER_AFTER_IMPL, _READER_IN_IMPL), _STATUS, RUST_REPLY_SHAPE)
    assert named == [Prose("; ".join(reaching))]

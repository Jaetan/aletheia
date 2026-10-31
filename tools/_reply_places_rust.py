# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Rust reader of the reply-tags arm, ``tools/_reply_places.py``.

It reads the set the Rust binding's reply readers take at each string place of
``replyText`` from their own code: the string-literal arms of a function's one
``match`` on its ``word``, the literals its ``field_word`` calls await, the
words one method gives an enum's variants, which no line elsewhere may give or
reach, or the ``BOUND_KIND_*`` codes.  A function reading the word at its key
into an unused binding compares none and takes every word.  A match's final
``_`` arm, which reads every word its other arms do not name, reads as the word
of the arm building the variant it builds, or as no word when no other arm
builds it, and the arm holds it to the row's last word.  A line of a reader
file comparing a word outside these functions is reported with each set the
module cannot read, and a function ``RUST_UNTAGGED`` reads past, which matches
a word at a place ``replyText`` has no row for, is a divergence once it has one.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import TYPE_CHECKING, NewType

from tools._reply_places import (
    REPO_ROOT,
    AnyNonEmpty,
    Arms,
    ReaderSets,
    ReplyPlace,
    ReplyWord,
    UnnamedLast,
    read_sets,
)

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection, Iterator
    from pathlib import Path

    from tools._reply_places import BindingReader

RUST_SOURCE = REPO_ROOT / "rust" / "src"
RUST_RESPONSE = RUST_SOURCE / "response.rs"
RUST_REPLY_SHAPE = RUST_SOURCE / "reply_shape.rs"
RUST_DECODE = RUST_SOURCE / "dbc" / "decode.rs"
# The files of the crate that read a reply's words.
RUST_READER_FILES = (RUST_RESPONSE, RUST_REPLY_SHAPE, RUST_DECODE)

# A name in the Rust crate: a function, an enum, a variant or a constant.
RustSymbol = NewType("RustSymbol", str)
# Rust source: a file, a function of it or a fragment of either.
RustText = NewType("RustText", str)
# The number of a line of a Rust file, from 1.
RustLine = NewType("RustLine", int)
# The index of a character of a Rust file, from 0.
RustOffset = NewType("RustOffset", int)
# A regular expression over Rust source.
RustRegex = NewType("RustRegex", str)


@dataclass(frozen=True)
class _RustMatch:
    """The string-literal arms of a function's one ``match word``, its last arm ``_``.

    The function takes the word first, as ``word: &str``, and uses it only as
    the match's scrutinee; each arm builds one variant of the type it returns,
    and the ``_`` arm reads as the word of an arm building the same variant.
    """

    module: Path
    function: RustSymbol


@dataclass(frozen=True)
class _RustUnread:
    """A function reading the word at a key once, into an unused binding, and comparing none.

    It takes every word, as a match whose one arm is ``_`` does.
    """

    module: Path
    function: RustSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _RustWordCall:
    """The literals a function's ``field_word`` calls at a key await."""

    module: Path
    function: RustSymbol
    key: ReplyWord


@dataclass(frozen=True)
class _RustEnumWords:
    """The words one method gives the variants of an enum declared once in the crate.

    A second word for a variant, or its word reached outside ``reader``, could
    stand for a word the method does not give, so the gate refuses, where it
    stands, a pattern of a variant outside ``words``, a reference to ``words``
    outside it and ``reader``, an import of the variants, an ``impl`` naming the
    enum other than the one holding ``words``, and an attribute on the enum or a
    variant other than a derive of traits that give no word.
    """

    module: Path
    enum: RustSymbol
    words: RustSymbol
    reader: RustSymbol


@dataclass(frozen=True)
class _RustBoundKinds:
    """The ``BOUND_KIND_*`` codes of ``rust/src/limits.rs``."""


type _RustSet = _RustMatch | _RustUnread | _RustWordCall | _RustEnumWords | _RustBoundKinds

# Every row of `replyText`, with the set the Rust reader takes at its place, read
# from the reader's own code, under the rules PYTHON_REPLY_TEXT is held to; a
# match's `_` arm, building a variant no other arm builds, reads the row's last
# word.
RUST_REPLY_TEXT: dict[ReplyPlace, _RustSet | AnyNonEmpty] = {
    ReplyPlace(place): spec
    for place, spec in {
        "status": _RustEnumWords(
            RUST_REPLY_SHAPE,
            RustSymbol("ReplyStatus"),
            RustSymbol("word"),
            RustSymbol("field_status"),
        ),
        "type": _RustWordCall(RUST_RESPONSE, RustSymbol("decode_frame"), ReplyWord("type")),
        "results/type": _RustUnread(
            RUST_RESPONSE, RustSymbol("read_property_event"), ReplyWord("type")
        ),
        "results/status <property>": _RustMatch(RUST_RESPONSE, RustSymbol("verdict")),
        "warnings/kind": _RustUnread(
            RUST_RESPONSE, RustSymbol("read_stream_warning"), ReplyWord("kind")
        ),
        "issues/severity": _RustMatch(RUST_RESPONSE, RustSymbol("severity")),
        "warnings/severity": _RustMatch(RUST_RESPONSE, RustSymbol("severity")),
        "bound_kind": _RustBoundKinds(),
        "dbc/messages/signals/byteOrder": _RustMatch(RUST_DECODE, RustSymbol("byte_order")),
        "dbc/messages/signals/presence": _RustMatch(RUST_DECODE, RustSymbol("presence")),
        "dbc/messages/signals/multiplexor": AnyNonEmpty(),
        "dbc/comments/target/kind": _RustMatch(RUST_DECODE, RustSymbol("comment_target")),
        "dbc/attributes/kind": _RustMatch(RUST_DECODE, RustSymbol("attribute")),
        "dbc/attributes/scope <definition>": _RustMatch(RUST_DECODE, RustSymbol("attr_scope")),
        "dbc/attributes/attrType/kind": _RustMatch(RUST_DECODE, RustSymbol("attr_type")),
        "dbc/attributes/value/kind": _RustMatch(RUST_DECODE, RustSymbol("attr_value")),
        "dbc/attributes/target/kind": _RustMatch(RUST_DECODE, RustSymbol("attr_target")),
    }.items()
}

# The functions of a reader file that match a word with literals at a place
# `replyText` has no row for, whose lines the gate reads past: an issue's code,
# a set that grows with the kernel's checks, read as unknown when unnamed.  A row
# `replyText` gains at the place is a divergence.
RUST_UNTAGGED: dict[ReplyPlace, tuple[Path, RustSymbol]] = {
    ReplyPlace("issues/code"): (RUST_RESPONSE, RustSymbol("from_wire")),
}


# Where a comment, a string, a raw string or a character literal may open; a
# quote that opens none is a lifetime's or a label's.
_RUST_OPENER = re.compile(r"//|/\*|[bc]?r#*\"|[bc]?\"|b?'")
_RUST_RAW = re.compile(r'[bc]?r(?P<hashes>#*)".*?"(?P=hashes)', flags=re.DOTALL)
_RUST_STRING = re.compile(r'[bc]?"(?:[^"\\]|\\.)*"', flags=re.DOTALL)
_RUST_CHAR = re.compile(r"b?'(?:[^'\\\n]|\\(?:x[0-9A-Fa-f]{2}|u\{[0-9A-Fa-f_]{1,8}\}|[^\n]))'")
_RUST_BLOCK_MARK = re.compile(r"/\*|\*/")
# An item compiled for the tests alone, and a test module in a file of its own.
_CFG_TEST = re.compile(r"#\[cfg\(test\)\]")
_TEST_MODULE = re.compile(r"#\[cfg\(test\)\]\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+(?P<name>\w+)\s*;")
# A comparison that could read a word, in source whose literals' text is
# blanked: `==` or `!=` beside a string literal, a string literal as a pattern
# (before `=>`, `|` or a guard, or after `let`), `matches!`, or a comparing call.
_RUST_WORD_COMPARISON = re.compile(
    r'[!=]=\s*&?\s*[bc]?r?#*"|"#*\s*(?:[!=]=|=>|\|(?!\|)|if\b)|\blet\s+[bc]?r?#*"|\bmatches!'
    + r"|\.(?:eq|ne|eq_ignore_ascii_case|starts_with|ends_with|strip_prefix|strip_suffix)\s*\("
)
# An arm's pattern of string literals joined by `|`, and one such literal.
_RUST_ARM_WORDS = re.compile(r'^"[^"\\]*"(?:\s*\|\s*"[^"\\]*")*$')
_RUST_WORD = re.compile(r'"(?P<word>[^"\\]*)"')
# A `field_word` call whose arguments hold no call of their own, and those
# arguments: the object and the path, the literal key and the borrowed words.
_RUST_WORD_CALL_HEAD = re.compile(r"\bfield_word\s*\(")
_RUST_WORD_CALL = re.compile(r"\bfield_word\s*\((?P<args>[^()]*)\)")
_RUST_WORD_CALL_ARGS = re.compile(
    r'^.*?,\s*"(?P<key>[^"\\]*)"\s*,\s*&\s*\[(?P<words>[^\[\]]*)\]\s*,?\s*$', flags=re.DOTALL
)
# An enum's declaration: the attributes before it, and its variants.
_RUST_ENUM = r"(?P<attributes>(?:#\[[^\]]*\]\s*)*)(?:pub(?:\([^)]*\))?\s+)?enum\s+{enum}\s*\{{"
# The uses of a match function's word: its parameter and the match's scrutinee.
_WORD_USES = 2
# The quotes of a string literal.
_QUOTES_PER_LITERAL = 2
# The traits an enum whose words one method gives may derive, none giving a word.
_WORDLESS_TRAITS = frozenset(
    {"Debug", "Clone", "Copy", "PartialEq", "Eq", "Hash", "PartialOrd", "Ord"}
)


@dataclass(frozen=True)
class _RustFile:
    """A file of the crate, its comments and test items blanked, then its literals' text too."""

    code: RustText
    hollow: RustText


@dataclass(frozen=True)
class _RustSpan:
    """Where a braced item stands in its file: its start, its opening brace and past its close."""

    start: RustOffset
    opening: RustOffset
    end: RustOffset


@dataclass(frozen=True)
class _RustArm:
    """An arm of a match: its pattern as written, and its body with its literals' text blanked."""

    pattern: RustText
    body: RustText


@dataclass(frozen=True)
class _ArmReading:
    """The words an arm's pattern names, none for ``_``, and the variant its body builds."""

    words: list[ReplyWord]
    variant: RustSymbol


@dataclass(frozen=True)
class _RustBreach:
    """A shape that could give a variant a second word or reach its word, and where it may stand.

    ``exempt`` and ``within`` are spans of the enum's module: the shape may
    stand in ``exempt``, and is looked for only in ``within`` when it is given.
    """

    regex: RustRegex
    what: Prose
    exempt: tuple[_RustSpan, ...]
    within: _RustSpan | None


# A line of a file of the crate.
type _RustSite = tuple[Path, RustLine]


def _shown(path: Path) -> Prose:
    """Return a path from the repository's root."""
    return Prose(str(path.relative_to(REPO_ROOT)))


def _blank(text: RustText) -> RustText:
    """Return text with every character but a line break blanked."""
    return RustText(re.sub(r"[^\n]", " ", text))


def _hollow_literal(literal: RustText) -> RustText:
    """Return a literal with its text blanked: a string's inside its quotes, a character's whole."""
    if not literal.endswith(('"', "#")):
        return _blank(literal)
    opening, closing = literal.index('"') + 1, literal.rindex('"')
    return RustText(
        literal[:opening] + _blank(RustText(literal[opening:closing])) + literal[closing:]
    )


def _rust_literal(text: RustText, start: RustOffset) -> RustText | None:
    """Return the string or character literal opening at ``start``, or None.

    A prefix letter after an identifier's character is that identifier's, and a
    quote no literal closes is a lifetime's or a label's.
    """
    before = text[start - 1] if start > 0 else " "
    if text[start] in "bcr" and (before.isalnum() or before == "_"):
        return None
    for literal in (_RUST_RAW, _RUST_STRING, _RUST_CHAR):
        if (found := literal.match(text, start)) is not None:
            return RustText(found.group())
    return None


def _comment_end(text: RustText, start: RustOffset) -> RustOffset:
    """Return where the comment opening at ``start`` ends, a block comment's nested ones in it."""
    if text.startswith("//", start):
        end = text.find("\n", start)
        return RustOffset(len(text) if end < 0 else end)
    depth = 0
    for mark in _RUST_BLOCK_MARK.finditer(text, start):
        depth += 1 if mark.group() == "/*" else -1
        if depth == 0:
            return RustOffset(mark.end())
    return RustOffset(len(text))


def _rust_strip(text: RustText) -> _RustFile:
    """Return Rust source with each comment blanked, and that with its literals' text blanked."""
    code: list[RustText] = []
    hollow: list[RustText] = []
    at = RustOffset(0)
    while (opener := _RUST_OPENER.search(text, at)) is not None:
        start = RustOffset(opener.start())
        code.append(RustText(text[at:start]))
        hollow.append(RustText(text[at:start]))
        if opener.group() in {"//", "/*"}:
            at = _comment_end(text, start)
            code.append(_blank(RustText(text[start:at])))
            hollow.append(_blank(RustText(text[start:at])))
        elif (literal := _rust_literal(text, start)) is not None:
            at = RustOffset(start + len(literal))
            code.append(literal)
            hollow.append(_hollow_literal(literal))
        else:
            at = RustOffset(start + 1)
            code.append(RustText(text[start]))
            hollow.append(RustText(text[start]))
    code.append(RustText(text[at:]))
    hollow.append(RustText(text[at:]))
    return _RustFile(RustText("".join(code)), RustText("".join(hollow)))


def _closing(hollow: RustText, opening: RustOffset) -> RustOffset:
    """Return the index of the brace closing the one at ``opening``, the text's end if none."""
    depth = 0
    for index in range(opening, len(hollow)):
        if hollow[index] == "{":
            depth += 1
        elif hollow[index] == "}":
            depth -= 1
            if depth == 0:
                return RustOffset(index)
    return RustOffset(len(hollow))


def _item_end(hollow: RustText, at: RustOffset) -> RustOffset:
    """Return where the item from ``at`` ends: past its first ``;`` or its body's closing brace."""
    depth = 0
    for index in range(at, len(hollow)):
        char = hollow[index]
        if char in "([":
            depth += 1
        elif char in ")]":
            depth -= 1
        elif depth == 0 and char == ";":
            return RustOffset(index + 1)
        elif depth == 0 and char == "{":
            return RustOffset(_closing(hollow, RustOffset(index)) + 1)
    return RustOffset(len(hollow))


def _without_tests(file: _RustFile) -> _RustFile:
    """Return a file with each ``#[cfg(test)]`` item blanked, its attribute included."""
    code, hollow = file.code, file.hollow
    while (attribute := _CFG_TEST.search(hollow)) is not None:
        start, end = attribute.start(), _item_end(hollow, RustOffset(attribute.end()))
        code = RustText(code[:start] + _blank(RustText(code[start:end])) + code[end:])
        hollow = RustText(hollow[:start] + _blank(RustText(hollow[start:end])) + hollow[end:])
    return _RustFile(code, hollow)


def _module_dir(path: Path) -> Path:
    """Return the directory a file's child modules live in."""
    return path.parent if path.name in {"lib.rs", "main.rs", "mod.rs"} else path.parent / path.stem


def _rust_package() -> dict[Path, _RustFile]:
    """Return every file of the crate's library outside its tests, each test item blanked."""
    files = {
        path: _rust_strip(RustText(path.read_text(encoding="utf-8")))
        for path in sorted(RUST_SOURCE.rglob("*.rs"))
    }
    tests = {
        _module_dir(path) / module.group("name")
        for path, file in files.items()
        for module in _TEST_MODULE.finditer(file.hollow)
    }
    return {
        path: _without_tests(file)
        for path, file in files.items()
        if "#![cfg(test)]" not in file.hollow
        and not any(path.with_suffix("") == test or test in path.parents for test in tests)
    }


def _line(file: _RustFile, offset: RustOffset) -> RustLine:
    """Return the number of the line an offset of a file stands on."""
    return RustLine(file.hollow.count("\n", 0, offset) + 1)


def _span_lines(file: _RustFile, span: _RustSpan) -> range:
    """Return the numbers of the lines a span of a file covers."""
    return range(_line(file, span.start), _line(file, RustOffset(span.end - 1)) + 1)


def _body_opening(hollow: RustText, at: RustOffset) -> RustOffset | None:
    """Return the opening brace of the body a signature from ``at`` heads, None if ``;`` ends it."""
    depth = 0
    for index in range(at, len(hollow)):
        char = hollow[index]
        if char in "([":
            depth += 1
        elif char in ")]":
            depth -= 1
        elif depth == 0 and char in "{;":
            return RustOffset(index) if char == "{" else None
    return None


def _rust_function(file: _RustFile, name: RustSymbol) -> _RustSpan | Prose | None:
    """Return where a function with a body is defined, None when none is, or why not once."""
    spans: list[_RustSpan] = []
    for head in re.finditer(rf"\bfn\s+{re.escape(name)}\s*[<(]", file.hollow):
        opening = _body_opening(file.hollow, RustOffset(head.end() - 1))
        if opening is not None:
            end = RustOffset(_closing(file.hollow, opening) + 1)
            spans.append(_RustSpan(RustOffset(head.start()), opening, end))
    if len(spans) > 1:
        return Prose(f"is defined {len(spans)} times, not once")
    return spans[0] if spans else None


def _skip_space(text: RustText, at: RustOffset) -> RustOffset:
    """Return the first index from ``at`` that holds no white space."""
    while at < len(text) and text[at].isspace():
        at = RustOffset(at + 1)
    return at


def _depth_zero(
    hollow: RustText, start: RustOffset, stop: RustOffset, token: RustText
) -> RustOffset | None:
    """Return where ``token`` first stands outside every bracket in ``start:stop``, or None."""
    depth = 0
    for index in range(start, stop):
        if depth == 0 and hollow.startswith(token, index):
            return RustOffset(index)
        if hollow[index] in "([{":
            depth += 1
        elif hollow[index] in ")]}":
            depth -= 1
    return None


def _arm_end(hollow: RustText, body: RustOffset, closing: RustOffset) -> RustOffset:
    """Return where an arm's body ends: past its block, or at the comma or brace closing it."""
    if hollow[body] == "{":
        return RustOffset(_closing(hollow, body) + 1)
    comma = _depth_zero(hollow, body, closing, RustText(","))
    return closing if comma is None else comma


def _arms(file: _RustFile, opening: RustOffset) -> list[_RustArm] | Prose:
    """Return the arms of the match whose braces open at ``opening``."""
    hollow, closing = file.hollow, _closing(file.hollow, opening)
    arms: list[_RustArm] = []
    at = RustOffset(opening + 1)
    while (start := _skip_space(hollow, at)) < closing:
        arrow = _depth_zero(hollow, start, closing, RustText("=>"))
        if arrow is None:
            return Prose(f"{file.code[start:closing].strip()!r} is no arm of its match")
        body = _skip_space(hollow, RustOffset(arrow + len("=>")))
        end = _arm_end(hollow, body, closing)
        arms.append(_RustArm(RustText(file.code[start:arrow].strip()), RustText(hollow[body:end])))
        after = _skip_space(hollow, end)
        at = RustOffset(after + 1) if hollow[after] == "," else after
    return arms


def _match_head(file: _RustFile, span: _RustSpan) -> tuple[RustSymbol, RustOffset] | Prose:
    """Return the type a match function returns and where its one match on ``word`` opens."""
    hollow = file.hollow[span.start : span.end]
    signature = file.hollow[span.start : span.opening]
    returned = re.search(r"->\s*(?:Result\s*<\s*)?(?P<type>[A-Z]\w*)", signature)
    held = re.search(r"\bmatch\s+word\s*\{", hollow)
    if re.search(r"\(\s*word\s*:\s*&(?:'\w+\s+)?str\s*[,)]", signature) is None:
        return Prose("does not take the word first, as word: &str")
    if returned is None or held is None or len(re.findall(r"\bmatch\b", hollow)) != 1:
        return Prose("is not one match on word returning a type of its own")
    if len(re.findall(r"\bword\b", hollow)) != _WORD_USES:
        return Prose("uses word other than to match on it")
    return RustSymbol(returned.group("type")), RustOffset(span.start + held.end() - 1)


def _arm_readings(arms: list[_RustArm], kind: RustSymbol) -> list[_ArmReading] | Prose:
    """Return each arm's words and the variant of ``kind`` it builds, the ``_`` arm's words none."""
    if not arms or arms[-1].pattern != "_":
        return Prose("its match's last arm is not _")
    readings: list[_ArmReading] = []
    for index, arm in enumerate(arms):
        built = [
            RustSymbol(variant.group("variant"))
            for variant in re.finditer(
                rf"\b{re.escape(kind)}\s*::\s*(?P<variant>[A-Z]\w*)", arm.body
            )
        ]
        last = index == len(arms) - 1
        if not last and _RUST_ARM_WORDS.match(arm.pattern) is None:
            return Prose(f"the arm {arm.pattern!r} is neither _ nor string literals joined by |")
        if len(built) != 1:
            return Prose(f"the arm {arm.pattern!r} builds {len(built)} variants of {kind}, not one")
        words = (
            [] if last else [ReplyWord(m.group("word")) for m in _RUST_WORD.finditer(arm.pattern)]
        )
        readings.append(_ArmReading(words, built[0]))
    return readings


def _match_arms(file: _RustFile, span: _RustSpan) -> Arms | Prose:
    """Return the words a function's match on ``word`` names and the word its ``_`` arm reads as.

    The ``_`` arm reads as the last word of the last arm building the variant it
    builds, and as no word when no other arm builds that variant.
    """
    head = _match_head(file, span)
    if isinstance(head, str):
        return head
    kind, opening = head
    arms = _arms(file, opening)
    readings = arms if isinstance(arms, str) else _arm_readings(arms, kind)
    if isinstance(readings, str):
        return readings
    words = [word for reading in readings for word in reading.words]
    if len(set(words)) != len(words):
        return Prose("its match names a word twice")
    if len(_RUST_WORD_COMPARISON.findall(file.hollow, span.start, span.end)) != len(words):
        return Prose("compares a word other than in its match's patterns")
    *named, last = readings
    sharing = [reading.words[-1] for reading in named if reading.variant == last.variant]
    return Arms(frozenset(words), sharing[-1] if sharing else UnnamedLast())


def _unread_arms(spec: _RustUnread, file: _RustFile, span: _RustSpan) -> Arms | Prose:
    """Return the empty arms of a function reading the word at its key into an unused binding."""
    code, hollow = file.code[span.start : span.end], file.hollow[span.start : span.end]
    read = rf'\bfield_string\(\s*\w+\s*,\s*\w+\s*,\s*"{re.escape(spec.key)}"\s*\)'
    reads = list(re.finditer(read, code))
    if len(reads) != 1:
        return Prose(f"reads {spec.key!r} with field_string {len(reads)} times, not once")
    held = re.search(r"\blet\s+(?P<name>_\w*)\s*=\s*\Z", code[: reads[0].start()])
    if held is None:
        return Prose(f"does not read the word at {spec.key!r} into a binding named from _")
    name = held.group("name")
    if name != "_" and len(re.findall(rf"\b{name}\b", hollow)) != 1:
        return Prose(f"uses {name} after reading it")
    if _RUST_WORD_COMPARISON.search(hollow) is not None:
        return Prose("compares a word with a literal")
    return Arms(frozenset(), UnnamedLast())


def _word_call_words(
    file: _RustFile, span: _RustSpan, key: ReplyWord
) -> frozenset[ReplyWord] | Prose:
    """Return the words a function's ``field_word`` calls at ``key`` await."""
    words: set[ReplyWord] = set()
    for at in _RUST_WORD_CALL_HEAD.finditer(file.hollow, span.start, span.end):
        call = _RUST_WORD_CALL.match(file.code, at.start())
        args = None if call is None else _RUST_WORD_CALL_ARGS.match(call.group("args"))
        if call is None or args is None:
            return Prose("a field_word call holds a call of its own, or no literal key and words")
        if args.group("key") != key:
            continue
        items = [item.strip() for item in args.group("words").split(",")]
        found = [_RUST_WORD.fullmatch(item) for item in (items[:-1] if not items[-1] else items)]
        if not found or None in found:
            return Prose(f"field_word({call.group('args')}) awaits a word that is not a literal")
        words |= {ReplyWord(word.group("word")) for word in found if word is not None}
    return frozenset(words) if words else Prose(f"no field_word call at {key!r}")


def _enum_variants(
    spec: _RustEnumWords, attributes: RustText, variants: RustText
) -> list[RustSymbol] | Prose:
    """Return an enum's variants, or why the enum or a variant could carry a word unread."""
    for attribute in re.finditer(r"#\[(?P<body>[^\]]*)\]", attributes):
        derived = re.fullmatch(r"derive\((?P<traits>[^()]*)\)", attribute.group("body").strip())
        traits = [] if derived is None else derived.group("traits").split(",")
        if derived is None or any(t.strip() not in _WORDLESS_TRAITS | {""} for t in traits):
            return Prose(f"#[{attribute.group('body')}] on {spec.enum} could give it a word")
    named = [variant.strip() for variant in variants.split(",") if variant.strip()]
    if any(re.fullmatch(r"[A-Z]\w*", variant) is None for variant in named):
        return Prose(f"a variant of {spec.enum} is not a unit variant without an attribute")
    return [RustSymbol(variant) for variant in named]


def _given_words(
    spec: _RustEnumWords, module: _RustFile, giver: _RustSpan, variants: list[RustSymbol]
) -> frozenset[ReplyWord] | Prose:
    """Return the word a method's one match on ``self`` gives each variant, or why it cannot."""
    code, hollow = module.code[giver.opening : giver.end], module.hollow[giver.opening : giver.end]
    enum = re.escape(spec.enum)
    arms = list(
        re.finditer(rf'\b(?:{enum}|Self)\s*::\s*(?P<variant>\w+)\s*=>\s*"(?P<word>[^"\\]*)"', code)
    )
    shaped = (
        len(re.findall(r"\bmatch\b", hollow)) == 1
        and re.search(r"\bmatch\s+self\s*\{", hollow) is not None
        and re.search(r"\breturn\b", hollow) is None
        and hollow.count("=>") == len(arms)
        and hollow.count('"') == _QUOTES_PER_LITERAL * len(arms)
    )
    if not shaped:
        return Prose("its body is not one match on self, each arm one variant giving one literal")
    words = [ReplyWord(arm.group("word")) for arm in arms]
    given = sorted(arm.group("variant") for arm in arms)
    if given != sorted(variants) or len(set(words)) != len(words):
        return Prose(f"its arms do not give each variant of {spec.enum} its own word")
    return frozenset(words)


def _holding_impl(file: _RustFile, enum: RustSymbol, giver: _RustSpan) -> _RustSpan | None:
    """Return the ``impl`` naming ``enum`` that holds ``giver``, None when none does."""
    for head in re.finditer(rf"\bimpl\b[^{{;]*\b{re.escape(enum)}\b[^{{;]*\{{", file.hollow):
        opening = RustOffset(head.end() - 1)
        span = _RustSpan(
            RustOffset(head.start()), opening, RustOffset(_closing(file.hollow, opening) + 1)
        )
        if span.opening < giver.start < span.end:
            return span
    return None


def _enum_breach_shapes(
    spec: _RustEnumWords, giver: _RustSpan, reader: _RustSpan, holder: _RustSpan
) -> tuple[_RustBreach, ...]:
    """Return the shapes that could give a variant a second word or reach its word elsewhere."""
    enum, words = re.escape(spec.enum), re.escape(spec.words)
    pattern = r"\s*::\s*\w+\s*(?:=>|\|(?!\|)|if\b)"
    reach = Prose(f"reaches {spec.words} outside {spec.reader}")
    second = Prose(
        f"matches on a {spec.enum} outside {spec.words}, which could give it a second word"
    )
    return (
        _RustBreach(RustRegex(rf"(?:\.|\b{enum}\s*::)\s*{words}\b"), reach, (giver, reader), None),
        _RustBreach(RustRegex(rf"\bSelf\s*::\s*{words}\b"), reach, (giver, reader), holder),
        _RustBreach(RustRegex(rf"\b{enum}{pattern}"), second, (giver,), None),
        _RustBreach(RustRegex(rf"\bSelf{pattern}"), second, (giver,), holder),
        _RustBreach(
            RustRegex(rf"\b{enum}\s*::\s*[{{*]"),
            Prose(f"imports the variants of {spec.enum}, which a pattern could name bare"),
            (),
            None,
        ),
        _RustBreach(
            RustRegex(rf"\bimpl\b[^{{;]*\b{enum}\b"),
            Prose(f"implements for {spec.enum} beside the impl holding {spec.words}"),
            (holder,),
            None,
        ),
    )


def _excused(shape: _RustBreach, at: RustOffset) -> bool:
    """Whether a shape standing at an offset of the enum's module is one the gate allows there."""
    if shape.within is not None and not shape.within.start <= at < shape.within.end:
        return True
    return any(span.start <= at < span.end for span in shape.exempt)


def _enum_word_breaches(
    spec: _RustEnumWords, package: dict[Path, _RustFile], giver: _RustSpan
) -> Iterator[Prose]:
    """Yield each line that could give a variant a second word or reach its word elsewhere."""
    module = package[spec.module]
    reader = _rust_function(module, spec.reader)
    holder = _holding_impl(module, spec.enum, giver)
    if not isinstance(reader, _RustSpan) or holder is None:
        yield Prose(
            f"{_shown(spec.module)}: {spec.reader} is not defined once, "
            + f"or {spec.words} is no method of an impl of {spec.enum}"
        )
        return
    shapes = _enum_breach_shapes(spec, giver, reader, holder)
    for path, file in package.items():
        shown = file.code.split("\n")
        for shape in shapes:
            if shape.within is not None and path != spec.module:
                continue
            for hit in re.finditer(shape.regex, file.hollow):
                if path != spec.module or not _excused(shape, RustOffset(hit.start())):
                    number = _line(file, RustOffset(hit.start()))
                    yield Prose(
                        f"{_shown(path)}:{number}: {shown[number - 1].strip()!r} {shape.what}"
                    )


def _rust_enum_words(
    spec: _RustEnumWords, package: dict[Path, _RustFile]
) -> frozenset[ReplyWord] | Prose:
    """Return the word a method gives each variant of an enum, or each line that hides them."""
    where = f"{_shown(spec.module)}:{spec.enum}::{spec.words}"
    declaration = re.compile(
        _RUST_ENUM.format(enum=re.escape(spec.enum)) + r"(?P<variants>[^{}]*)\}"
    )
    declared = [
        (path, found)
        for path, file in package.items()
        for found in declaration.finditer(file.hollow)
    ]
    if [path for path, _ in declared] != [spec.module]:
        return Prose(f"{spec.enum} is not declared once, in {_shown(spec.module)}")
    found = declared[0][1]
    variants = _enum_variants(
        spec, RustText(found.group("attributes")), RustText(found.group("variants"))
    )
    giver = _rust_function(package[spec.module], spec.words)
    if isinstance(variants, str) or not isinstance(giver, _RustSpan):
        return Prose(f"{where}: {variants if isinstance(variants, str) else 'not defined once'}")
    words = _given_words(spec, package[spec.module], giver, variants)
    if isinstance(words, str):
        return Prose(f"{where}: {words}")
    breaches = list(dict.fromkeys(_enum_word_breaches(spec, package, giver)))
    return Prose("; ".join(breaches)) if breaches else words


def _rust_words(
    spec: _RustSet, rust_codes: frozenset[ReplyWord], package: dict[Path, _RustFile]
) -> frozenset[ReplyWord] | Arms | Prose:
    """Return a Rust reader set's words and last arm, or why the gate cannot read them."""
    if isinstance(spec, _RustBoundKinds):
        return rust_codes
    if isinstance(spec, _RustEnumWords):
        return _rust_enum_words(spec, package)
    where = f"{_shown(spec.module)}:{spec.function}"
    file = package.get(spec.module)
    span = None if file is None else _rust_function(file, spec.function)
    if file is None or not isinstance(span, _RustSpan):
        return Prose(f"{where} {span or 'is not defined'}")
    if isinstance(spec, _RustMatch):
        found = _match_arms(file, span)
    elif isinstance(spec, _RustUnread):
        found = _unread_arms(spec, file, span)
    else:
        found = _word_call_words(file, span, spec.key)
    return Prose(f"{where}: {found}") if isinstance(found, str) else found


def _function_sites(
    package: dict[Path, _RustFile], module: Path, function: RustSymbol
) -> frozenset[_RustSite] | None:
    """Return the lines a function of a file spans, None when the file does not define it once."""
    file = package.get(module)
    span = None if file is None else _rust_function(file, function)
    if file is None or not isinstance(span, _RustSpan):
        return None
    return frozenset((module, RustLine(number)) for number in _span_lines(file, span))


def _rust_reader_breaches(package: dict[Path, _RustFile]) -> Iterator[Prose]:
    """Yield each line of a reader file comparing a word outside the functions the gate reads.

    Those are the functions ``RUST_REPLY_TEXT`` names a match or an unread word
    in, which the gate reads, and those ``RUST_UNTAGGED`` names, which it reads past.
    """
    read = {
        (spec.module, spec.function)
        for spec in RUST_REPLY_TEXT.values()
        if isinstance(spec, _RustMatch | _RustUnread)
    }
    exempt: set[_RustSite] = set()
    for module, function in sorted(read | set(RUST_UNTAGGED.values())):
        sites = _function_sites(package, module, function)
        if sites is None and (module, function) not in read:
            yield Prose(f"RUST_UNTAGGED names {_shown(module)}:{function}, not defined once")
        exempt |= sites or frozenset()
    for path in RUST_READER_FILES:
        file = package.get(path)
        if file is None:
            yield Prose(f"{_shown(path)} is no file of the crate's library")
            continue
        shown = file.code.split("\n")
        hits = {
            _line(file, RustOffset(hit.start()))
            for hit in _RUST_WORD_COMPARISON.finditer(file.hollow)
        }
        for number in sorted(hits - {line for module, line in exempt if module == path}):
            yield Prose(
                f"{_shown(path)}:{number}: {shown[number - 1].strip()!r} "
                + "compares a word outside the matches RUST_REPLY_TEXT names"
            )


def rust_untagged_rows(rows: Collection[ReplyPlace]) -> list[Prose]:
    """Return a divergence for each place ``RUST_UNTAGGED`` reads past that ``replyText`` has."""
    return [
        Prose(
            f"reply place {place}: replyText has a row, so {_shown(module)}:{function}, "
            + "which RUST_UNTAGGED reads past, reads a tag place; name it in RUST_REPLY_TEXT"
        )
        for place, (module, function) in RUST_UNTAGGED.items()
        if place in rows
    ]


def rust_reader(rust_codes: frozenset[ReplyWord]) -> BindingReader:
    """Return the Rust reader, whose bound kinds are ``rust_codes``.

    It adds each line of a reader file that could read a tag word outside its
    sets to the places none reads.
    """

    def read(unread: list[Prose]) -> ReaderSets:
        package = _rust_package()
        sets = read_sets(
            Prose("the Rust reader"),
            Prose("RUST_REPLY_TEXT"),
            RUST_REPLY_TEXT,
            lambda spec: _rust_words(spec, rust_codes, package),
            unread,
        )
        unread.extend(_rust_reader_breaches(package))
        return sets

    return read

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads the Rust crate's library, and nothing else, through its grammar.

A reader file's line comparing a word outside the lines its rows read and the
matches of the functions ``RUST_UNTAGGED`` names is reported at its line, shown
with its comments blanked; an item ``#[cfg(test)]`` marks and a file holding
``#![cfg(test)]`` are no part of the library, a ``#[test]`` function outside
such an item is, and the library's files are read in their paths' order.  A
line tree-sitter-rust cannot parse is refused there and the gate exits 2,
whatever else it reads, an escape the grammar refuses included: it cannot read
the ``_`` Rust allows among a Unicode escape's digits.  ``RUST_UNTAGGED``
naming a function its file does not define, a reader file the crate lacks and a
place it reads past that ``replyText`` has a row for are reported.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal, NewType

import pytest
from _rust_reply_gate import UNPARSED, line_of, planted_in, unparsed

from tools import check_limits_parity
from tools._reply_places import REPO_ROOT, ReplyPlace
from tools._reply_places_rust import (
    RUST_DECODE,
    RUST_RESPONSE,
    RUST_UNTAGGED,
    RustLine,
    RustSymbol,
    RustText,
    rust_read_sites,
    rust_reader,
    rust_untagged_rows,
)

from aletheia.common_types import Prose

# The index of a line of a stray reader's body, from 0.
_BodyLine = NewType("_BodyLine", int)

# The function of the Rust responses no row names that a stray reader is
# planted before, the stray's name, and a line of its body comparing a word.
_ANCHOR = RustText("fn is_ack(")
_STRAY = RustSymbol("stray_reader")
_HOLDS = RustText('if word == "holds" {}')
_CLOSE = RustText("}")
_NONE = RustText("")


def _with_stray(
    monkeypatch: pytest.MonkeyPatch, body: tuple[RustText, ...], before: RustText = _NONE
) -> list[Prose]:
    """Return what the gate reports with a stray reader holding ``body`` planted.

    The function stands before the anchor, ``before`` opening it, each line of
    ``body`` one of its own, its first right after the function's opening line.
    """
    lines = "".join(f"    {line}\n" for line in body)
    stray = RustText(f"{before}fn {_STRAY}(word: &str) {{\n{lines}}}\n\n{_ANCHOR}")
    return planted_in(monkeypatch, RUST_RESPONSE, _ANCHOR, stray)


def _stray_line(at: _BodyLine = _BodyLine(0), before: RustText = _NONE) -> RustLine:
    """Return the number the line at ``at`` of a stray's body stands at, ``before`` opening it."""
    return RustLine(line_of(RUST_RESPONSE, _ANCHOR) + before.count("\n") + 1 + at)


def _breach(number: RustLine, line: RustText, path: Path = RUST_RESPONSE) -> Prose:
    """Return the gate's report of a word ``line`` compares at ``number`` of ``path``."""
    return Prose(
        f"{path.relative_to(REPO_ROOT)}:{number}: {line.strip()!r} "
        + "compares a word outside the lines RUST_REPLY_TEXT reads"
    )


def _compared(found: list[Prose]) -> list[Prose]:
    """Return each report of a line comparing a word."""
    return [each for each in found if "compares a word outside" in each]


def _refused(line: RustText) -> Prose:
    """Return the gate's refusal of ``line``, the first of a stray's body, as unparsed."""
    return Prose(f"rust/src/response.rs:{_stray_line()}: {line!r} {UNPARSED}")


@pytest.mark.parametrize(
    "line",
    [
        pytest.param(RustText("if word == {}"), id="an operand missing"),
        pytest.param(RustText("let _ = len(word;"), id="a parenthesis missing"),
        pytest.param(RustText(r"if c == '\u{6_8}' {}"), id="a char's escape with an underscore"),
        *(
            pytest.param(RustText(f'if word == "{text}" {{}}'), id=f"== {text}")
            for text in (
                r"\u{6_8}olds",
                r"\x6",
                r"\u{_2d}",
                r"\u{}",
                r"\u{2_d}",
                r"\u{2__d}",
                r"\u{2d_}",
            )
        ),
    ],
)
def test_a_line_the_grammar_cannot_parse_is_refused_at_it(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose], line: RustText
) -> None:
    """A file holding a line tree-sitter-rust cannot parse is refused there, and the gate exits 2.

    A refused escape can leave the grammar misreading the lines after it, which
    are refused too; the first refused is the line planted.
    """
    refusal = _refused(line)
    assert unparsed(_with_stray(monkeypatch, (line,)))[:1] == [refusal]
    monkeypatch.setattr("sys.argv", ["check_limits_parity"])
    assert check_limits_parity.main() == 2
    assert f"check-limits-parity: {refusal}\n" in capsys.readouterr().err


def test_a_stray_bracket_ends_a_comparing_calls_arguments(monkeypatch: pytest.MonkeyPatch) -> None:
    """A ``]`` ends a comparing call's arguments as ``)`` does, on a line the grammar refuses.

    The call reads a literal holding no word up to the stray ``]``, so compares
    none: the line is refused unparsed and no comparison is reported.
    """
    line = RustText('if word.eq("" ]) {}')
    found = _with_stray(monkeypatch, (line,))
    assert unparsed(found)[:1] == [_refused(line)]
    assert _compared(found) == []


@pytest.mark.parametrize(
    ("before", "after"),
    [
        pytest.param(
            RustText("#[cfg(test)]\n#[allow(dead_code)]\n"), _NONE, id="another attribute after"
        ),
        pytest.param(RustText("#[cfg(test)]\n/// A stray.\n"), _NONE, id="a doc comment after"),
        pytest.param(
            RustText('#[cfg(test)]\n#[doc = matches!(word, "holds")]\n'),
            _NONE,
            id="an attribute comparing a word after",
        ),
        pytest.param(RustText("#[cfg(test)]\nmod stray {\n"), RustText("}\n"), id="a module"),
    ],
)
def test_a_word_compared_in_an_item_compiled_for_the_tests_is_read_past(
    monkeypatch: pytest.MonkeyPatch, before: RustText, after: RustText
) -> None:
    """An item ``#[cfg(test)]`` marks, an attribute or a comment between, is no breach."""
    stray = RustText(f"{before}fn {_STRAY}(word: &str) {{\n    {_HOLDS}\n}}\n{after}\n{_ANCHOR}")
    found = planted_in(monkeypatch, RUST_RESPONSE, _ANCHOR, stray)
    assert unparsed(found) == []
    assert _compared(found) == []


@pytest.mark.parametrize(
    "before",
    [
        pytest.param(RustText("#[cfg(not(test))]\n"), id="an item compiled outside the tests"),
        pytest.param(RustText("#[test]\n"), id="a test function outside a test module"),
        pytest.param(RustText("#[cfg( test )]\n"), id="a test attribute written spaced"),
    ],
)
def test_a_word_compared_in_an_item_of_the_library_is_reported(
    monkeypatch: pytest.MonkeyPatch, before: RustText
) -> None:
    """An item no ``#[cfg(test)]`` marks is part of the library, a ``#[test]`` function too."""
    found = _with_stray(monkeypatch, (_HOLDS,), before)
    assert found == [_breach(_stray_line(before=before), _HOLDS)]


def test_a_reader_file_compiled_for_the_tests_alone_is_no_file_of_the_library(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A reader file holding ``#![cfg(test)]`` is read as no file of the crate's library."""
    found = planted_in(monkeypatch, RUST_RESPONSE, _ANCHOR, RustText(f"#![cfg(test)]\n{_ANCHOR}"))
    assert Prose("rust/src/response.rs is no file of the crate's library") in found


# A line tree-sitter-rust cannot parse, and the files of a crate declaring a
# module in a directory of its own, each holding that line first, the module's
# file declaring a child module.
_BROKEN = RustText("fn stray(word: &str) { if word == {} }")
_MODULE_FILES = {
    Path("planted/mod.rs"): RustText(f"{_BROKEN}\nmod inner;\n"),
    Path("planted/inner.rs"): RustText(f"{_BROKEN}\n"),
}


@pytest.mark.parametrize(
    ("declared", "refused"),
    [
        pytest.param(RustText("#[cfg(test)]\nmod planted;\n"), (), id="a test module"),
        pytest.param(
            RustText("mod planted;\n"),
            (Path("planted/inner.rs"), Path("planted/mod.rs")),
            id="a module of the library",
        ),
    ],
)
def test_a_test_modules_directory_is_no_part_of_the_library(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    declared: RustText,
    refused: tuple[Path, ...],
) -> None:
    """The files in a test module's directory are no part of the library, a library module's are.

    The crate is ``lib.rs`` declaring the module and the module's files alone.
    """
    unread = _read_crate(monkeypatch, tmp_path, {Path("lib.rs"): declared, **_MODULE_FILES})
    assert unparsed(unread) == [
        Prose(f"rust/src/{path.as_posix()}:1: {_BROKEN!r} {UNPARSED}") for path in refused
    ]


@dataclass(frozen=True)
class _ListedBackwards:
    """A crate's source directory whose files are listed in reverse path order."""

    source: Path

    def rglob(self, pattern: Literal["*.rs"]) -> list[Path]:
        """Return the files under the directory that ``pattern`` matches, in reverse path order."""
        return sorted(self.source.rglob(pattern), reverse=True)


def _read_crate(
    monkeypatch: pytest.MonkeyPatch,
    root: Path,
    files: dict[Path, RustText],
    *,
    backwards: bool = False,
) -> list[Prose]:
    """Return what the Rust reader adds to the places none reads, over a crate of ``files`` alone.

    The crate's source directory is ``rust/src`` under ``root``, its files
    listed in reverse path order when ``backwards``; the gate reads no row and
    no reader file in it.
    """
    source = root / "rust" / "src"
    for path, text in files.items():
        (source / path).parent.mkdir(parents=True, exist_ok=True)
        (source / path).write_text(text, encoding="utf-8")
    monkeypatch.setattr("tools._reply_places_rust.REPO_ROOT", root)
    listed = _ListedBackwards(source) if backwards else source
    monkeypatch.setattr("tools._reply_places_rust.RUST_SOURCE", listed)
    monkeypatch.setattr("tools._reply_places_rust.RUST_REPLY_TEXT", {})
    monkeypatch.setattr("tools._reply_places_rust.RUST_UNTAGGED", {})
    monkeypatch.setattr("tools._reply_places_rust.RUST_READER_FILES", ())
    unread: list[Prose] = []
    rust_reader(frozenset())(unread)
    return unread


def test_the_crates_files_are_read_in_their_paths_order(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """The library's files are read in their paths' order, whatever order they are listed in."""
    names = ("a.rs", "b.rs", "lib.rs")
    files = {Path(name): RustText(f"{_BROKEN}\n") for name in names}
    assert unparsed(_read_crate(monkeypatch, tmp_path, files, backwards=True)) == [
        Prose(f"rust/src/{name}:1: {_BROKEN!r} {UNPARSED}") for name in names
    ]


def test_a_comparison_in_a_mapping_is_read_with_it(monkeypatch: pytest.MonkeyPatch) -> None:
    """A word compared in the function a mapped row maps with is refused there, and no breach."""
    holds = RustText('"holds" => Verdict::Holds,')
    compared = RustText('"holds" => { if word == "fails" {} Verdict::Holds }')
    found = planted_in(monkeypatch, RUST_RESPONSE, holds, compared)
    assert unparsed(found) == []
    assert _compared(found) == []


def test_a_comparison_in_a_mapped_rows_caller_is_reported(monkeypatch: pytest.MonkeyPatch) -> None:
    """A mapped row reads its mapping's lines, not the lines of the function calling it."""
    index = RustText('let property_index = field_natural(result, path, "property_index")?;')
    stray = RustText('if path == "results" {}')
    found = planted_in(monkeypatch, RUST_RESPONSE, index, RustText(f"{index}\n    {stray}"))
    assert _compared(found) == [_breach(RustLine(line_of(RUST_RESPONSE, index) + 1), stray)]


@pytest.mark.parametrize(
    ("path", "head", "stray"),
    [
        pytest.param(
            RUST_DECODE,
            RustText("fn byte_order(word: &str) -> ByteOrder {"),
            _HOLDS,
            id="a match row's function",
        ),
        pytest.param(
            RUST_RESPONSE,
            RustText("fn verdict(word: &str) -> Verdict {"),
            _HOLDS,
            id="a mapped row's mapping",
        ),
        pytest.param(
            RUST_RESPONSE,
            RustText("pub fn from_wire(s: &str) -> Option<Self> {"),
            RustText('if s == "holds" {}'),
            id="a function RUST_UNTAGGED names",
        ),
    ],
)
def test_a_comparison_before_the_match_a_function_is_read_at_is_reported(
    monkeypatch: pytest.MonkeyPatch, path: Path, head: RustText, stray: RustText
) -> None:
    """A row, or ``RUST_UNTAGGED``, reads its function's match, not the line before it."""
    found = planted_in(monkeypatch, path, head, RustText(f"{head}\n    {stray}"))
    assert _compared(found) == [_breach(RustLine(line_of(path, head) + 1), stray, path)]


def _spans(path: Path, heads: tuple[RustText, ...]) -> set[RustLine]:
    """Return the lines of ``path`` from each line a head opens to the next indented as it is."""
    lines = path.read_text(encoding="utf-8").split("\n")
    indents = [len(line) - len(line.lstrip()) if line.strip() else -1 for line in lines]
    spans: set[RustLine] = set()
    for at, line in enumerate(lines):
        if line.strip().startswith(heads):
            end = indents.index(indents[at], at + 1)
            spans |= {RustLine(number) for number in range(at + 1, end + 2)}
    return spans


def test_the_rows_record_the_lines_they_read() -> None:
    """A row reads its match, or its mapping's and its call's; from_wire's match is read past."""
    match = RustText("match word {")
    calls = (
        RustText('let severity = severity(field_word(issue, path, "severity"'),
        RustText('let status = field_word(result, path, "status"'),
    )
    responses = _spans(RUST_RESPONSE, (match, RustText("Some(match s {"))) | {
        line_of(RUST_RESPONSE, call) for call in calls
    }
    heads = (
        match,
        RustText("byte_order: byte_order(field_word("),
        RustText("let kind = field_word("),
    )
    decoded = _spans(RUST_DECODE, heads) | {
        line_of(RUST_DECODE, RustText('field_word(signal, path, "presence"'))
    }
    assert rust_read_sites() == {(RUST_DECODE, line) for line in decoded} | {
        (RUST_RESPONSE, line) for line in responses
    }


def test_a_function_rust_untagged_names_is_read_past_at_its_match(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A word compared in the match of a function ``RUST_UNTAGGED`` names is no breach."""
    untagged = {**RUST_UNTAGGED, ReplyPlace("stray"): (RUST_RESPONSE, _STRAY)}
    monkeypatch.setattr("tools._reply_places_rust.RUST_UNTAGGED", untagged)
    arms = (RustText("match word {"), RustText('"fails" => {}'), RustText("_ => {}"), _CLOSE)
    found = _with_stray(monkeypatch, (_HOLDS, *arms))
    assert _compared(found) == [_breach(_stray_line(), _HOLDS)]


def test_a_function_rust_untagged_names_and_no_file_defines_is_reported(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``RUST_UNTAGGED`` naming a function its file does not define is reported."""
    untagged = {ReplyPlace("issues/code"): (RUST_RESPONSE, RustSymbol("no_such_reader"))}
    monkeypatch.setattr("tools._reply_places_rust.RUST_UNTAGGED", untagged)
    assert Prose(
        "RUST_UNTAGGED names rust/src/response.rs:no_such_reader, not defined once"
    ) in planted_in(monkeypatch, RUST_RESPONSE, _ANCHOR, _ANCHOR)


def test_a_mapping_no_file_defines_is_reported_at_its_place_alone(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A mapping a row reads and no file defines is named at the row's place, not as untagged."""
    found = planted_in(monkeypatch, RUST_RESPONSE, RustText("fn verdict("), RustText("fn of("))
    assert (
        Prose(
            "reply place results/status <property>: "
            + "rust/src/response.rs:read_verdict: verdict is not defined"
        )
        in found
    )
    assert [each for each in found if each.startswith("RUST_UNTAGGED")] == []


def test_a_reader_file_the_crate_lacks_is_reported_and_the_rest_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A reader file the library does not hold is reported, and the files after it still read."""
    missing = RUST_RESPONSE.with_name("no_such_reader.rs")
    monkeypatch.setattr("tools._reply_places_rust.RUST_READER_FILES", (missing, RUST_RESPONSE))
    found = _with_stray(monkeypatch, (_HOLDS,))
    assert Prose("rust/src/no_such_reader.rs is no file of the crate's library") in found
    assert _breach(_stray_line(), _HOLDS) in found


def test_the_lines_comparing_a_word_are_reported_in_their_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A comparing call and an ``==`` on the line after it are reported in their lines' order."""
    body = (RustText("let _ = word.starts_with(prefix);"), _HOLDS)
    breaches = [_breach(_stray_line(_BodyLine(at)), body[at]) for at in (0, 1)]
    assert _compared(_with_stray(monkeypatch, body)) == breaches


def test_a_comparison_is_shown_without_its_comment(monkeypatch: pytest.MonkeyPatch) -> None:
    """A reported line is shown as its code reads, a comment on it blanked."""
    found = _with_stray(monkeypatch, (RustText(f"{_HOLDS} // the one word"),))
    assert _compared(found) == [_breach(_stray_line(), _HOLDS)]


# A place `replyText` has a row for, and a function of the Rust responses no row reads.
_ROWED = ReplyPlace("status")
_PASSED = RustSymbol("decode_success")


def test_a_place_rust_untagged_reads_past_is_a_divergence_once_reply_text_has_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``RUST_UNTAGGED`` naming a place ``replyText`` has a row for is named; another is not."""
    passed = {**RUST_UNTAGGED, _ROWED: (RUST_RESPONSE, _PASSED)}
    monkeypatch.setattr("tools._reply_places_rust.RUST_UNTAGGED", passed)
    divergence = Prose(
        "reply place status: replyText has a row, so rust/src/response.rs:decode_success, "
        + "which RUST_UNTAGGED reads past, reads a tag place; name it in RUST_REPLY_TEXT"
    )
    assert rust_untagged_rows([_ROWED, ReplyPlace("type")]) == [divergence]
    assert rust_untagged_rows([ReplyPlace("type")]) == []


def test_the_gate_reports_a_place_rust_untagged_reads_past_that_reply_text_has(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate exits 1 naming a ``RUST_UNTAGGED`` place ``replyText`` has a row for."""
    passed = {**RUST_UNTAGGED, _ROWED: (RUST_RESPONSE, _PASSED)}
    monkeypatch.setattr("tools._reply_places_rust.RUST_UNTAGGED", passed)
    monkeypatch.setattr("sys.argv", ["check_limits_parity"])
    assert check_limits_parity.main() == 1
    assert "which RUST_UNTAGGED reads past, reads a tag place" in capsys.readouterr().err

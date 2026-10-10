# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_docs``, the documentation gate, and the readers its arms share.

The gate reads every tracked Markdown file once and runs every arm over the
same texts: these tests hold the reading, the order the arms' findings come
in, the exit status, the registry of arms, and the tracked-file, heading,
directory, paragraph and destination readers in ``tools/docs_arms/__init__.py``
and the prose reader in ``tools/_common.py`` they rest on. Each
arm's own claim is tested in ``python/tests/test_docs_arm_<arm>.py``.
"""

from __future__ import annotations

import pkgutil
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant

from tools import check_docs, docs_arms
from tools._common import RelPath, prose_lines
from tools.check_docs import ARMS, check_tree, main, read_documents
from tools.docs_arms import (
    Unread,
    destination,
    header_slugs,
    headings,
    missing,
    paragraphs,
    read_tracked,
    read_tracked_bytes,
    slug,
    tracked_dirs,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    from tools.docs_arms import Arm


def test_slug_turns_each_whitespace_character_into_one_hyphen() -> None:
    """GitHub's slug keeps a run of spaces as a run of hyphens, punctuation dropped."""
    assert slug(Prose("Change Detection & Stability")) == "change-detection--stability"
    assert slug(Prose("Path 1 (Excel + CLI)")) == "path-1-excel--cli"
    assert slug(Prose("See [the guide](x.md)")) == "see-the-guide"


def test_headings_skip_fenced_code_and_keep_code_spans() -> None:
    """A heading-shaped line in a fence is code; a code span stays in the heading's text."""
    text = Prose("# One\n```\n# Not a heading\n```\n## Two `code` ##\n")
    assert headings(text) == [Prose("One"), Prose("Two `code`")]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("#\tTitle\n"), [Prose("Title")]),
        (Prose("#\u00a0Title\n"), list[Prose]()),
        (Prose("#\n"), [Prose("")]),
    ],
    ids=["tab", "no-break-space", "run-alone"],
)
def test_a_hash_run_opens_a_heading_before_a_space_a_tab_or_the_line_end(
    text: Prose, expected: list[Prose]
) -> None:
    """A run opens a heading before a space, a tab or the line's end, never a no-break space."""
    assert headings(text) == expected


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("##  \tTitle \t##  \n"), [Prose("Title")]),
        (Prose("# \u00a0Title\n"), [Prose("\u00a0Title")]),
        (Prose("# Title\u00a0\n"), [Prose("Title\u00a0")]),
    ],
    ids=["spaces-and-tabs", "leading-no-break-space", "trailing-no-break-space"],
)
def test_only_spaces_and_tabs_around_a_headings_text_are_dropped(
    text: Prose, expected: list[Prose]
) -> None:
    """Spaces and tabs around the text and a closing run are dropped; a no-break space stays."""
    assert headings(text) == expected


def test_a_repeated_heading_takes_githubs_numbered_suffixes() -> None:
    """The first copy keeps the slug; each later one adds -1, -2 in order."""
    text = Prose("# Same\n## Same\n### Same\n")
    assert header_slugs(text) == {Prose("same"), Prose("same-1"), Prose("same-2")}


def test_an_html_name_or_id_is_an_anchor_too() -> None:
    """Explicit name= and id= attributes are anchors beside the headings' slugs."""
    text = Prose('# Top\n<a name="kept"></a> <span id="also-kept"></span>\n')
    assert header_slugs(text) == {Prose("top"), Prose("kept"), Prose("also-kept")}


def test_tracked_dirs_are_every_directory_on_the_way_to_a_file() -> None:
    """Each proper prefix of a tracked path, and neither the file nor the empty path."""
    assert tracked_dirs([RelPath("a/b/c.md"), RelPath("top.md")]) == {RelPath("a"), RelPath("a/b")}


@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        (Prose('x.md "Title"'), Prose("x.md")),
        (Prose("x.md\t'Title'"), Prose("x.md")),
        (Prose("x.md\n(Title)"), Prose("x.md")),
        (Prose(" \t\nx.md"), Prose("x.md")),
        (Prose('\u00a0g\u00a0b.md "Title"'), Prose("\u00a0g\u00a0b.md")),
        (Prose(" \t\n"), Prose("")),
        (Prose(""), Prose("")),
    ],
    ids=["space", "tab", "line-break", "leading", "no-break-space", "blank", "empty"],
)
def test_destination_ends_at_a_space_a_tab_or_a_line_break(raw: Prose, expected: Prose) -> None:
    """A destination drops the spaces, tabs and line breaks before it and ends at the next one."""
    assert destination(raw) == expected


def test_paragraphs_end_at_a_blank_or_whitespace_only_line() -> None:
    """A paragraph's lines are joined by line breaks; a line of spaces and tabs alone ends it."""
    text = Prose("\n\none\ntwo\n \t\nthree\n\u00a0\nfour\n\nfive\n")
    assert paragraphs(RelPath("a.md"), text) == [
        Prose("one\ntwo"),
        Prose("three\n\u00a0\nfour"),
        Prose("five"),
    ]


def test_a_line_of_letters_alone_is_paragraph_text() -> None:
    """Only spaces and tabs make a line blank, so a line holding a letter stays in its paragraph."""
    assert paragraphs(RelPath("a.md"), Prose("one\nX\ntwo\n")) == [Prose("one\nX\ntwo")]


def test_paragraphs_end_lines_where_the_prose_reader_does() -> None:
    """A form feed or line separator ends a line as the prose reader does; two make a blank line."""
    text = Prose("one\x0c\x0ctwo\nthree\u2028\u2028four\n")
    assert paragraphs(RelPath("a.md"), text) == [Prose("one"), Prose("two\nthree"), Prose("four")]


def test_paragraphs_hold_the_prose_alone() -> None:
    """Fenced code is dropped and each inline code span masked to one backtick."""
    text = Prose("one `[a](x.md)` two `b` three\n\n```\n[b](y.md)\n```\n\nfour\n")
    assert paragraphs(RelPath("a.md"), text) == [Prose("one ` two ` three"), Prose("four")]


def test_a_file_other_than_markdown_is_prose_whole() -> None:
    """A source file's fences and code spans are its own text: every line stays as it is."""
    text = Prose("```\nx = `y`\n```\n")
    assert prose_lines(RelPath("a.py"), text) == [(1, "```"), (2, "x = `y`"), (3, "```")]


def test_an_indented_fence_opens_and_closes_fenced_code() -> None:
    """A fence after leading spaces or a tab still opens and closes fenced code in Markdown."""
    text = Prose("  ```\nx\n\t```\ny\n")
    assert prose_lines(RelPath("a.md"), text) == [(4, "y")]


def test_fenced_code_ends_a_paragraph() -> None:
    """A fence interrupts a paragraph, so the prose on either side of it is two paragraphs."""
    text = Prose("[a](x.md\n```\ncode\n```\nb) c\n")
    assert paragraphs(RelPath("a.md"), text) == [Prose("[a](x.md"), Prose("b) c")]


def test_read_documents_reads_every_tracked_markdown_file_and_nothing_else(tmp_path: Path) -> None:
    """Both Markdown suffixes are read; a source file is not; a byte not UTF-8 reads as U+FFFD."""
    files = {
        RelPath("a.md"): Prose("# A\n"),
        RelPath("docs/b.markdown"): Prose("# B\n"),
        RelPath("c.py"): Prose("print()\n"),
    }
    repo = plant(tmp_path / "repo", files)
    _ = (repo / "a.md").write_bytes(b"# A \xff\n")
    assert read_documents(repo, list(files)) == (
        {RelPath("a.md"): Prose("# A �\n"), RelPath("docs/b.markdown"): Prose("# B\n")},
        [],
    )


def test_read_documents_keeps_the_order_of_the_tracked_paths(tmp_path: Path) -> None:
    """The texts come in the order the tracked paths are given, which every arm reports in."""
    tracked = [RelPath("b.md"), RelPath("a.md"), RelPath("c.md")]
    repo = plant(tmp_path / "repo", dict.fromkeys(tracked, Prose("# Doc\n")))
    texts, _ = read_documents(repo, tracked)
    assert list(texts) == tracked


def test_read_documents_names_each_document_the_work_tree_lacks(tmp_path: Path) -> None:
    """A tracked document gone from the work tree is left out of the texts and named, in order."""
    tracked = [RelPath("a.md"), RelPath("gone.md"), RelPath("b.md"), RelPath("lost.markdown")]
    repo = plant(tmp_path / "repo", dict.fromkeys(tracked[::2], Prose("# Doc\n")))
    assert read_documents(repo, tracked) == (
        {RelPath("a.md"): Prose("# Doc\n"), RelPath("b.md"): Prose("# Doc\n")},
        [
            Prose("gone.md: could not be read, so what it says is unchecked"),
            Prose("lost.markdown: could not be read, so what it says is unchecked"),
        ],
    )


def test_read_tracked_names_a_path_that_is_no_readable_file(tmp_path: Path) -> None:
    """A directory where a tracked file should be is unread like a missing one, never an error."""
    (tmp_path / "dir.md").mkdir()
    for rel in (RelPath("dir.md"), RelPath("gone.md")):
        assert read_tracked(tmp_path, rel, Prose("its claim is unchecked")) == Unread(
            Prose(f"{rel}: could not be read, so its claim is unchecked")
        )


def test_read_tracked_decodes_utf8_and_ends_lines_as_python_text_files_do(tmp_path: Path) -> None:
    """UTF-8 decodes, a byte that is not UTF-8 is U+FFFD, and CRLF and a lone CR are each LF."""
    _ = (tmp_path / "a.md").write_bytes("# Café\r\nb\rc\r\r\n".encode() + b"\xff\n")
    assert read_tracked(tmp_path, RelPath("a.md"), Prose("x")) == Prose("# Café\nb\nc\n\n\ufffd\n")


def test_read_tracked_bytes_gives_the_bytes_as_the_work_tree_holds_them(tmp_path: Path) -> None:
    """The bytes come back unchanged: line ends and a byte that is not UTF-8 among them."""
    data = b"a\r\nb\rc\xff\n"
    _ = (tmp_path / "a").write_bytes(data)
    assert read_tracked_bytes(tmp_path, RelPath("a"), Prose("x")) == data


def test_an_unread_finding_is_a_value() -> None:
    """Two unread findings of one text are one value, so a set holds them once."""
    assert {Unread(Prose("a: x")), Unread(Prose("a: x"))} == {Unread(Prose("a: x"))}


def test_missing_names_an_untracked_file_apart_from_an_unread_one() -> None:
    """A file git does not track is untracked; one it tracks that has no text is unread."""
    tracked = [RelPath("a.md")]
    assert missing(RelPath("a.md"), tracked, Prose("x is unchecked")) == Prose(
        "a.md: could not be read, so x is unchecked"
    )
    assert missing(RelPath("b.md"), tracked, Prose("x is unchecked")) == Prose(
        "b.md: not tracked, so x is unchecked"
    )


def _arm(found: Sequence[Prose]) -> Arm:
    """Return a stand-in arm that reports ``found`` whatever the tree holds."""

    def arm(
        root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
    ) -> list[Prose]:
        del root, tracked, documents
        return list(found)

    return arm


def test_check_tree_returns_every_arms_findings_in_registry_order(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Each registered arm runs, and its findings follow the previous arm's."""
    first, second = [Prose("a.md: first")], [Prose("b.md: second"), Prose("b.md: third")]
    monkeypatch.setattr(check_docs, "ARMS", (_arm(first), _arm(()), _arm(second)))
    assert check_tree(tmp_path, [], {}) == [*first, *second]


def test_main_exits_1_listing_the_findings_and_0_when_every_arm_holds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A finding fails the gate and is printed; no finding passes it."""
    printed: list[Prose] = []

    def record(message: Prose) -> None:
        printed.append(message)

    repo = plant(tmp_path / "repo", {RelPath("README.md"): Prose("# Readme\n")})
    monkeypatch.setattr(check_docs, "emit", record)
    monkeypatch.setattr(check_docs, "REPO", repo)

    def tracked(_root: Path) -> list[RelPath]:
        return [RelPath("README.md")]

    monkeypatch.setattr(check_docs, "git_ls_files", tracked)
    monkeypatch.setattr(check_docs, "ARMS", (_arm([Prose("README.md: planted")]),))
    assert main([]) == ExitStatus(1)
    assert Prose("  README.md: planted") in printed
    monkeypatch.setattr(check_docs, "ARMS", (_arm(()),))
    assert main([]) == ExitStatus(0)


def test_main_lists_a_document_the_work_tree_lacks_before_the_arms(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tracked document gone from the work tree fails the gate, named before every arm's finding.

    The arms run over the documents that were read, the unread one not among them.
    """
    printed: list[Prose] = []
    seen: list[list[RelPath]] = []

    def record(message: Prose) -> None:
        printed.append(message)

    def arm(
        root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
    ) -> list[Prose]:
        del root, tracked
        seen.append(list(documents))
        return [Prose("README.md: planted")]

    def tracked(_root: Path) -> list[RelPath]:
        return [RelPath("README.md"), RelPath("gone.md")]

    repo = plant(tmp_path / "repo", {RelPath("README.md"): Prose("# Readme\n")})
    monkeypatch.setattr(check_docs, "emit", record)
    monkeypatch.setattr(check_docs, "REPO", repo)
    monkeypatch.setattr(check_docs, "git_ls_files", tracked)
    monkeypatch.setattr(check_docs, "ARMS", (arm,))
    assert main([]) == ExitStatus(1)
    assert printed == [
        Prose("check_docs: 2 documentation defect(s):"),
        Prose("  gone.md: could not be read, so what it says is unchecked"),
        Prose("  README.md: planted"),
    ]
    assert seen == [[RelPath("README.md")]]


def test_every_arm_module_is_registered() -> None:
    """The gate runs the ``findings`` of every module under ``tools/docs_arms/``, and nothing else.

    An arm written and left out of ``ARMS`` would hold its claim nowhere while
    its own tests stay green.
    """
    modules = {f"tools.docs_arms.{info.name}" for info in pkgutil.iter_modules(docs_arms.__path__)}
    assert modules, "a scan over no arm module holds nothing"
    assert {arm.__module__ for arm in ARMS} == modules
    assert {arm.__name__ for arm in ARMS} == {"findings"}
    assert len(ARMS) == len(modules)

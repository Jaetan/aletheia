# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_docs``, the documentation gate, and the readers its arms share.

The gate reads every tracked Markdown file once and runs every arm over the
same texts: these tests hold the reading, the order the arms' findings come
in, the exit status, the registry of arms, and the tracked-file, directory and
anchor readers in ``tools/docs_arms/__init__.py`` they rest on. The Markdown
reader under them is tested in ``python/tests/test_markdown.py``, and each
arm's own claim in ``python/tests/test_docs_arm_<arm>.py``.
"""

from __future__ import annotations

import pkgutil
from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant

from tools import check_docs, docs_arms
from tools._common import RelPath
from tools.check_docs import ARMS, check_tree, main, read_documents
from tools.docs_arms import (
    Unread,
    header_slugs,
    html_anchors,
    missing,
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


def test_a_repeated_heading_takes_githubs_numbered_suffixes() -> None:
    """The first copy keeps the slug; each later one adds -1, -2 in order."""
    text = Prose("# Same\n## Same\n### Same\n")
    assert header_slugs(text) == {Prose("same"), Prose("same-1"), Prose("same-2")}


def test_an_html_name_or_id_is_an_anchor_too() -> None:
    """Explicit name= and id= attributes are anchors beside the headings' slugs."""
    text = Prose('# Top\n<a name="kept"></a> <span id="also-kept"></span>\n')
    assert header_slugs(text) == {Prose("top"), Prose("kept"), Prose("also-kept")}


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("# a &amp; b\n"), {Prose("a--b")}),
        (Prose("# See [the guide](x.md)\n"), {Prose("see-the-guide")}),
        (Prose("# Set *in* `code`\n"), {Prose("set-in-code")}),
        (Prose("Underlined\n===\n"), {Prose("underlined")}),
        (Prose("> ## Quoted\n"), {Prose("quoted")}),
        (Prose("## Closed #\n"), {Prose("closed")}),
    ],
    ids=["entity", "link", "emphasis-and-code", "setext", "in-a-quote", "closing-run"],
)
def test_a_headings_anchor_is_the_slug_of_what_it_renders(
    text: Prose, expected: set[Prose]
) -> None:
    """The slug is taken from the rendered text, of any heading CommonMark reads."""
    assert header_slugs(text) == expected


def test_html_in_code_defines_no_anchor() -> None:
    """An id or a name inside a fence or a code span is an example, not an anchor."""
    text = Prose('# Top\n\n```\n<a id="fenced"></a>\n```\n\nSee `<a name="span">`.\n')
    assert header_slugs(text) == {Prose("top")}


def test_tracked_dirs_are_every_directory_on_the_way_to_a_file() -> None:
    """Each proper prefix of a tracked path, and neither the file nor the empty path."""
    assert tracked_dirs([RelPath("a/b/c.md"), RelPath("top.md")]) == {RelPath("a"), RelPath("a/b")}


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


@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        (
            Prose("<a id='single'></a> <span id=bare></span> <b ID=\"upper\">"),
            [Prose("single"), Prose("bare"), Prose("upper")],
        ),
        (Prose('<a name="named"></a> <div name="not"></div>'), [Prose("named")]),
        (Prose('<a id="a&amp;b"></a>'), [Prose("a&b")]),
        (Prose('<p id="first" id="second"></p>'), [Prose("first")]),
        (
            Prose('<div data-id="no" title=\'id="no"\'></div> <a href="h" title="t" id>'),
            list[Prose](),
        ),
        (Prose('<!-- <a id="no"> -->'), list[Prose]()),
        (Prose('<script>x = "<a id=no>"</script>'), list[Prose]()),
        (Prose('<textarea><a id="no"></textarea>'), list[Prose]()),
    ],
    ids=[
        "quoting-and-case",
        "name-on-a-only",
        "reference",
        "repeated-attribute",
        "other-attributes",
        "comment",
        "script",
        "textarea",
    ],
)
def test_an_html_fragment_is_what_a_browser_would_scroll_to(
    raw: Prose, expected: list[Prose]
) -> None:
    """Any element's id and an a element's name, read as HTML, and nothing else."""
    assert html_anchors(raw) == expected


def test_a_tag_inside_an_inline_script_is_no_anchor() -> None:
    """A paragraph's tags are read together, so one inside its ``<script>`` names nothing."""
    text = Prose('# Top\n\nText <script>x = "<a id="no">";</script> more.\n')
    assert header_slugs(text) == {Prose("top")}

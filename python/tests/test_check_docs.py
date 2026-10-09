# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_docs``, the documentation gate, and the readers its arms share.

The gate reads every tracked Markdown file once and runs every arm over the
same texts: these tests hold the reading, the order the arms' findings come
in, the exit status, the registry of arms, and the heading and directory
readers in ``tools/docs_arms/__init__.py``. Each arm's own claim is tested in
``python/tests/test_docs_arm_<arm>.py``.
"""

from __future__ import annotations

import pkgutil
from typing import TYPE_CHECKING

from _planted_tree import plant

from tools import check_docs, docs_arms
from tools._common import RelPath
from tools.check_docs import ARMS, check_tree, main, read_documents
from tools.docs_arms import header_slugs, headings, slug, tracked_dirs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

    import pytest

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


def test_read_documents_reads_every_tracked_markdown_file_and_nothing_else(tmp_path: Path) -> None:
    """Both Markdown suffixes are read; a source file is not; a byte not UTF-8 reads as U+FFFD."""
    files = {
        RelPath("a.md"): Prose("# A\n"),
        RelPath("docs/b.markdown"): Prose("# B\n"),
        RelPath("c.py"): Prose("print()\n"),
    }
    repo = plant(tmp_path / "repo", files)
    _ = (repo / "a.md").write_bytes(b"# A \xff\n")
    assert read_documents(repo, list(files)) == {
        RelPath("a.md"): Prose("# A �\n"),
        RelPath("docs/b.markdown"): Prose("# B\n"),
    }


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

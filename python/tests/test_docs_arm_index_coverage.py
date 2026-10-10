# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The index-coverage arm finds a tracked document docs/INDEX.md does not name.

Each test plants a tree with an index and a few documents and runs the arm the
way the gate does, on the tracked paths and the tracked Markdown files.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.index_coverage import INDEX, findings, in_scope, names

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path


def _repo(tmp_path: Path, files: dict[RelPath, Prose]) -> Path:
    """Return a planted tree holding ``files``, each at its relative path."""
    return plant(tmp_path / "repo", files)


def _run(repo: Path) -> list[Prose]:
    """Run the arm on ``repo`` as the gate does: every tracked path, every tracked Markdown file."""
    return run_planted(findings, repo)


_DESIGN_LINE = Prose("- [Design](architecture/DESIGN.md)\n")
_SOMEIP_LINE = Prose("- [SOME/IP](development/SOMEIP_DESIGN.md)\n")
_STANDARDS_LINE = Prose("- [Standards](../AGENTS.md)\n")
_PYTHON_LINE = Prose("- [Python](../AGENTS/python.md)\n")
_INDEX_NAMING_ALL = Prose(f"# Index\n\n{_DESIGN_LINE}{_STANDARDS_LINE}{_PYTHON_LINE}")
_DOCS = {
    RelPath("docs/architecture/DESIGN.md"): Prose("# Design\n"),
    RelPath("AGENTS.md"): Prose("# Standards\n"),
    RelPath("AGENTS/python.md"): Prose("# Python\n"),
    RelPath("README.md"): Prose("# Not in scope\n"),
}


def test_a_document_the_index_does_not_name_is_a_finding(tmp_path: Path) -> None:
    """A tracked per-language standards file absent from the index is reported against the index."""
    repo = _repo(
        tmp_path,
        {
            INDEX: Prose(f"# Index\n\n{_DESIGN_LINE}{_STANDARDS_LINE}"),
            **_DOCS,
        },
    )
    assert _run(repo) == [Prose("docs/INDEX.md: does not name AGENTS/python.md")]


def test_an_index_naming_every_document_is_clean(tmp_path: Path) -> None:
    """An index naming every document in scope yields no finding."""
    repo = _repo(tmp_path, {INDEX: _INDEX_NAMING_ALL, **_DOCS})
    assert _run(repo) == list[Prose]()


def test_a_name_inside_a_longer_name_does_not_count(tmp_path: Path) -> None:
    """``SOMEIP_DESIGN.md`` in the index does not name ``DESIGN.md``."""
    repo = _repo(
        tmp_path,
        {
            INDEX: Prose(f"# Index\n\n{_SOMEIP_LINE}{_STANDARDS_LINE}{_PYTHON_LINE}"),
            RelPath("docs/development/SOMEIP_DESIGN.md"): Prose("# SOME/IP\n"),
            **_DOCS,
        },
    )
    assert _run(repo) == [Prose("docs/INDEX.md: does not name docs/architecture/DESIGN.md")]


def test_a_name_quoted_in_backticks_counts(tmp_path: Path) -> None:
    """A file name in a code span still tells the reader where to look."""
    repo = _repo(
        tmp_path,
        {
            INDEX: Prose("# Index\n\n`DESIGN.md`, `AGENTS.md` and `python.md` sit beside it.\n"),
            **_DOCS,
        },
    )
    assert _run(repo) == list[Prose]()


def test_a_tree_with_no_document_in_scope_is_a_finding(tmp_path: Path) -> None:
    """An index with nothing to name is not a pass: the scan found nothing it expects."""
    repo = _repo(tmp_path, {INDEX: Prose("# Index\n"), RelPath("README.md"): Prose("# Root\n")})
    assert _run(repo) == [
        Prose("docs/INDEX.md: no document read under docs/ or AGENTS/ to check against it")
    ]


def test_an_untracked_index_is_a_finding(tmp_path: Path) -> None:
    """A tree whose index is not tracked has no index naming its documents."""
    repo = _repo(tmp_path, dict(_DOCS))
    assert _run(repo) == [
        Prose("docs/INDEX.md: not tracked, so whether it names every document is unchecked")
    ]


def test_scope_is_docs_agents_and_the_root_standards_file() -> None:
    """The index names the documents under docs/ and AGENTS/ and AGENTS.md, never itself."""
    assert in_scope(RelPath("docs/guides/TUTORIAL.md"))
    assert in_scope(RelPath("AGENTS/go.md"))
    assert in_scope(RelPath("AGENTS.md"))
    assert not in_scope(INDEX)
    assert not in_scope(RelPath("README.md"))
    assert not in_scope(RelPath("python/README.md"))
    assert not in_scope(RelPath(".archive/reviews/notes.md"))


def test_names_is_a_whole_name_match() -> None:
    """A name is whole between non-word characters; a dot or a hyphen beside it is a boundary."""
    assert names(Prose("(architecture/DESIGN.md)"), RelPath("DESIGN.md"))
    assert names(Prose("`DESIGN.md`"), RelPath("DESIGN.md"))
    assert not names(Prose("(development/SOMEIP_DESIGN.md)"), RelPath("DESIGN.md"))
    assert not names(Prose("(DESIGN.mdx)"), RelPath("DESIGN.md"))
    assert names(Prose("See DESIGN.md."), RelPath("DESIGN.md"))
    assert names(Prose("(OLD-DESIGN.md)"), RelPath("DESIGN.md"))


def test_a_path_only_beginning_with_a_scope_name_is_out_of_scope() -> None:
    """A path whose first segment only begins with ``docs`` or ``AGENTS`` is not in scope."""
    assert not in_scope(RelPath("docs-archive/OLD.md"))
    assert not in_scope(RelPath("AGENTS-draft.md"))


def test_the_dot_of_a_file_name_matches_only_a_dot() -> None:
    """``DESIGN.md`` is not named by ``DESIGN_md``, where another character stands for the dot."""
    assert not names(Prose("See DESIGN_md for the layout."), RelPath("DESIGN.md"))


def test_findings_follow_the_order_of_the_documents(tmp_path: Path) -> None:
    """The unnamed documents are reported in the order the documents are handed in."""
    documents = {
        INDEX: Prose("# Index\n"),
        RelPath("docs/guides/TUTORIAL.md"): Prose("# Tutorial\n"),
        RelPath("AGENTS/python.md"): Prose("# Python\n"),
        RelPath("docs/architecture/DESIGN.md"): Prose("# Design\n"),
        RelPath("AGENTS.md"): Prose("# Standards\n"),
    }
    assert findings(tmp_path, list(documents), documents) == [
        Prose("docs/INDEX.md: does not name docs/guides/TUTORIAL.md"),
        Prose("docs/INDEX.md: does not name AGENTS/python.md"),
        Prose("docs/INDEX.md: does not name docs/architecture/DESIGN.md"),
        Prose("docs/INDEX.md: does not name AGENTS.md"),
    ]


def test_a_tracked_index_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """An index git tracks and the work tree lacks is named as unread, never as untracked."""
    repo = _repo(tmp_path, _DOCS)
    assert run_planted(findings, repo, absent={INDEX}) == [
        Prose(f"{INDEX}: could not be read, so what it says is unchecked"),
        Prose(f"{INDEX}: could not be read, so whether it names every document is unchecked"),
    ]


def test_an_unread_document_in_scope_leaves_none_read(tmp_path: Path) -> None:
    """A document under docs/ the work tree lacks is named by the read; none is left to check."""
    repo = _repo(tmp_path, {INDEX: Prose("# Index\n")})
    gone = RelPath("docs/architecture/DESIGN.md")
    assert run_planted(findings, repo, absent={gone}) == [
        Prose(f"{gone}: could not be read, so what it says is unchecked"),
        Prose(f"{INDEX}: no document read under docs/ or AGENTS/ to check against it"),
    ]

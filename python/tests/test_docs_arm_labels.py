# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The transient-label arm of the documentation gate, run over planted trees.

Each mark the arm refuses is planted in the prose of a living document and
reported once; the same mark in code, or in a document the arm does not read,
is no finding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.labels import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

_CLEAN = Prose("# Guide\n\nThe current state, plainly.\n")


def _run(tmp_path: Path, files: Mapping[RelPath, Prose]) -> list[Prose]:
    return run_planted(findings, plant(tmp_path / "repo", {RelPath("README.md"): _CLEAN, **files}))


@pytest.mark.parametrize(
    ("mark", "finding"),
    [
        (Prose("(PR C)"), Prose("internal PR label -> '(PR C)'")),
        (Prose("R19 cluster"), Prose("review-round cluster mark -> 'R19 cluster'")),
        (Prose("AGDA-C-6.2"), Prose("finding id -> 'AGDA-C-6.2'")),
        (Prose("PY-S-20"), Prose("review finding mark -> 'PY-S-20'")),
        (Prose("Pending Push"), Prose("transient session phrase -> 'Pending Push'")),
        (Prose("committed locally"), Prose("transient session phrase -> 'committed locally'")),
        (Prose("Committed Locally"), Prose("transient session phrase -> 'Committed Locally'")),
        (
            Prose("[x](memory/notes.md)"),
            Prose("link into the ~/.claude memory store -> memory/notes.md"),
        ),
        (
            Prose("[x](/home/u/.claude/notes.md)"),
            Prose("link into the ~/.claude memory store -> /home/u/.claude/notes.md"),
        ),
    ],
    ids=[
        "pr",
        "cluster",
        "finding-id",
        "py-s",
        "pending",
        "committed",
        "committed-any-case",
        "memory",
        "claude",
    ],
)
def test_a_mark_in_living_prose_is_a_finding(tmp_path: Path, mark: Prose, finding: Prose) -> None:
    """Each refused mark, in the prose of a document under docs/, is reported against it."""
    found = _run(tmp_path, {RelPath("docs/guide.md"): Prose(f"{_CLEAN}See {mark} here.\n")})
    assert found == [Prose(f"docs/guide.md: {finding}")]


@pytest.mark.parametrize(
    "rel",
    [RelPath("README.md"), RelPath("python/README.md"), RelPath("docs/sub/deep.md")],
    ids=["root-readme", "nested-readme", "docs"],
)
def test_every_living_document_is_read(tmp_path: Path, rel: RelPath) -> None:
    """The root README, any other README and anything under docs/ are living documents."""
    assert _run(tmp_path, {rel: Prose(f"{_CLEAN}(PR C)\n")}) == [
        Prose(f"{rel}: internal PR label -> '(PR C)'")
    ]


@pytest.mark.parametrize(
    "rel",
    [RelPath("CHANGELOG.md"), RelPath("PROJECT_STATUS.md"), RelPath("AGENTS/go.md")],
    ids=["changelog", "status", "standard"],
)
def test_a_record_of_history_is_not_read(tmp_path: Path, rel: RelPath) -> None:
    """The logs and the standards outside docs/ are not living documents here."""
    assert _run(tmp_path, {rel: Prose(f"{_CLEAN}(PR C)\n")}) == list[Prose]()


def test_a_mark_shown_as_code_is_not_prose(tmp_path: Path) -> None:
    """A mark in a fence or an inline code span is an example, not a label."""
    text = Prose(f"{_CLEAN}```\n(PR C)\n```\nMarks like `AGDA-C-6.2` are refused.\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == list[Prose]()


@pytest.mark.parametrize(
    "code",
    [
        Prose("````\n```\n(PR C)\n````"),
        Prose("Marks like ``(PR C)`` are refused."),
        Prose("Marks like `` `(PR C)` `` are refused."),
        Prose("```\n[x](memory/notes.md)\n```"),
        Prose("See `[x](memory/notes.md)` there."),
    ],
    ids=[
        "fence-of-four",
        "double-backtick-span",
        "span-holding-backticks",
        "fenced-link",
        "span-link",
    ],
)
def test_code_as_commonmark_reads_it_holds_no_label(tmp_path: Path, code: Prose) -> None:
    """A fence closes only on a run as long as its own; a span of two backticks is code too."""
    text = Prose(f"{_CLEAN}\n{code}\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == list[Prose]()


@pytest.mark.parametrize(
    ("text", "finding"),
    [
        (Prose("~~~\n```\n~~~\n(PR C)"), Prose("internal PR label -> '(PR C)'")),
        (Prose("    ```\n(PR C)"), Prose("internal PR label -> '(PR C)'")),
        (
            Prose("See [x][notes].\n\n[notes]: memory/notes.md"),
            Prose("link into the ~/.claude memory store -> memory/notes.md"),
        ),
        (
            Prose("See [x](<memory/my notes.md>)."),
            Prose("link into the ~/.claude memory store -> memory/my notes.md"),
        ),
    ],
    ids=["backticks-inside-a-tilde-fence", "indented-backticks", "reference", "pointy-brackets"],
)
def test_prose_and_links_as_commonmark_reads_them_are_read(
    tmp_path: Path, text: Prose, finding: Prose
) -> None:
    """Backticks inside a tilde fence or indented as code open no fence; any link form is read."""
    found = _run(tmp_path, {RelPath("docs/guide.md"): Prose(f"{_CLEAN}\n{text}\n")})
    assert found == [Prose(f"docs/guide.md: {finding}")]


def test_each_distinct_mark_is_reported_once_in_order(tmp_path: Path) -> None:
    """A repeated mark is one finding; two distinct ones come in sorted order."""
    text = Prose(f"{_CLEAN}(PR D) and (PR C), then (PR D) again.\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == [
        Prose("docs/guide.md: internal PR label -> '(PR C)'"),
        Prose("docs/guide.md: internal PR label -> '(PR D)'"),
    ]


def test_a_tree_with_no_living_document_is_a_finding(tmp_path: Path) -> None:
    """With no living document the scan holds nothing, which is reported."""
    repo = plant(tmp_path / "repo", {RelPath("CHANGELOG.md"): _CLEAN})
    assert run_planted(findings, repo) == [
        Prose("README.md: no living document was read, so no label is checked")
    ]


def test_a_tracked_readme_the_work_tree_lacks_leaves_no_living_document(tmp_path: Path) -> None:
    """A README git tracks and the work tree lacks, and no other living document, is a finding."""
    repo = plant(tmp_path / "repo", {RelPath("src/main.py"): Prose("print()\n")})
    assert run_planted(findings, repo, absent={RelPath("README.md")}) == [
        Prose("README.md: could not be read, so what it says is unchecked"),
        Prose("README.md: no living document was read, so no label is checked"),
    ]


def test_an_unread_readme_leaves_the_other_living_documents_checked(tmp_path: Path) -> None:
    """A README the work tree lacks is named, and a guide under docs/ is still read for labels."""
    repo = plant(tmp_path / "repo", {RelPath("docs/guide.md"): Prose("# Guide\n\n(PR C)\n")})
    assert run_planted(findings, repo, absent={RelPath("README.md")}) == [
        Prose("README.md: could not be read, so what it says is unchecked"),
        Prose("docs/guide.md: internal PR label -> '(PR C)'"),
    ]


@pytest.mark.parametrize(
    ("link", "target"),
    [
        (Prose("[x](.claude/notes.md)"), Prose(".claude/notes.md")),
        (Prose("[x](./memory/notes.md)"), Prose("./memory/notes.md")),
        (Prose("[x](memory%2Fnotes.md)"), Prose("memory%2Fnotes.md")),
        (Prose("<file:///home/u/.claude/notes.md>"), Prose("file:///home/u/.claude/notes.md")),
    ],
    ids=["relative-claude", "dot-memory", "encoded-slash", "autolink"],
)
def test_every_spelling_of_a_memory_link_is_found(
    tmp_path: Path, link: Prose, target: Prose
) -> None:
    """A ``.claude`` directory anywhere, ``./`` before ``memory/``, an escape, an autolink."""
    found = _run(tmp_path, {RelPath("docs/guide.md"): Prose(f"{_CLEAN}\nSee {link}.\n")})
    assert found == [Prose(f"docs/guide.md: link into the ~/.claude memory store -> {target}")]


def test_a_path_that_only_begins_like_the_store_is_not_one(tmp_path: Path) -> None:
    """``memoryless.md`` is not under ``memory/``."""
    text = Prose(f"{_CLEAN}\nSee [x](memoryless.md).\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == list[Prose]()


def test_a_mark_opening_a_line_is_read_apart_from_the_line_before(tmp_path: Path) -> None:
    """The prose's lines stay apart, so a word ending one line leaves the next one's mark whole."""
    text = Prose(f"{_CLEAN}\nSee\nPY-S-20 here.\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == [
        Prose("docs/guide.md: review finding mark -> 'PY-S-20'")
    ]

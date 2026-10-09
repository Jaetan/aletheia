# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The transient-label arm of the documentation gate, run over throwaway repositories.

Each mark the arm refuses is planted in the prose of a living document and
reported once; the same mark in code, or in a document the arm does not read,
is no finding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import committed

from tools._common import RelPath
from tools.check_docs import run_arm
from tools.docs_arms.labels import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

_CLEAN = Prose("# Guide\n\nThe current state, plainly.\n")


def _run(tmp_path: Path, files: Mapping[RelPath, Prose]) -> list[Prose]:
    return run_arm(findings, committed(tmp_path / "repo", {RelPath("README.md"): _CLEAN, **files}))


@pytest.mark.parametrize(
    ("mark", "finding"),
    [
        (Prose("(PR C)"), Prose("internal PR label -> '(PR C)'")),
        (Prose("R19 cluster"), Prose("review-round cluster mark -> 'R19 cluster'")),
        (Prose("AGDA-C-6.2"), Prose("finding id -> 'AGDA-C-6.2'")),
        (Prose("PY-S-20"), Prose("review finding mark -> 'PY-S-20'")),
        (Prose("Pending Push"), Prose("transient session phrase -> 'Pending Push'")),
        (Prose("committed locally"), Prose("transient session phrase -> 'committed locally'")),
        (
            Prose("[x](memory/notes.md)"),
            Prose("link into the ~/.claude memory store -> ](memory/notes.md)"),
        ),
        (
            Prose("[x](/home/u/.claude/notes.md)"),
            Prose("link into the ~/.claude memory store -> ](/home/u/.claude/notes.md)"),
        ),
    ],
    ids=["pr", "cluster", "finding-id", "py-s", "pending", "committed", "memory", "claude"],
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
    assert _run(tmp_path, {rel: Prose(f"{_CLEAN}(PR C)\n")}) == []


def test_a_mark_shown_as_code_is_not_prose(tmp_path: Path) -> None:
    """A mark in a fence or an inline code span is an example, not a label."""
    text = Prose(f"{_CLEAN}```\n(PR C)\n```\nMarks like `AGDA-C-6.2` are refused.\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == []


def test_each_distinct_mark_is_reported_once_in_order(tmp_path: Path) -> None:
    """A repeated mark is one finding; two distinct ones come in sorted order."""
    text = Prose(f"{_CLEAN}(PR D) and (PR C), then (PR D) again.\n")
    assert _run(tmp_path, {RelPath("docs/guide.md"): text}) == [
        Prose("docs/guide.md: internal PR label -> '(PR C)'"),
        Prose("docs/guide.md: internal PR label -> '(PR D)'"),
    ]


def test_a_tree_with_no_living_document_is_a_finding(tmp_path: Path) -> None:
    """With no living document the scan holds nothing, which is reported."""
    repo = committed(tmp_path / "repo", {RelPath("CHANGELOG.md"): _CLEAN})
    assert run_arm(findings, repo) == [
        Prose("README.md: not tracked, and no other living document is")
    ]

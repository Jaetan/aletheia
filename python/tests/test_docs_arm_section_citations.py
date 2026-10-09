# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The section-citation arm of the documentation gate, run over planted trees.

Each fixture is a tree holding ``go/README.md``, the document the arm
expects a section citation in, and the document it cites. A planted defect
yields one finding naming the citing document; a clean fixture yields none; a
subject carrying no citation is a finding too, so the scan cannot pass by
matching nothing.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import run_planted

from tools.docs_arms.section_citations import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_SUBJECT = "go/README.md"
_TARGET = "docs/architecture/CANCELLATION.md"

# The citation after the link, as go/README.md spells it, the number on the next line.
_AFTER_LINK = Prose(
    "# Go binding\n\nThe lock is a channel (see\n"
    + "[../docs/architecture/CANCELLATION.md](../docs/architecture/CANCELLATION.md)\n"
    + "§ 2.2). More prose.\n"
)
# The citation inside the link text, as the runbook spells it.
_IN_LINK_TEXT = Prose(
    "# Go binding\n\nPer [CANCELLATION.md § 2.2]"
    + "(../docs/architecture/CANCELLATION.md#22-go), the lock is a channel.\n"
)


def _repo(tmp_path: Path, readme: Prose, contract: Prose) -> Path:
    """Return a planted tree holding the subject and the document it cites."""
    repo = tmp_path / "repo"
    (repo / "go").mkdir(parents=True)
    (repo / "docs" / "architecture").mkdir(parents=True)
    _ = (repo / _SUBJECT).write_text(readme, encoding="utf-8")
    _ = (repo / _TARGET).write_text(contract, encoding="utf-8")
    return repo.resolve()


def _contract(go: Prose) -> Prose:
    """Return the cited document with ``go`` as the heading of its Go section."""
    return Prose(
        "# Cancellation\n\n## 2. Per-Binding Mechanics\n\n### 2.1 Python\n\n" + go + "\n\nprose\n"
    )


def _run(repo: Path) -> list[Prose]:
    """Run the arm over ``repo`` the way the gate does."""
    return run_planted(findings, repo)


@pytest.mark.parametrize("readme", [_AFTER_LINK, _IN_LINK_TEXT], ids=["after-link", "in-text"])
def test_citation_naming_a_heading_is_clean(tmp_path: Path, readme: Prose) -> None:
    """Section 2.2 cited beside the link, and a heading of the target starting with 2.2."""
    assert not _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))


@pytest.mark.parametrize("readme", [_AFTER_LINK, _IN_LINK_TEXT], ids=["after-link", "in-text"])
@pytest.mark.parametrize(
    "heading", [Prose(h) for h in ("### 2.3 Go", "### 2.21 Go", "### 2.2.1 Go", "### Go")]
)
def test_renumbered_target_heading_is_a_finding(
    tmp_path: Path, readme: Prose, heading: Prose
) -> None:
    """The target's heading no longer starts with the cited number: one finding naming the citer."""
    found = _run(_repo(tmp_path, readme, _contract(heading)))
    assert len(found) == 1
    assert found[0].startswith(f"{_SUBJECT}: ")
    assert "2.2" in found[0]
    assert _TARGET in found[0]


@pytest.mark.parametrize(
    "readme",
    [
        Prose(
            "# Go binding\n\nSee [the contract](../docs/architecture/CANCELLATION.md) § 2.2.1.\n"
        ),
        Prose(
            "# Go binding\n\nPer [CANCELLATION.md § 2.2.1]"
            + "(../docs/architecture/CANCELLATION.md), the lock is a channel.\n"
        ),
    ],
    ids=["after-link", "in-text"],
)
def test_a_three_level_section_is_read_whole(tmp_path: Path, readme: Prose) -> None:
    """Section 2.2.1 is cited whole, so a heading starting with 2.2.1 answers it."""
    assert not _run(_repo(tmp_path, readme, _contract(Prose("### 2.2.1 Go"))))


def test_a_link_title_is_not_part_of_the_target(tmp_path: Path) -> None:
    """A titled link cites the document its path names, the quoted title dropped."""
    readme = Prose(
        '# Go binding\n\nSee [the contract](../docs/architecture/CANCELLATION.md "Cancellation")'
        + " § 2.2.\n"
    )
    assert not _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))


@pytest.mark.parametrize(
    ("cited", "expected"),
    [
        (Prose("2"), []),
        (
            Prose("3"),
            [Prose(f"{_SUBJECT}: § 3 cited beside a link to {_SUBJECT} names no heading there")],
        ),
    ],
    ids=["own-heading", "no-such-heading"],
)
def test_an_anchor_only_link_cites_the_document_it_sits_in(
    tmp_path: Path, cited: Prose, expected: list[Prose]
) -> None:
    """A link holding only an anchor cites a section of its own document, held to its headings."""
    readme = Prose(f"# Go binding\n\n## 2. Lock\n\nSee [the lock § {cited}](#2-lock).\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == expected


def test_citation_in_a_fence_is_not_read(tmp_path: Path) -> None:
    """A link and section number shown in a code fence are an example, not a citation."""
    readme = Prose(_AFTER_LINK + "\n```\n[x](../docs/architecture/CANCELLATION.md) § 9.9\n```\n")
    assert not _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))


def test_subject_without_a_citation_is_a_finding(tmp_path: Path) -> None:
    """The subject carries no section citation beside a link: the scan matched nothing."""
    readme = Prose("# Go binding\n\nSee [the contract](../docs/architecture/CANCELLATION.md).\n")
    found = _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))
    assert len(found) == 1
    assert found[0].startswith(f"{_SUBJECT}: ")


def test_absent_subject_is_a_finding(tmp_path: Path) -> None:
    """The subject is not among the tracked documents: a finding naming it."""
    repo = _repo(tmp_path, _AFTER_LINK, _contract(Prose("### 2.2 Go")))
    (repo / _SUBJECT).unlink()
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{_SUBJECT}: ")


def test_target_outside_the_tracked_documents_is_a_finding(tmp_path: Path) -> None:
    """A section cited beside a link to an untracked target cannot resolve: one finding."""
    readme = Prose("# Go binding\n\nSee [notes](../docs/NOTES.md) § 2.2 for the lock.\n")
    found = _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))
    assert len(found) == 1
    assert found[0].startswith(f"{_SUBJECT}: ")
    assert "2.2" in found[0]


def test_a_citation_in_any_document_is_read(tmp_path: Path) -> None:
    """A numbered citation in a document other than the expected subject is held to its target."""
    repo = _repo(tmp_path, _AFTER_LINK, _contract(Prose("### 2.2 Go")))
    guide = repo / "docs" / "guides" / "QUICK.md"
    guide.parent.mkdir(parents=True)
    _ = guide.write_text(
        "See [the contract §1 Prerequisites](../architecture/CANCELLATION.md#cancellation).\n",
        encoding="utf-8",
    )
    assert _run(repo) == [
        Prose(
            "docs/guides/QUICK.md: § 1 cited beside a link to "
            + f"{_TARGET} names no heading there"
        )
    ]

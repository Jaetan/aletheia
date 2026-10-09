# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The section-citation arm of the documentation gate, run over planted trees.

Each fixture is a tree holding ``go/README.md``, the document the arm
expects a section citation in, and the document it cites. Each planted defect
yields one finding naming the citing document; a clean fixture yields none; a
subject carrying no citation is a finding too, so the scan cannot pass by
matching nothing.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.section_citations import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_SUBJECT = RelPath("go/README.md")
_TARGET = RelPath("docs/architecture/CANCELLATION.md")

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
# The finding of a subject whose links carry no section number.
_CITES_NOTHING = Prose(
    f"{_SUBJECT}: carries no section citation beside a link, which this arm expects"
)


def _repo(tmp_path: Path, readme: Prose, contract: Prose) -> Path:
    """Return a planted tree holding the subject and the document it cites."""
    return plant(tmp_path / "repo", {_SUBJECT: readme, _TARGET: contract})


def _contract(go: Prose) -> Prose:
    """Return the cited document with ``go`` as the heading of its Go section."""
    return Prose(
        "# Cancellation\n\n## 2. Per-Binding Mechanics\n\n### 2.1 Python\n\n" + go + "\n\nprose\n"
    )


def _no_heading(section: Prose) -> Prose:
    """Return the finding of the subject citing ``section``, which no target heading opens with."""
    return Prose(f"{_SUBJECT}: § {section} cited beside a link to {_TARGET} names no heading there")


def _run(repo: Path) -> list[Prose]:
    """Run the arm over ``repo`` the way the gate does."""
    return run_planted(findings, repo)


@pytest.mark.parametrize("readme", [_AFTER_LINK, _IN_LINK_TEXT], ids=["after-link", "in-text"])
def test_citation_naming_a_heading_is_clean(tmp_path: Path, readme: Prose) -> None:
    """Section 2.2 cited beside the link, and a heading of the target starting with 2.2."""
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == list[Prose]()


@pytest.mark.parametrize("readme", [_AFTER_LINK, _IN_LINK_TEXT], ids=["after-link", "in-text"])
@pytest.mark.parametrize(
    "heading", [Prose(h) for h in ("### 2.3 Go", "### 2.21 Go", "### 2.2.1 Go", "### Go")]
)
def test_renumbered_target_heading_is_a_finding(
    tmp_path: Path, readme: Prose, heading: Prose
) -> None:
    """The target's heading no longer starts with the cited number: one finding naming the citer."""
    found = _run(_repo(tmp_path, readme, _contract(heading)))
    assert found == [_no_heading(Prose("2.2"))]


@pytest.mark.parametrize("readme", [_AFTER_LINK, _IN_LINK_TEXT], ids=["after-link", "in-text"])
def test_a_dot_in_the_number_matches_only_a_dot(tmp_path: Path, readme: Prose) -> None:
    """A heading starting with 2x2 does not answer section 2.2, whose dot is literal."""
    found = _run(_repo(tmp_path, readme, _contract(Prose("### 2x2 Go"))))
    assert found == [_no_heading(Prose("2.2"))]


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
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2.1 Go")))) == list[Prose]()


@pytest.mark.parametrize(
    ("link", "expected"),
    [
        (Prose("[CANCELLATION.md § 2.2](@) § 9.9"), [Prose("9.9")]),
        (Prose("[CANCELLATION.md § 9.9](@) § 2.2"), [Prose("9.9")]),
        (Prose("[CANCELLATION.md § 2.2 and § 9.9](@)"), [Prose("9.9")]),
        (Prose("[CANCELLATION.md § 8.8](@) § 9.9"), [Prose("8.8"), Prose("9.9")]),
    ],
    ids=["after-unanswered", "in-text-unanswered", "second-in-text", "both-unanswered"],
)
def test_every_number_beside_a_link_is_read(
    tmp_path: Path, link: Prose, expected: list[Prose]
) -> None:
    """Every number in a link's text and the one after it is held, in that order."""
    readme = Prose(
        "# Go binding\n\nSee " + link.replace("@", "../docs/architecture/CANCELLATION.md") + ".\n"
    )
    found = _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))
    assert found == [_no_heading(section) for section in expected]


def test_a_link_with_empty_text_is_read(tmp_path: Path) -> None:
    """A link whose text is empty is still a link, and the number after it is held."""
    readme = Prose("# Go binding\n\nSee [](../docs/architecture/CANCELLATION.md) § 9.9.\n")
    found = _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go"))))
    assert found == [_no_heading(Prose("9.9"))]


def test_a_line_break_between_text_and_destination_makes_no_link(tmp_path: Path) -> None:
    """A link's destination opens right after its text's bracket: a line break there is no link."""
    readme = Prose(
        "# Go binding\n\nSee [the contract]\n(../docs/architecture/CANCELLATION.md) § 2.2.\n"
    )
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [_CITES_NOTHING]


@pytest.mark.parametrize(
    "separator", [Prose(" "), Prose("\t"), Prose("\n")], ids=["space", "tab", "line-break"]
)
def test_a_link_title_is_not_part_of_the_target(tmp_path: Path, separator: Prose) -> None:
    """A titled link cites the document its path names, the title after any whitespace dropped."""
    readme = Prose(
        "# Go binding\n\nSee [the contract](../docs/architecture/CANCELLATION.md"
        + f'{separator}"Cancellation") § 2.2.\n'
    )
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == list[Prose]()


@pytest.mark.parametrize(
    ("link", "expected"),
    [
        (Prose("[the contract](`x` @)"), [_CITES_NOTHING]),
        (Prose("[the contract](\n`x`\n@)"), [_CITES_NOTHING]),
        (Prose("[the `x` contract](@)"), [_no_heading(Prose("9.9"))]),
    ],
    ids=["destination", "destination-own-line", "text"],
)
def test_a_code_span_in_a_links_parentheses_makes_no_link(
    tmp_path: Path, link: Prose, expected: list[Prose]
) -> None:
    """A code span in a link's parentheses makes no link to cite beside, unlike one in its text."""
    readme = Prose(
        "# Go binding\n\nSee "
        + link.replace("@", "../docs/architecture/CANCELLATION.md")
        + " § 9.9.\n"
    )
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == expected


def test_a_no_break_space_stays_in_the_target(tmp_path: Path) -> None:
    """A citation beside a link to a tracked path holding a no-break space resolves."""
    target = RelPath("docs/architecture/CANCEL\u00a0LATION.md")
    readme = Prose(f"# Go binding\n\nSee [the contract](../{target}) § 2.2.\n")
    repo = plant(tmp_path / "repo", {_SUBJECT: readme, target: _contract(Prose("### 2.2 Go"))})
    assert _run(repo) == list[Prose]()


def test_a_bracket_before_the_link_does_not_open_its_text(tmp_path: Path) -> None:
    """A ``[`` earlier in the prose, such as an interval's, is not part of the link's text."""
    readme = Prose(
        "# Go binding\n\nValues in [0, 255) per § 4 of the spec; see "
        + "[CANCELLATION.md § 2.2](../docs/architecture/CANCELLATION.md).\n"
    )
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == list[Prose]()


@pytest.mark.parametrize(
    "split",
    [
        Prose("See [the contract\n\nat § 9.9](../docs/architecture/CANCELLATION.md)."),
        Prose('See [the contract](../docs/architecture/CANCELLATION.md\n\n"Contract") § 9.9.'),
        Prose("See [the contract](../docs/architecture/CANCELLATION.md)\n\n§ 9.9 is apart."),
    ],
    ids=["text", "destination", "number-after"],
)
def test_a_link_split_by_a_blank_line_cites_nothing(tmp_path: Path, split: Prose) -> None:
    """A blank line ends a paragraph, and no link's text, target or cited number crosses it."""
    readme = Prose(f"# Go binding\n\n{split}\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [_CITES_NOTHING]


def test_a_blank_destination_cites_the_document_it_sits_in(tmp_path: Path) -> None:
    """A link whose destination is whitespace alone cites a section of its own document."""
    readme = Prose("# Go binding\n\n## 2. Lock\n\nSee [the lock]( ) § 3.\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [
        Prose(f"{_SUBJECT}: § 3 cited beside a link to {_SUBJECT} names no heading there")
    ]


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
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == list[Prose]()


def test_subject_without_a_citation_is_a_finding(tmp_path: Path) -> None:
    """The subject carries no section citation beside a link: the scan matched nothing."""
    readme = Prose("# Go binding\n\nSee [the contract](../docs/architecture/CANCELLATION.md).\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [_CITES_NOTHING]


def test_absent_subject_is_a_finding(tmp_path: Path) -> None:
    """The subject is not among the tracked documents: a finding naming it."""
    repo = plant(tmp_path / "repo", {_TARGET: _contract(Prose("### 2.2 Go"))})
    assert _run(repo) == [
        Prose(f"{_SUBJECT}: not among the tracked documents, the subject of this arm")
    ]


def test_target_outside_the_tracked_documents_is_a_finding(tmp_path: Path) -> None:
    """A section cited beside a link to an untracked target cannot resolve: one finding."""
    readme = Prose("# Go binding\n\nSee [notes](../docs/NOTES.md) § 2.2 for the lock.\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [
        Prose(f"{_SUBJECT}: § 2.2 cited beside a link to ../docs/NOTES.md, not a tracked document")
    ]


def test_target_outside_the_repository_is_a_finding(tmp_path: Path) -> None:
    """A section cited beside a link that climbs out of the root is a finding, not an error."""
    readme = Prose("# Go binding\n\nSee [notes](../../OUTSIDE.md) § 2.2 for the lock.\n")
    assert _run(_repo(tmp_path, readme, _contract(Prose("### 2.2 Go")))) == [
        Prose(f"{_SUBJECT}: § 2.2 cited beside a link to ../../OUTSIDE.md, not a tracked document")
    ]


def test_a_citation_in_any_document_is_read(tmp_path: Path) -> None:
    """A numbered citation in a document other than the expected subject is held to its target."""
    repo = _repo(tmp_path, _AFTER_LINK, _contract(Prose("### 2.2 Go")))
    _ = plant(
        repo,
        {
            RelPath("docs/guides/QUICK.md"): Prose(
                "See [the contract §1 Prerequisites]"
                + "(../architecture/CANCELLATION.md#cancellation).\n"
            )
        },
    )
    assert _run(repo) == [
        Prose(f"docs/guides/QUICK.md: § 1 cited beside a link to {_TARGET} names no heading there")
    ]

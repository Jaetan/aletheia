# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shared-opening arm of the documentation gate holds README.md and docs/PITCH.md to one text.

A throwaway repository carries the two documents with the two shared sections identical, each
document spacing them its own way; one edited word in either section, a lost heading or a
missing document is a finding, and the untouched pair is clean.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools.check_docs import run_arm
from tools.docs_arms.shared_opening import PAIRS, findings, section

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

PAIN = Prose(
    """## The pain this removes

Every item below is a bug class that has shipped in real CAN tooling:

- **Wrong endianness** → swapped bytes. → *Proven to honor the byte order.*
- **Sign extension** → a negative reads huge. → *Signed decoding is proven for all widths.*
"""
)
WHY = Prose(
    """## Why switch from cantools / python-can / hand-rolled scripts?

All three decode CAN with **tested** code. Aletheia's decoder is **proven correct**.

| If you use… | The gap Aletheia closes |
|---|---|
| **cantools** | an untested combination can still decode wrong |
"""
)
README = Prose(f"# Aletheia\n\nOne line of pitch.\n\n{PAIN}\n{WHY}\n## What you get\n\nA list.\n")
PITCH = Prose(
    f"# Aletheia: Project Pitch\n\nAnother opening.\n\n---\n\n{PAIN}\n\n{WHY}\n---\n\n"
    + "## What is Aletheia?\n\nThe long answer.\n"
)


def _edited(text: Prose, before: Prose, after: Prose) -> Prose:
    """Return ``text`` with ``before`` replaced by ``after``: one document moving alone."""
    return Prose(str(text).replace(before, after))


def _repository(tmp_path: Path, readme: Prose, pitch: Prose | None) -> Path:
    """Commit ``readme`` as README.md and, when given, ``pitch`` as docs/PITCH.md."""
    repo = tmp_path / "repo"
    (repo / "docs").mkdir(parents=True)
    _ = (repo / "README.md").write_text(readme, encoding="utf-8")
    if pitch is not None:
        _ = (repo / "docs" / "PITCH.md").write_text(pitch, encoding="utf-8")
    git(repo, "init", "-q")
    _ = commit(repo, "documents")
    return repo


def _run(repo: Path) -> list[Prose]:
    """Run the arm as the gate does, over the tracked Markdown documents of ``repo``."""
    return run_arm(findings, repo)


def test_identical_sections_spaced_differently_are_clean(tmp_path: Path) -> None:
    """Blank lines and horizontal rules are each document's own and do not count as drift."""
    assert not _run(_repository(tmp_path, README, PITCH))


@pytest.mark.parametrize(
    ("before", "after"),
    [
        ("Signed decoding is proven for all widths", "Signed decoding is tested for all widths"),
        ("Aletheia's decoder is **proven correct**", "Aletheia's decoder is **proven** correct"),
    ],
)
def test_one_edited_word_in_the_pitch_is_a_finding(
    tmp_path: Path, before: Prose, after: Prose
) -> None:
    """A section refreshed in one document and not the other is reported against README.md."""
    found = _run(_repository(tmp_path, README, _edited(PITCH, before, after)))
    assert len(found) == 1
    assert found[0].startswith("README.md: ")
    assert "docs/PITCH.md" in found[0]
    assert before in found[0]
    assert after in found[0]


def test_an_edited_readme_is_a_finding_too(tmp_path: Path) -> None:
    """Drift is symmetric: the README moving alone is the same defect, each side's line named."""
    found = _run(
        _repository(tmp_path, _edited(README, Prose("swapped bytes"), Prose("wrong bytes")), PITCH)
    )
    swapped = "- **Wrong endianness** → swapped bytes. → *Proven to honor the byte order.*"
    wrong = swapped.replace("swapped", "wrong")
    assert found == [
        Prose(
            "README.md: '## The pain this removes' is not the text docs/PITCH.md carries; "
            + f"only in README.md: {wrong}; only in docs/PITCH.md: {swapped}"
        )
    ]


@pytest.mark.parametrize(
    "rule", [Prose(r) for r in ("***", "___", "- - -", "-  -  -", "* * *", "_\t_\t_", "-----")]
)
def test_every_horizontal_rule_spelling_is_spacing(tmp_path: Path, rule: Prose) -> None:
    """A horizontal rule in any spelling is the document's own spacing, not drift."""
    pitch = _edited(PITCH, Prose(f"{WHY}\n---\n"), Prose(f"{WHY}\n{rule}\n"))
    assert not _run(_repository(tmp_path, README, pitch))


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("## A\nx\n# B\ny"), [Prose("## A"), Prose("x")]),
        (Prose("## A\nx\n## B\ny"), [Prose("## A"), Prose("x")]),
        (
            Prose("## A\nx\n### A.1\ny\n## B\nz"),
            [Prose("## A"), Prose("x"), Prose("### A.1"), Prose("y")],
        ),
    ],
    ids=["shallower", "same-level", "deeper"],
)
def test_a_section_ends_at_a_heading_of_its_level_or_shallower(
    text: Prose, expected: list[Prose]
) -> None:
    """A deeper heading stays inside the section; one of the same level or shallower ends it."""
    assert section(text, Prose("## A")) == expected


@pytest.mark.parametrize(
    "line",
    [Prose(r) for r in ("**", "-*_", "*** bold claim")],
    ids=["two-characters", "mixed-characters", "text-after-the-rule"],
)
def test_a_line_short_of_a_horizontal_rule_is_kept(line: Prose) -> None:
    """Two rule characters, a mix of them, or a rule followed by text: content, not spacing."""
    assert section(Prose(f"## A\n{line}\nx"), Prose("## A")) == [Prose("## A"), line, Prose("x")]


def test_a_lost_heading_is_a_finding(tmp_path: Path) -> None:
    """A document that no longer carries a shared heading has nothing to compare."""
    found = _run(
        _repository(tmp_path, README, _edited(PITCH, Prose("## Why switch"), Prose("## Why move")))
    )
    assert found == [
        Prose(
            "docs/PITCH.md: no longer carries "
            + "'## Why switch from cantools / python-can / hand-rolled scripts?', "
            + "which README.md still does"
        )
    ]


def test_a_heading_both_documents_lost_is_a_finding_for_each(tmp_path: Path) -> None:
    """A heading neither document carries is reported against both, neither said to keep it."""
    readme = _edited(README, Prose("## Why switch"), Prose("## Why move"))
    pitch = _edited(PITCH, Prose("## Why switch"), Prose("## Why move"))
    heading = "'## Why switch from cantools / python-can / hand-rolled scripts?'"
    assert _run(_repository(tmp_path, readme, pitch)) == [
        Prose(f"README.md: no longer carries {heading}, nor does docs/PITCH.md"),
        Prose(f"docs/PITCH.md: no longer carries {heading}, nor does README.md"),
    ]


def test_a_missing_document_is_a_finding(tmp_path: Path) -> None:
    """The vacuous guard: a pitch absent from the tree is reported, not passed over."""
    found = _run(_repository(tmp_path, README, None))
    assert len(found) == 1
    assert found[0].startswith("docs/PITCH.md: not tracked")


def test_the_pair_names_the_two_front_doors() -> None:
    """The arm's subject is the README and the pitch, and the two sections they open with."""
    assert [(pair.first, pair.second) for pair in PAIRS] == [("README.md", "docs/PITCH.md")]
    assert all(len(pair.headings) == 2 for pair in PAIRS)


def test_a_heading_the_readme_lost_names_the_pitch_as_keeping_it(tmp_path: Path) -> None:
    """The finding names the document that lost the heading and the one that still carries it."""
    readme = _edited(README, Prose("## Why switch"), Prose("## Why move"))
    assert _run(_repository(tmp_path, readme, PITCH)) == [
        Prose(
            "README.md: no longer carries "
            + "'## Why switch from cantools / python-can / hand-rolled scripts?', "
            + "which docs/PITCH.md still does"
        )
    ]

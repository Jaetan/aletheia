# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The shared-opening arm of the documentation gate holds README.md and docs/PITCH.md to one text.

A planted tree carries the two documents with the two shared sections identical, each
document spacing them its own way; one edited line in either section, a lost heading or an
untracked document is a finding, and the untouched pair is clean.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.shared_opening import PAIRS, SharedOpening, findings, section

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Collection
    from pathlib import Path

README_MD = RelPath("README.md")
PITCH_MD = RelPath("docs/PITCH.md")
PAIN_HEADING = Prose("## The pain this removes")
WHY_HEADING = Prose("## Why switch from cantools / python-can / hand-rolled scripts?")
SWAPPED = Prose("- **Wrong endianness** → swapped bytes. → *Proven to honor the byte order.*")
SIGNED = Prose(
    "- **Sign extension** → a negative reads huge. → *Signed decoding is proven for all widths.*"
)
DECODER = Prose(
    "All three decode CAN with **tested** code. Aletheia's decoder is **proven correct**."
)
PAIN = Prose(
    f"""{PAIN_HEADING}

Every item below is a bug class that has shipped in real CAN tooling:

{SWAPPED}
{SIGNED}
"""
)
WHY = Prose(
    f"""{WHY_HEADING}

{DECODER}

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


def _run(
    tmp_path: Path,
    readme: Prose = README,
    pitch: Prose = PITCH,
    *,
    untracked: Collection[RelPath] = (),
) -> list[Prose]:
    """Run the arm as the gate does over README.md and docs/PITCH.md planted with these texts."""
    repo = plant(tmp_path / "repo", {README_MD: readme, PITCH_MD: pitch})
    return run_planted(findings, repo, untracked=untracked)


def _drift(heading: Prose, readme_only: Prose, pitch_only: Prose) -> Prose:
    """Return the finding for ``heading`` drifting, given each document's lines the other lacks."""
    return Prose(
        f"README.md: '{heading}' is not the text docs/PITCH.md carries; "
        + f"only in README.md: {readme_only}; only in docs/PITCH.md: {pitch_only}"
    )


def test_identical_sections_spaced_differently_are_clean(tmp_path: Path) -> None:
    """Blank lines and horizontal rules are each document's own and do not count as drift."""
    assert _run(tmp_path) == list[Prose]()


@pytest.mark.parametrize(
    ("heading", "line", "after"),
    [
        (PAIN_HEADING, SIGNED, _edited(SIGNED, Prose("proven"), Prose("tested"))),
        (
            WHY_HEADING,
            DECODER,
            _edited(DECODER, Prose("proven correct**"), Prose("proven** correct")),
        ),
    ],
    ids=["pain", "why"],
)
def test_one_edited_word_in_the_pitch_is_a_finding(
    tmp_path: Path, heading: Prose, line: Prose, after: Prose
) -> None:
    """A section refreshed in one document and not the other is reported against README.md."""
    pitch = _edited(PITCH, line, after)
    assert _run(tmp_path, pitch=pitch) == [_drift(heading, line, after)]


def test_an_edited_readme_is_a_finding_too(tmp_path: Path) -> None:
    """Drift is symmetric: the README moving alone is the same defect, each side's line named."""
    wrong = _edited(SWAPPED, Prose("swapped"), Prose("wrong"))
    assert _run(tmp_path, _edited(README, SWAPPED, wrong)) == [_drift(PAIN_HEADING, wrong, SWAPPED)]


def test_every_line_a_side_lacks_is_listed(tmp_path: Path) -> None:
    """Each side lists every line the other lacks, in its own order, joined by semicolons."""
    wrong = _edited(SWAPPED, Prose("swapped"), Prose("wrong"))
    large = _edited(SIGNED, Prose("huge"), Prose("large"))
    readme = _edited(_edited(README, SWAPPED, wrong), SIGNED, large)
    assert _run(tmp_path, readme) == [
        _drift(PAIN_HEADING, Prose(f"{wrong}; {large}"), Prose(f"{SWAPPED}; {SIGNED}"))
    ]


EXTRA = Prose("- **Overflow** → a value wraps. → *Proven to stay in range.*")
GAINS = (SIGNED, Prose(f"{SIGNED}\n{EXTRA}"))
NOTHING = Prose("nothing")


@pytest.mark.parametrize(
    ("readme", "pitch", "readme_only", "pitch_only"),
    [
        (_edited(README, *GAINS), PITCH, EXTRA, NOTHING),
        (README, _edited(PITCH, *GAINS), NOTHING, EXTRA),
        (
            README,
            _edited(PITCH, Prose(f"{SWAPPED}\n{SIGNED}"), Prose(f"{SIGNED}\n{SWAPPED}")),
            NOTHING,
            NOTHING,
        ),
    ],
    ids=["readme-gains-a-line", "pitch-gains-a-line", "lines-reordered"],
)
def test_a_side_with_no_line_of_its_own_shows_nothing(
    tmp_path: Path, readme: Prose, pitch: Prose, readme_only: Prose, pitch_only: Prose
) -> None:
    """A side with no line the other lacks shows nothing, and a reordering nothing on both."""
    assert _run(tmp_path, readme, pitch) == [_drift(PAIN_HEADING, readme_only, pitch_only)]


@pytest.mark.parametrize(
    "moved",
    [Prose(f"  {SIGNED}"), Prose(f"{SIGNED}  ")],
    ids=["nested-under-the-item-above", "trailing-blanks"],
)
def test_indentation_and_trailing_blanks_are_content(tmp_path: Path, moved: Prose) -> None:
    """Indentation or trailing blanks one document alone gives a line are drift, not spacing."""
    assert _run(tmp_path, pitch=_edited(PITCH, SIGNED, moved)) == [
        _drift(PAIN_HEADING, SIGNED, moved)
    ]


@pytest.mark.parametrize(
    "rule",
    [
        Prose(r)
        for r in (
            "***",
            "___",
            "- - -",
            "-  -  -",
            "* * *",
            "_\t_\t_",
            "-----",
            " ---",
            "   ***",
            "--- ",
            "___\t",
            "- - - ",
        )
    ],
)
def test_every_horizontal_rule_spelling_is_spacing(tmp_path: Path, rule: Prose) -> None:
    """A rule in any spelling, up to three blanks before it and any after, is spacing, not drift."""
    pitch = _edited(PITCH, Prose(f"{WHY}\n---\n"), Prose(f"{WHY}\n{rule}\n"))
    assert _run(tmp_path, pitch=pitch) == list[Prose]()


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
    """A document that does not carry a shared heading has nothing to compare."""
    found = _run(tmp_path, pitch=_edited(PITCH, Prose("## Why switch"), Prose("## Why move")))
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
    assert _run(tmp_path, readme, pitch) == [
        Prose(f"README.md: no longer carries {heading}, nor does docs/PITCH.md"),
        Prose(f"docs/PITCH.md: no longer carries {heading}, nor does README.md"),
    ]


@pytest.mark.parametrize(
    ("untracked", "expected"),
    [
        (
            [PITCH_MD],
            [Prose("docs/PITCH.md: not tracked, so the opening README.md shares is uncheckable")],
        ),
        (
            [README_MD],
            [Prose("README.md: not tracked, so the opening docs/PITCH.md shares is uncheckable")],
        ),
        (
            [README_MD, PITCH_MD],
            [
                Prose("README.md: not tracked, so the opening docs/PITCH.md shares is uncheckable"),
                Prose("docs/PITCH.md: not tracked, so the opening README.md shares is uncheckable"),
            ],
        ),
    ],
    ids=["pitch", "readme", "both"],
)
def test_an_untracked_document_is_a_finding_naming_its_partner(
    tmp_path: Path, untracked: Collection[RelPath], expected: list[Prose]
) -> None:
    """The vacuous guard: an untracked document of the pair is reported, and nothing compared."""
    assert _run(tmp_path, untracked=untracked) == expected


def test_a_drifting_line_is_shown_to_its_first_120_characters(tmp_path: Path) -> None:
    """A long line one side alone holds is cut to its first 120 characters in the finding."""
    long = Prose(f"{SIGNED} {'x' * 150}")
    assert _run(tmp_path, pitch=_edited(PITCH, SIGNED, long)) == [
        _drift(PAIN_HEADING, SIGNED, Prose(str(long)[:120]))
    ]


def test_the_pair_names_the_two_front_doors() -> None:
    """The arm's subject is the README and the pitch, and the two sections they open with."""
    assert (SharedOpening(README_MD, PITCH_MD, (PAIN_HEADING, WHY_HEADING)),) == PAIRS


def test_a_heading_the_readme_lost_names_the_pitch_as_keeping_it(tmp_path: Path) -> None:
    """The finding names the document that lost the heading and the one that still carries it."""
    readme = _edited(README, Prose("## Why switch"), Prose("## Why move"))
    assert _run(tmp_path, readme) == [
        Prose(
            "README.md: no longer carries "
            + "'## Why switch from cantools / python-can / hand-rolled scripts?', "
            + "which docs/PITCH.md still does"
        )
    ]


def test_a_tracked_document_the_work_tree_lacks_is_a_finding(tmp_path: Path) -> None:
    """A document of the pair git tracks and the work tree lacks is named as unread."""
    repo = plant(tmp_path / "repo", {PITCH_MD: PITCH})
    assert run_planted(findings, repo, absent={README_MD}) == [
        Prose("README.md: could not be read, so what it says is unchecked"),
        Prose("README.md: could not be read, so the opening docs/PITCH.md shares is uncheckable"),
    ]

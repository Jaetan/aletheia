# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_changelog.cut_problem``: a release cut read against its base.

The cut is docs/development/RELEASE.md's: the base's ``## [Unreleased]`` lines
under ``## [X.Y.Z] — YYYY-MM-DD`` below a fresh empty ``## [Unreleased]``, no
other line changed, the version newer than every release the base holds.  Each
way a CHANGELOG falls short of one is named, with the cut as the fix.
"""

from __future__ import annotations

import pytest
from _changelog_texts import CUT, CUT_TAIL, ENTRY, ENTRY_TAIL, SHAPE_FIX, VERSION

from tools.check_changelog import CutProblem, cut_problem

from aletheia.common_types import Prose

OLDER = Prose("\n## [1.2.2] — 2026-01-01\n\n- **Old.** Kept.\n")
HEAD = "# Changelog\n\n## [Unreleased]\n\n"
# A preamble quoting a later version's heading and holding one deeper than a release's.
QUOTED = "# Changelog\n\n> ## [9.9.9] — 2026-01-01\n\n### [9.9.9] — 2026-01-01\n"


@pytest.mark.parametrize(
    ("changelog", "base"),
    [
        (CUT, ENTRY),
        (Prose(CUT + OLDER), Prose(ENTRY + OLDER)),
        (
            Prose(QUOTED + CUT_TAIL),
            Prose(QUOTED + ENTRY_TAIL),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n### Fixed\n- **A bug.** Gone.\n"),
            Prose("# Changelog\n\n## [Unreleased]\n### Fixed\n- **A bug.** Gone.\n"),
        ),
        (
            Prose("# Change\u2028log\n" + CUT_TAIL),
            Prose("# Change\u2028log\n" + ENTRY_TAIL),
        ),
        (
            Prose(
                "# Changelog\n\n## [Unreleased]\n\t \n## [1.2.3] — 2026-10-12\n\n### Fixed\n\n"
                + "- **A bug.** Gone.\n"
            ),
            ENTRY,
        ),
    ],
    ids=[
        "cut",
        "older-release-kept",
        "quoted-and-deeper-are-no-release",
        "no-blank-under-the-headings",
        "line-separator-in-the-preamble",
        "tab-and-space-are-blank",
    ],
)
def test_a_release_cut_has_no_problem(changelog: Prose, base: Prose) -> None:
    """The base's unreleased lines under the dated heading, nothing else moved, is the cut."""
    assert cut_problem(changelog, base, VERSION) is None


_WANTED = "'## [1.2.3] — YYYY-MM-DD'"


@pytest.mark.parametrize(
    ("changelog", "found"),
    [
        (
            "# Changelog\n\n## [Unreleased]\n\n- **A bug.** Gone.\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n- **A bug.** Gone.\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            HEAD + "[x]: https://example.com\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        (
            HEAD + "\u00a0\n\n## [1.2.3] — 2026-10-12\n",
            "is not empty under '## [Unreleased]'",
        ),
        ("# Changelog\n\n## [Unreleased]\n", f"has no {_WANTED} heading after '## [Unreleased]'"),
        (
            "# Changelog\n\n## [Unreleased]\n\n# [1.2.3] — 2026-10-12\n",
            f"has no {_WANTED} heading after '## [Unreleased]'",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.2] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[1.2.2] — 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3]\n",
            f"heads the section after '## [Unreleased]' '[1.2.3]', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] - 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[1.2.3] - 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 20261012\n",
            f"heads the section after '## [Unreleased]' '[1.2.3] — 20261012', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [01.2.3] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[01.2.3] — 2026-10-12', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — \u0662\u0660\u0662\u0666-10-12\n",
            "heads the section after '## [Unreleased]' "
            + "'[1.2.3] — \u0662\u0660\u0662\u0666-10-12', not "
            + _WANTED,
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [Other]\n\n## [1.2.3] — 2026-10-12\n",
            f"heads the section after '## [Unreleased]' '[Other]', not {_WANTED}",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-13-40\n",
            "dates release 1.2.3 '2026-13-40', which is not a calendar date",
        ),
        (
            "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n## [Unreleased]\n",
            "has 2 '## [Unreleased]' sections, not one",
        ),
        ("# Changelog\n", "has 0 '## [Unreleased]' sections, not one"),
    ],
    ids=[
        "entries-left",
        "entry-under-the-heading",
        "definition-left",
        "no-break-space-left",
        "no-heading",
        "level-one",
        "another-version",
        "undated",
        "hyphen",
        "basic-date",
        "leading-zero",
        "arabic-indic-date",
        "heading-between",
        "not-a-date",
        "two-unreleased",
        "no-unreleased",
    ],
)
def test_a_changelog_short_of_the_cut_says_how(changelog: Prose, found: Prose) -> None:
    """Each way a CHANGELOG falls short of the cut's shape is named, with the cut as the fix."""
    assert cut_problem(changelog, ENTRY, VERSION) == CutProblem(found, SHAPE_FIX)


_NEWER = "names release 1.2.3, not newer than the base's newest release, "
MOVED = Prose(
    "holds under release 1.2.3 other lines, or the same in another order, than the base's "
    + "'## [Unreleased]' held"
)
# Two older releases: by SemVer 1.2.10 is the newer, as text 1.2.9 is.
SEMVER = Prose(
    "\n## [1.2.10] — 2026-09-02\n\n- **Later.** Kept.\n"
    + "\n## [1.2.9] — 2026-09-01\n\n- **Old.** Kept.\n"
)


@pytest.mark.parametrize(
    ("changelog", "base", "problem"),
    [
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n### Fixed\n\n- **B.** b\n- **A.** a\n"),
            Prose(HEAD + "### Fixed\n\n- **A.** a\n- **B.** b\n"),
            CutProblem(MOVED, SHAPE_FIX),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n### Added\n\n- **A.** a\n\n### Fixed\n\n"),
            Prose(HEAD + "### Added\n\n### Fixed\n\n- **A.** a\n\n"),
            CutProblem(MOVED, SHAPE_FIX),
        ),
        (
            Prose("# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "- **New.** Slipped in.\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.2] — 2026-01-01\n\n- **Old.** Edited.\n"),
            Prose(ENTRY + OLDER),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose("# Change log\n" + CUT_TAIL),
            ENTRY,
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(
                "# Changelog\n"
                + OLDER
                + "\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n"
                + "### Fixed\n\n- **A bug.** Gone.\n"
            ),
            Prose(ENTRY + OLDER),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.4] — 2026-09-01\n\n- **Later.** Kept.\n" + OLDER),
            Prose(ENTRY + "\n## [1.2.4] — 2026-09-01\n\n- **Later.** Kept.\n" + OLDER),
            CutProblem(
                Prose(_NEWER + "1.2.4"),
                Prose(
                    "Prepare a version newer than 1.2.4, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-09-01\n\n- **A bug.** Gone.\n"
            ),
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n## [1.2.3] — 2026-09-01\n\n- **A bug.** Gone.\n"
            ),
            CutProblem(
                Prose(_NEWER + "1.2.3"),
                Prose(
                    "Prepare a version newer than 1.2.3, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            CUT,
            Prose(ENTRY + "\n## [Unreleased]\n"),
            CutProblem(
                Prose("is cut from a base with 2 '## [Unreleased]' sections, not one"),
                Prose("Merge the base's '## [Unreleased]' sections into one on main first."),
            ),
        ),
        (
            CUT,
            Prose("# Changelog\n"),
            CutProblem(
                Prose("is cut from a base with 0 '## [Unreleased]' sections, not one"),
                Prose("Merge the base's '## [Unreleased]' sections into one on main first."),
            ),
        ),
        (
            Prose(CUT + SEMVER),
            Prose(ENTRY + SEMVER),
            CutProblem(
                Prose(_NEWER + "1.2.10"),
                Prose(
                    "Prepare a version newer than 1.2.10, in the commit, the title and the heading."
                ),
            ),
        ),
        (
            Prose("# Changelog\n\n## [1.2.3] — 2026-10-12\n" + CUT_TAIL),
            ENTRY,
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n"),
            ENTRY,
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose(HEAD + "## [1.2.3] — 2026-10-12\n\n- a\n- b\u0085- c\n"),
            Prose(HEAD + "- a\u0085- b\n- c\n"),
            CutProblem(
                MOVED,
                SHAPE_FIX,
            ),
        ),
        (
            Prose("## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n- a\n\n# Changelog\n\n"),
            Prose("# Changelog\n\n## [Unreleased]\n\n- a\n"),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(
                "# Changelog\n\n## [1.0.0] — 2026-01-01\n\n- old\n## [Unreleased]\n\n"
                + "## [1.2.3] — 2026-10-12\n\n- a\n- b\n"
            ),
            Prose(
                "# Changelog\n\n## [Unreleased]\n\n- a\n- b\n\n## [1.0.0] — 2026-01-01\n\n- old\n"
            ),
            CutProblem(
                Prose("changes text outside '## [Unreleased]' and the new release's section"),
                SHAPE_FIX,
            ),
        ),
        (
            Prose(CUT + "\n## [1.2.3] — 2026-01-01 and earlier\n\n- **Old.** Kept.\n"),
            Prose(ENTRY + "\n## [1.2.3] — 2026-01-01 and earlier\n\n- **Old.** Kept.\n"),
            CutProblem(
                Prose(_NEWER + "1.2.3"),
                Prose(
                    "Prepare a version newer than 1.2.3, in the commit, the title and the heading."
                ),
            ),
        ),
    ],
    ids=[
        "entries-reordered",
        "entry-moved-to-another-category",
        "entries-dropped",
        "entry-added",
        "older-release-edited",
        "preamble-edited",
        "unreleased-below-older",
        "not-newer",
        "already-released",
        "base-two-unreleased",
        "base-no-unreleased",
        "semver-order",
        "release-heading-also-above",
        "blank-line-added",
        "entry-boundary-moved-across-a-next-line",
        "title-moved-below-the-release",
        "release-placed-below-an-older-one",
        "older-heading-in-another-form",
    ],
)
def test_a_cut_that_differs_from_its_base_says_how(
    changelog: Prose, base: Prose, problem: CutProblem
) -> None:
    """Against the base, the cut moves exactly its unreleased lines, and to a newer version."""
    assert cut_problem(changelog, base, VERSION) == problem

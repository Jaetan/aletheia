# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The retired-document arm of the documentation gate, run over planted trees.

The arm holds that the dependency ledger has one home, the Dependencies and
Licenses section of the building guide: no copy of the retired ledger file is
tracked, and no tracked file outside the changelog names it. Each test plants
one defect and reads the finding, or plants none and reads an empty list. The
retired name is taken from the arm, so this file does not itself carry it.
"""

from __future__ import annotations

from pathlib import Path

import pytest
from _planted_tree import run_planted

from tools._common import RelPath
from tools.docs_arms import retired_document
from tools.docs_arms.retired_document import LEDGER, RECORD_OF_THE_MOVE, RETIRED_DOCUMENT, findings

from aletheia.common_types import Prose

_SECTION_LINE = "## Dependencies and Licenses\n"


def _repo(tmp_path: Path) -> Path:
    """Return a planted tree: the ledger in its one home, nothing naming the old file."""
    repo = tmp_path / "repo"
    (repo / "docs" / "development").mkdir(parents=True)
    _ = (repo / LEDGER).write_text(f"# Building\n\n{_SECTION_LINE}\nA table.\n", encoding="utf-8")
    _ = (repo / "README.md").write_text(
        "# Front door\n\nSee the building guide.\n", encoding="utf-8"
    )
    _ = (repo / RECORD_OF_THE_MOVE).write_text("# Changelog\n\nA record.\n", encoding="utf-8")
    _ = (repo / "tool.py").write_text("print('a line of code')\n", encoding="utf-8")
    return repo


def _run(repo: Path) -> list[Prose]:
    """Run the arm over ``repo`` as the gate does, with every tracked path and Markdown file."""
    return run_planted(findings, repo)


def test_a_clean_tree_has_no_finding(tmp_path: Path) -> None:
    """The ledger in its home, the old file untracked and unnamed: no finding."""
    assert not _run(_repo(tmp_path))


def test_the_changelog_may_name_the_retired_file(tmp_path: Path) -> None:
    """The changelog records the move, so its mention of the old file is no finding."""
    repo = _repo(tmp_path)
    with (repo / RECORD_OF_THE_MOVE).open("a", encoding="utf-8") as record:
        _ = record.write(f"\nThe ledger moved out of {RETIRED_DOCUMENT}.\n")
    assert not _run(repo)


def test_a_tracked_copy_of_the_retired_file_is_a_finding(tmp_path: Path) -> None:
    """A tracked file bearing the retired name is a second home for the ledger."""
    repo = _repo(tmp_path)
    _ = (repo / RETIRED_DOCUMENT).write_text("# Dependencies\n", encoding="utf-8")
    assert _run(repo) == [
        f"{RETIRED_DOCUMENT}: is tracked, a second home for the ledger beside {LEDGER}"
    ]


def test_a_document_naming_the_retired_file_is_a_finding(tmp_path: Path) -> None:
    """A document sending its reader to the old file names the file and the line."""
    repo = _repo(tmp_path)
    with (repo / "README.md").open("a", encoding="utf-8") as readme:
        _ = readme.write(f"\nLicenses are listed in {RETIRED_DOCUMENT}.\n")
    assert _run(repo) == [
        f"README.md: line 5 names {RETIRED_DOCUMENT}, whose ledger lives in {LEDGER}"
    ]


def test_a_code_file_naming_the_retired_file_is_a_finding(tmp_path: Path) -> None:
    """The claim covers every tracked file, so a mention in code is found too."""
    repo = _repo(tmp_path)
    _ = (repo / "tool.py").write_text(f"# writes {RETIRED_DOCUMENT}\n", encoding="utf-8")
    assert _run(repo) == [
        f"tool.py: line 1 names {RETIRED_DOCUMENT}, whose ledger lives in {LEDGER}"
    ]


def test_a_mention_shown_as_code_is_a_finding(tmp_path: Path) -> None:
    """An inline code span naming the old file still sends the reader there."""
    repo = _repo(tmp_path)
    with (repo / "README.md").open("a", encoding="utf-8") as readme:
        _ = readme.write(f"\nThe former `{RETIRED_DOCUMENT}` is gone.\n")
    assert len(_run(repo)) == 1


def test_a_ledger_without_its_section_is_a_finding(tmp_path: Path) -> None:
    """The guide without the Dependencies and Licenses heading gives the ledger no home."""
    repo = _repo(tmp_path)
    _ = (repo / LEDGER).write_text("# Building\n\n## Toolchain\n", encoding="utf-8")
    assert _run(repo) == [
        f"{LEDGER}: has no Dependencies and Licenses section, the ledger's one home"
    ]


def test_a_ledger_whose_heading_differs_in_case_is_a_finding(tmp_path: Path) -> None:
    """The section is named in its own case; a heading spelled in another case is not it."""
    repo = _repo(tmp_path)
    _ = (repo / LEDGER).write_text("# Building\n\n## dependencies and licenses\n", encoding="utf-8")
    assert _run(repo) == [
        f"{LEDGER}: has no Dependencies and Licenses section, the ledger's one home"
    ]


def test_a_ledger_whose_heading_sits_in_a_fence_is_a_finding(tmp_path: Path) -> None:
    """A heading shown inside a code fence is an example, not the section."""
    repo = _repo(tmp_path)
    _ = (repo / LEDGER).write_text(f"# Building\n\n```\n{_SECTION_LINE}```\n", encoding="utf-8")
    assert len(_run(repo)) == 1


def test_a_tree_without_the_guide_is_a_finding(tmp_path: Path) -> None:
    """A tree with no building guide gives the scan nothing it expects."""
    repo = _repo(tmp_path)
    (repo / LEDGER).unlink()
    assert _run(repo) == [f"{LEDGER}: is not tracked, the ledger has no home"]


def test_a_tracked_file_gone_from_the_worktree_is_a_finding(tmp_path: Path) -> None:
    """A tracked file that cannot be read is reported, never passed as clean."""
    repo = _repo(tmp_path)
    (repo / "tool.py").unlink()
    assert run_planted(findings, repo, absent={RelPath("tool.py")}) == [
        "tool.py: could not be read, so its lines are unchecked"
    ]


@pytest.mark.parametrize(
    "anchor",
    [
        Prose('<a id="dependencies-and-licenses"></a>\n'),
        Prose('```\n<a id="dependencies-and-licenses"></a>\n```\n'),
    ],
    ids=["html", "fenced-html"],
)
def test_a_ledger_with_only_an_html_anchor_is_a_finding(tmp_path: Path, anchor: Prose) -> None:
    """An HTML anchor spelling the section's slug is no heading, so the section is missing."""
    repo = _repo(tmp_path)
    _ = (repo / LEDGER).write_text(f"# Building\n\n{anchor}\nA table.\n", encoding="utf-8")
    assert _run(repo) == [
        f"{LEDGER}: has no Dependencies and Licenses section, the ledger's one home"
    ]


@pytest.mark.parametrize(
    "name",
    [RelPath(f"PY_{RETIRED_DOCUMENT}"), RelPath(f"{RETIRED_DOCUMENT}x")],
    ids=["prefix", "suffix"],
)
def test_a_longer_name_holding_the_retired_one_is_no_finding(tmp_path: Path, name: RelPath) -> None:
    """Only the retired name as a whole word is a mention; a longer name is another file."""
    repo = _repo(tmp_path)
    with (repo / "README.md").open("a", encoding="utf-8") as readme:
        _ = readme.write(f"\nSee {name}.\n")
    assert not _run(repo)


def test_the_arm_s_own_source_is_left_out() -> None:
    """The arm names the retired file to look for it, so its own lines are no finding."""
    source = Path(retired_document.__file__).resolve()
    root = source.parents[2]
    assert RETIRED_DOCUMENT in source.read_text(encoding="utf-8")
    own = RelPath(source.relative_to(root).as_posix())
    assert not findings(root, [own], {LEDGER: Prose(f"# Building\n\n{_SECTION_LINE}")})


def test_a_heading_holding_more_than_the_section_name_is_not_its_home(tmp_path: Path) -> None:
    """The ledger's home is the heading that reads the section's name, not one containing it."""
    repo = _repo(tmp_path)
    text = "# Building\n\n## Dependencies and Licenses (old)\n"
    _ = (repo / LEDGER).write_text(text, encoding="utf-8")
    assert _run(repo) == [
        f"{LEDGER}: has no Dependencies and Licenses section, the ledger's one home"
    ]


def test_the_section_may_be_the_guide_s_first_heading(tmp_path: Path) -> None:
    """A guide opening on the section is its home all the same."""
    repo = _repo(tmp_path)
    _ = (repo / LEDGER).write_text(f"{_SECTION_LINE}\nA table.\n", encoding="utf-8")
    assert not _run(repo)

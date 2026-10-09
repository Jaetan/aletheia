# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the documentation-gate arm holding the building guide to one line per paragraph.

Each test plants a tree whose ``docs/development/BUILDING.md``
carries one shape, runs the arm as the gate does, and reads its findings.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import run_planted

from tools._common import RelPath
from tools.docs_arms.one_line_paragraphs import SUBJECT, findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

CLEAN = Prose(
    """\
# Building

One paragraph, one line, however long it runs across the screen.

## Steps

- first item
- second item
1. a numbered item

> a quote on one line

| a | b |
|---|---|
| 1 | 2 |

---

```sh
a fenced line
   an indented fenced line
another fenced line
```

`code` opens this line and the span is not a continuation.
"""
)


def _repo(tmp_path: Path, text: Prose | None) -> Path:
    """Return a planted tree whose building guide reads ``text``, or has no guide when None."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _ = (repo / "README.md").write_text("# Readme\n", encoding="utf-8")
    if text is not None:
        guide = repo / SUBJECT
        guide.parent.mkdir(parents=True)
        _ = guide.write_text(text, encoding="utf-8")
    return repo.resolve()


def _run(repo: Path) -> list[Prose]:
    """Run the arm over ``repo`` as the gate hands it: root, tracked paths, Markdown documents."""
    return run_planted(findings, repo)


def test_a_guide_of_one_line_paragraphs_is_clean(tmp_path: Path) -> None:
    """Headings, items, table rows and a fence may follow one another; nothing is found."""
    assert _run(_repo(tmp_path, CLEAN)) == list[Prose]()


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (
            Prose("# Building\n\nA paragraph that runs\nonto a second line.\n"),
            Prose(f"{SUBJECT}: line 4 wraps the paragraph above it"),
        ),
        (
            Prose("# Building\n\n- an item\n  continued on an indented line\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\nA paragraph\n\tcontinued on a tab-indented line\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\n- an item\nlazily continued at the margin\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\n> a quote\n> wrapped onto a second line\n"),
            Prose(f"{SUBJECT}: line 4 wraps the blockquote above it"),
        ),
        (
            Prose("# Building\n\n> a quote\nlazily continued at the margin\n"),
            Prose(f"{SUBJECT}: line 4 wraps the blockquote above it"),
        ),
        (
            Prose("# Building\n\n    indented after a blank line\n"),
            Prose(f"{SUBJECT}: line 3 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n  indented under a heading\n"),
            Prose(f"{SUBJECT}: line 2 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\n> a quote\n  indented under it\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\n| a | b |\n  indented under a table row\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
        (
            Prose("# Building\n\n---\n  indented under a break\n"),
            Prose(f"{SUBJECT}: line 4 continues a list item or paragraph"),
        ),
    ],
    ids=[
        "prose",
        "indented line",
        "tab-indented line",
        "lazy item",
        "quote",
        "lazy quote",
        "indented after a blank line",
        "indented under a heading",
        "indented under a quote",
        "indented under a table row",
        "indented under a break",
    ],
)
def test_a_wrapped_paragraph_is_found_by_line(tmp_path: Path, text: Prose, expected: Prose) -> None:
    """The line that continues a block is named, and it alone; an indented line, under anything."""
    assert _run(_repo(tmp_path, text)) == [expected]


@pytest.mark.parametrize(
    "text",
    [
        Prose("# Building\n\nOne paragraph.\n\nA second paragraph after a blank line.\n"),
        Prose("# Building\n\n###### A sixth-level heading\nA paragraph right under it.\n"),
        Prose("# Building\n\n1. a numbered item\n2. a second numbered item\n"),
        Prose("# Building\n\n9. a ninth item\n10. a tenth item\n"),
        Prose("# Building\n\n* a starred item\n* a second starred item\n"),
        Prose("# Building\n\n---  \nA paragraph right under a break with trailing spaces.\n"),
        Prose("# Building\n\n- an outer item\n  - a nested item\n\t- a tab-nested item\n"),
        Prose("# Building\n\n> a quote\n- an item right under it\n"),
        Prose("# Building\n\n> a quote\n## A heading right under it\n"),
        Prose("# Building\n\n> a quote\n| a | b |\n"),
        Prose("# Building\n\n> a quote\n---\n"),
        Prose("# Building\n\nA paragraph.\n> a quote right under it\n"),
        Prose("# Building\n\nA paragraph.\n## A heading right under it\n"),
        Prose("# Building\n\nA paragraph.\n- an item right under it\n"),
        Prose("# Building\n\nA paragraph.\n| a | b |\n"),
        Prose("# Building\n\n| a | b |\nA line right under a table row.\n"),
        Prose("# Building\n\n- an item\n> a quote right under it\n"),
        Prose("# Building\n\nA paragraph.\n#\tA heading\n"),
        Prose("# Building\n\nA paragraph.\n#\n"),
    ],
    ids=[
        "blank line",
        "sixth-level heading",
        "numbered items",
        "two-digit numbered item",
        "starred items",
        "break",
        "nested",
        "item under a quote",
        "heading under a quote",
        "table row under a quote",
        "break under a quote",
        "quote under a paragraph",
        "heading under a paragraph",
        "item under a paragraph",
        "table row under a paragraph",
        "line under a table row",
        "quote under an item",
        "heading opened by a tab under a paragraph",
        "empty heading under a paragraph",
    ],
)
def test_a_line_that_opens_a_block_is_not_a_wrap(tmp_path: Path, text: Prose) -> None:
    """A blank line ends a block, and a heading, item, table row or break starts one: none wraps."""
    assert _run(_repo(tmp_path, text)) == list[Prose]()


def test_wrapped_lines_inside_a_fence_are_code(tmp_path: Path) -> None:
    """Fenced code wraps freely; only prose is held to one line."""
    text = Prose("# Building\n\n~~~\nline one\nline two\n  indented\n~~~\n")
    assert _run(_repo(tmp_path, text)) == list[Prose]()


def test_a_missing_guide_is_a_finding(tmp_path: Path) -> None:
    """A scan whose subject is not among the documents vouches for nothing."""
    assert _run(_repo(tmp_path, None)) == [Prose(f"{SUBJECT}: not among the tracked documents")]


@pytest.mark.parametrize(
    "text",
    [Prose("```\nonly code\n```\n"), Prose("```\nonly code\n```\n\n")],
    ids=["fence alone", "fence and a blank line"],
)
def test_a_guide_without_prose_is_a_finding(tmp_path: Path, text: Prose) -> None:
    """A subject with only blank lines outside fenced code gives the scan nothing to check."""
    assert _run(_repo(tmp_path, text)) == [
        Prose(f"{SUBJECT}: no paragraph outside fenced code to check")
    ]


def test_every_wrap_is_named_in_line_order(tmp_path: Path) -> None:
    """Two wraps in one paragraph are two findings, the earlier line first."""
    text = Prose("# Building\n\nA paragraph\nwrapped once\nwrapped twice\n")
    assert _run(_repo(tmp_path, text)) == [
        Prose("docs/development/BUILDING.md: line 4 wraps the paragraph above it"),
        Prose("docs/development/BUILDING.md: line 5 wraps the paragraph above it"),
    ]


def test_a_line_opening_on_a_number_with_no_marker_wraps(tmp_path: Path) -> None:
    """A number is a list marker only with a dot and a space after it; otherwise it is prose."""
    text = Prose("# Building\n\nThe ratio of a circle is near\n3.14 for every radius.\n")
    assert _run(_repo(tmp_path, text)) == [
        Prose("docs/development/BUILDING.md: line 4 wraps the paragraph above it")
    ]


@pytest.mark.parametrize(
    "line",
    [
        Prose("#5 bolt continues it"),
        Prose("####### seven marks continue it"),
        Prose("#\u00a0a no-break space continues it"),
    ],
    ids=["digit after the run", "run of seven", "no-break space after the run"],
)
def test_a_hash_run_that_opens_no_heading_is_prose(tmp_path: Path, line: Prose) -> None:
    """A run of over six ``#``, or one before anything but a space, tab or line end, is prose."""
    text = Prose(f"# Building\n\nA paragraph\n{line}\n")
    assert _run(_repo(tmp_path, text)) == [
        Prose("docs/development/BUILDING.md: line 4 wraps the paragraph above it")
    ]


def test_a_lone_carriage_return_ends_a_line(tmp_path: Path) -> None:
    """A guide whose lines end in a carriage return alone has its wraps found by line."""
    text = Prose("# Building\r\rA paragraph\rwrapped onto a second line\r")
    assert findings(tmp_path, [SUBJECT, RelPath("README.md")], {SUBJECT: text}) == [
        Prose("docs/development/BUILDING.md: line 4 wraps the paragraph above it")
    ]

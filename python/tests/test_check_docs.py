# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_docs`` — the documentation-accuracy gate.

Covers the two subtle parsers the gate depends on:

* ``slug`` — GitHub-flavored anchor slugs WITHOUT whitespace-run collapse, so
  ``## Change Detection & Stability`` → ``change-detection--stability`` (the
  double-hyphen case a naive slugger gets wrong).
* ``_links`` — link extraction that skips BOTH fenced code blocks and inline
  code spans, so neither a ``[](const T& e)`` lambda in a fence nor prose
  describing link syntax as ``[text](target)`` in backticks is mistaken for a
  real link.  Plus the baseline: a genuine ``[x](y)`` link IS extracted (its
  existence/anchor resolution is the caller's job).
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools.check_docs import header_slugs, links, slug

if TYPE_CHECKING:
    from pathlib import Path


def test_slug_no_whitespace_collapse() -> None:
    """Each whitespace char becomes one hyphen — runs are NOT collapsed."""
    assert slug("Change Detection & Stability") == "change-detection--stability"
    assert slug("Path 1 (Excel + CLI)") == "path-1-excel--cli"


def test_links_skip_fences_and_inline_code(tmp_path: Path) -> None:
    """A fenced lambda and an inline `[t](u)` code span are not extracted as links."""
    good = tmp_path / "good.md"
    content = (
        "# Title\n## Change Detection & Stability\n"
        + "[ok](#change-detection--stability)\n"
        + "```\n[not a link](const T& e)\n```\n"
        + "Prose describing link syntax as `[text](target)` is not a link.\n"
    )
    good.write_text(content, encoding="utf-8")
    assert "change-detection--stability" in header_slugs(good)
    # The only extracted link is the real anchor — the fenced lambda and the
    # inline `[text](target)` code span are both masked.
    assert links(good) == ["#change-detection--stability"]


def test_real_links_are_extracted(tmp_path: Path) -> None:
    """Genuine links are extracted; existence/anchor checks happen caller-side."""
    bad = tmp_path / "bad.md"
    bad.write_text("[x](nope.md)\n[y](#missing)\n", encoding="utf-8")
    assert links(bad) == ["nope.md", "#missing"]

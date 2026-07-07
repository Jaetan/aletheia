# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools.check_docs`` — the documentation-accuracy gate.

Covers the parsers/predicates the gate depends on:

* ``slug`` — GitHub-flavored anchor slugs WITHOUT whitespace-run collapse, so
  ``## Change Detection & Stability`` → ``change-detection--stability`` (the
  double-hyphen case a naive slugger gets wrong).
* ``prose_lines`` / ``links`` — prose extraction that skips BOTH fenced code
  blocks and inline code spans, so neither a ``[](const T& e)`` lambda in a
  fence nor prose describing link syntax as ``[text](target)`` in backticks is
  mistaken for a real link OR a live internal label. Plus the baseline: a
  genuine ``[x](y)`` link IS extracted (existence/anchor resolution is the
  caller's job).
* ``escapes_repo`` — a relative link resolving outside the repo is a defect
  (not a valid in-checkout link) even if the path exists on the CI runner.
"""

from __future__ import annotations

from pathlib import Path

from tools.check_docs import REPO, escapes_repo, header_slugs, links, prose_lines, slug


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


def test_prose_lines_mask_code_examples() -> None:
    """Internal labels / memory links shown as code examples are stripped from prose.

    ``_label_findings`` runs on ``prose_lines`` output, so a mark shown as a
    fenced or inline-code EXAMPLE must not reach it — otherwise a doc explaining
    the convention would trip its own gate (the false positive Copilot flagged).
    A genuine mark written in prose still survives (and is flagged downstream).
    """
    doc = (
        "# Conventions\n"
        "Review marks like `AGDA-C-6.2` are stripped from living docs.\n"  # inline code
        "```\n(PR C) example line\n```\n"  # fenced block
        "The pointer `[x](memory/foo.md)` is illustrative.\n"  # inline memory link
        "A real (PR C) mark and a real [x](memory/foo.md) survive.\n"  # prose — kept
    )
    prose = "\n".join(prose_lines(doc))
    assert "AGDA-C-6.2" not in prose  # inline-code mark masked
    assert prose.count("(PR C)") == 1  # fenced example dropped; prose mark kept
    assert prose.count("memory/foo.md") == 1  # inline-code link masked; prose link kept


def test_escapes_repo_flags_out_of_tree_targets() -> None:
    """A target resolving outside the repo is a defect; an in-repo one is fine."""
    assert escapes_repo(Path("/etc/passwd"))
    assert not escapes_repo(REPO / "README.md")
    assert not escapes_repo(REPO / "docs" / "INDEX.md")

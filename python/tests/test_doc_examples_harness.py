# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cat 32 gate: the doc-example harness runs every Python fence the docs carry.

``pytest --markdown-docs`` runs each Python fence of the documents
``DOC_EXAMPLE_DOCS`` names (``tools/_ci_steps.py``) against the real FFI, with
the repo-root ``conftest.py`` supplying the globals.  The CI step, the command
AGENTS/python.md prints and these tests read that one list, and these tests
hold it to the tree: every tracked Markdown file with a Python fence is on it,
CHANGELOG.md aside, and every document on it is tracked, carries a Python fence
and has every one of them run.

A fence that is not runnable is tagged ``text``: the plugin skips a
``python notest`` fence while a reader still sees Python.  Whether a fence runs
is the plugin's own call, ``extract_fence_tests`` over the parser it collects
with, so a fence it skips for any reason fails here.
"""

from __future__ import annotations

from pathlib import Path
from typing import NewType

import pytest
from pytest_markdown_docs.plugin import extract_fence_tests, pytest_markdown_docs_markdown_it

from tools._ci_steps import DOC_EXAMPLE_DOCS
from tools._common import git_ls_files

REPO_ROOT = Path(__file__).resolve().parents[2]

# The line a fence opens on, as the plugin numbers it.
FenceLine = NewType("FenceLine", int)

# The fence languages the plugin runs as Python, and the suffixes it reads as Markdown.
_PYTHON_LANGUAGES = frozenset({"py", "python", "python3"})
_MARKDOWN_PATHSPECS = ("*.md", "*.mdx", "*.svx")
# Its fences describe past releases.
_CHANGELOG = Path("CHANGELOG.md")


def _python_fences(doc: Path) -> set[FenceLine]:
    """Return the opening line of every fence in ``doc`` a reader takes for Python."""
    tokens = pytest_markdown_docs_markdown_it().parse((REPO_ROOT / doc).read_text(encoding="utf-8"))
    return {
        FenceLine(token.map[0] + 1)
        for token in tokens
        if token.type == "fence"
        and token.map
        and (token.info.split() or [""])[0] in _PYTHON_LANGUAGES
    }


def _run_fences(doc: Path) -> set[FenceLine]:
    """Return the opening line of every fence in ``doc`` the harness runs."""
    return {
        FenceLine(fence.start_line)
        for fence in extract_fence_tests(
            pytest_markdown_docs_markdown_it(),
            (REPO_ROOT / doc).read_text(encoding="utf-8"),
            start_line_offset=0,
            source_path=REPO_ROOT / doc,
            markdown_type=doc.suffix.removeprefix("."),
        )
    }


def test_every_tracked_python_fence_is_in_a_harness_document() -> None:
    """Every tracked Markdown file with a Python fence is listed, CHANGELOG.md aside."""
    listed = set(DOC_EXAMPLE_DOCS)
    assert len(listed) == len(DOC_EXAMPLE_DOCS), "a document is listed twice"
    unlisted = [
        doc
        for doc in map(Path, git_ls_files(REPO_ROOT, *_MARKDOWN_PATHSPECS))
        if doc != _CHANGELOG and doc not in listed and _python_fences(doc)
    ]
    assert not unlisted, f"Python fences the harness does not run: {unlisted}"


@pytest.mark.parametrize("doc", DOC_EXAMPLE_DOCS, ids=str)
def test_the_harness_runs_every_python_fence_of_the_document(doc: Path) -> None:
    """``doc`` is tracked and carries a Python fence, and the harness skips none of them."""
    assert git_ls_files(REPO_ROOT, str(doc)) == [str(doc)], f"{doc} is listed and not tracked"
    fences = _python_fences(doc)
    assert fences, f"{doc} carries no Python fence, so the harness runs nothing in it"
    skipped = sorted(fences - _run_fences(doc))
    assert not skipped, (
        f"{doc}: the harness skips the Python fences opening on lines {skipped}; "
        "tag a fence that is not runnable ``text``"
    )

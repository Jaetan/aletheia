# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cat 32 gate: the doc-example harness runs every Python fence the docs carry.

``pytest --markdown-docs`` runs each Python fence of the documents
``DOC_EXAMPLE_DOCS`` names (``tools/_ci_steps.py``) against the real FFI, with
the repo-root ``conftest.py`` supplying the globals.  The CI step, the command
AGENTS/python.md prints and these tests read that one list, and these tests
hold it to the tree: every tracked Markdown file with a Python fence is on it,
and every document on it is tracked, carries a Python fence and has every one
of them run.

A fence that is not runnable opens with tildes, which the harness's parser
(``tools.check_fence_marks.harness_markdown_it``) reads as code rather than as a
fence, so it is neither run nor counted here.  The plugin skips a ``python
notest`` fence, and does not see one whose language word carries a suffix
(``python,notest``), while a reader still sees Python in both.  Whether a fence
runs is the plugin's own call, ``extract_fence_tests`` over the parser the
harness collects with, so a fence it skips for any reason fails here.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import NewType

import pytest
from pytest_markdown_docs.plugin import extract_fence_tests

from tools._ci_steps import DOC_EXAMPLE_DOCS
from tools._common import git_ls_files
from tools.check_fence_marks import harness_markdown_it

REPO_ROOT = Path(__file__).resolve().parents[2]

# The line a fence opens on, as the plugin numbers it.
FenceLine = NewType("FenceLine", int)
# A Markdown document's text, and a fence's info string within it.
MarkdownText = NewType("MarkdownText", str)
FenceInfo = NewType("FenceInfo", str)

# The fence languages the plugin runs as Python, and the suffixes it reads as Markdown.
_PYTHON_LANGUAGES = frozenset({"py", "python", "python3"})
# A language word a reader takes for Python and the plugin does not: one of those
# followed by ASCII punctuation, as in ``python,notest``.
_SUFFIXED_PYTHON = re.compile(r"(?:py|python|python3)[!-/:-@\[-^`{-~]")
_MARKDOWN_PATHSPECS = ("*.md", "*.mdx", "*.svx")
# The floor under the number of Python fences the listed documents carry
# together, so a mass rename cannot silently empty the harness.
_MIN_FENCES = 11


def _is_python(info: FenceInfo) -> bool:
    """Whether a reader takes a fence with this info string for Python."""
    word = (info.split() or [""])[0]
    return word in _PYTHON_LANGUAGES or _SUFFIXED_PYTHON.match(word) is not None


def _python_fence_lines(markdown: MarkdownText) -> set[FenceLine]:
    """Return the opening line of every fence of ``markdown`` a reader takes for Python."""
    return {
        FenceLine(token.map[0] + 1)
        for token in harness_markdown_it().parse(markdown)
        if token.type == "fence" and token.map and _is_python(FenceInfo(token.info))
    }


def _run_fence_lines(markdown: MarkdownText, doc: Path) -> set[FenceLine]:
    """Return the opening line of every fence of ``markdown`` the harness runs."""
    return {
        FenceLine(fence.start_line)
        for fence in extract_fence_tests(
            harness_markdown_it(),
            markdown,
            start_line_offset=0,
            source_path=REPO_ROOT / doc,
            markdown_type=doc.suffix.removeprefix("."),
        )
    }


def _python_fences(doc: Path) -> set[FenceLine]:
    """Return the opening line of every fence in ``doc`` a reader takes for Python."""
    return _python_fence_lines(MarkdownText((REPO_ROOT / doc).read_text(encoding="utf-8")))


def _run_fences(doc: Path) -> set[FenceLine]:
    """Return the opening line of every fence in ``doc`` the harness runs."""
    return _run_fence_lines(MarkdownText((REPO_ROOT / doc).read_text(encoding="utf-8")), doc)


def test_every_tracked_python_fence_is_in_a_harness_document() -> None:
    """Every tracked Markdown file with a Python fence is listed."""
    listed = set(DOC_EXAMPLE_DOCS)
    assert len(listed) == len(DOC_EXAMPLE_DOCS), "a document is listed twice"
    unlisted = [
        doc
        for doc in map(Path, git_ls_files(REPO_ROOT, *_MARKDOWN_PATHSPECS))
        if doc not in listed and _python_fences(doc)
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
        "open a fence that is not runnable with tildes"
    )


def test_a_fence_hidden_behind_a_suffix_is_seen_and_not_run() -> None:
    """A suffixed language word is Python to a reader and not to the plugin: the gate reports it."""
    markdown = MarkdownText(
        "```python,notest\nx = 1\n```\n\n```python\nx = 1\n```\n\n```pycon\n>>> 1\n```\n"
    )
    doc = Path("probe.md")
    assert _python_fence_lines(markdown) == {FenceLine(1), FenceLine(5)}
    assert _python_fence_lines(markdown) - _run_fence_lines(markdown, doc) == {FenceLine(1)}


def test_a_tilde_fence_is_neither_run_nor_counted() -> None:
    """A tilde fence is code no check runs: neither run by the harness nor counted by the gate."""
    markdown = MarkdownText("~~~python\nraise SystemExit(1)\n~~~\n\n```python\nx = 1\n```\n")
    doc = Path("probe.md")
    assert _python_fence_lines(markdown) == {FenceLine(5)}
    assert _run_fence_lines(markdown, doc) == {FenceLine(5)}


def test_the_listed_documents_keep_a_floor_of_python_fences() -> None:
    """The listed documents together carry at least the floor's Python fences."""
    total = sum(len(_run_fences(doc)) for doc in DOC_EXAMPLE_DOCS)
    assert total >= _MIN_FENCES, f"expected at least {_MIN_FENCES} Python fences, saw {total}"

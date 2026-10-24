# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Cat 32 gate: the doc-example harness runs every Python fence the docs carry.

``pytest --markdown-docs`` runs each Python fence of the documents
``DOC_EXAMPLE_DOCS`` names (``tools/_ci_steps.py``) against the real FFI, with
the repo-root ``conftest.py`` supplying the globals.  The CI step, the command
AGENTS/python.md prints and these tests read that one list, and these tests
hold it to the tree: every tracked Markdown file with a Python fence is on it,
and every document on it is tracked, carries a Python fence and has every one
of them run. The step reads the docstrings of the package ``DOC_EXAMPLE_PACKAGE``
names too, from each module's source, and every Python fence of a module's
docstrings is run. A fence that defines a function names it, so no example is
a definition nothing runs.

A fence that is not runnable opens with tildes, which the harness's parser
(``tools.check_fence_marks.harness_markdown_it``) reads as code rather than as a
fence, so it is neither run nor counted here.  The plugin skips a ``python
notest`` fence, and does not see one whose language word carries a suffix
(``python,notest``), while a reader still sees Python in both.  Whether a fence
runs is the plugin's own call, ``extract_fence_tests`` over the parser the
harness collects with, so a fence it skips for any reason fails here.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path
from typing import NewType

import pytest
from pytest_markdown_docs.plugin import extract_fence_tests

from tools._ci_steps import DOC_EXAMPLE_DOCS, DOC_EXAMPLE_PACKAGE
from tools._common import RelPath, git_ls_files
from tools._hosted_markdown import SourceText, docstrings
from tools.check_fence_marks import harness_markdown_it

REPO_ROOT = Path(__file__).resolve().parents[2]

# The line a fence opens on, as the plugin numbers it.
FenceLine = NewType("FenceLine", int)
# A Markdown document's text, and a fence's info string within it.
MarkdownText = NewType("MarkdownText", str)
FenceInfo = NewType("FenceInfo", str)
# A function a fence defines, by its name, and a fence's source as the plugin runs it.
FunctionName = NewType("FunctionName", str)
FenceSource = NewType("FenceSource", str)

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


@pytest.mark.process(
    "git's own index decides which Markdown files are tracked, so only git lists the"
    + " documents whose Python fences must be on the harness list"
)
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


@pytest.fixture(scope="module", name="tracked")
def _tracked() -> frozenset[RelPath]:
    """Return the tracked files the listed documents name, from one listing of them all."""
    return frozenset(git_ls_files(REPO_ROOT, *map(str, DOC_EXAMPLE_DOCS)))


@pytest.mark.process("git's own index decides whether a document on the harness list is tracked")
@pytest.mark.parametrize("doc", DOC_EXAMPLE_DOCS, ids=str)
def test_the_harness_runs_every_python_fence_of_the_document(
    doc: Path, tracked: frozenset[RelPath]
) -> None:
    """``doc`` is tracked and carries a Python fence, and the harness skips none of them."""
    assert str(doc) in tracked, f"{doc} is listed and not tracked"
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


def _docstring_fence_lines(module: Path) -> tuple[set[FenceLine], set[FenceLine]]:
    """Return the file lines of the docstring fences a reader takes for Python, and of those run."""
    source = SourceText((REPO_ROOT / module).read_text(encoding="utf-8"))
    read: set[FenceLine] = set()
    run: set[FenceLine] = set()
    for hosted in docstrings(source):
        read |= {
            FenceLine(hosted.start + token.map[0])
            for token in harness_markdown_it().parse(hosted.text)
            if token.type == "fence" and token.map and _is_python(FenceInfo(token.info))
        }
        run |= {
            FenceLine(fence.start_line)
            for fence in extract_fence_tests(
                harness_markdown_it(), hosted.text, hosted.start - 1, source_path=REPO_ROOT / module
            )
        }
    return read, run


@pytest.fixture(scope="module", name="package_modules")
def _package_modules() -> list[Path]:
    """Return the tracked modules of the package whose docstrings the harness runs."""
    return [Path(rel) for rel in git_ls_files(REPO_ROOT, f"{DOC_EXAMPLE_PACKAGE}/*.py")]


@pytest.mark.process("git's own index decides which modules of the package are tracked")
def test_the_harness_runs_every_python_fence_of_the_package_docstrings(
    package_modules: list[Path],
) -> None:
    """Every Python fence of a package module's docstrings is one the harness runs."""
    assert package_modules, f"{DOC_EXAMPLE_PACKAGE} holds no tracked module"
    skipped = {
        str(module): sorted(read - run)
        for module in package_modules
        for read, run in [_docstring_fence_lines(module)]
        if read - run
    }
    assert not skipped, f"the harness skips these docstring fences, by file line: {skipped}"


def test_a_docstring_fence_is_read_on_its_file_line() -> None:
    """A docstring's fence is numbered by the line of the file it opens on."""
    source = SourceText(
        'def f() -> None:\n    """Summary.\n\n    ```python\n    x = 1\n    ```\n    """\n'
        + 'class C:\n    """\n    ```python\n    y = 2\n    ```\n    """\n'
    )
    hosted = docstrings(source)
    assert [(text.owner, text.start) for text in hosted] == [("f", 2), ("C", 10)]
    lines = [
        fence.start_line
        for text in hosted
        for fence in extract_fence_tests(
            harness_markdown_it(), text.text, text.start - 1, source_path=Path("m.py")
        )
    ]
    assert lines == [4, 10]


def _uncalled(source: FenceSource) -> list[FunctionName]:
    """Return the functions a fence defines at its top level and names nowhere in it."""
    tree = ast.parse(source)
    named = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
    return [
        FunctionName(node.name)
        for node in tree.body
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef) and node.name not in named
    ]


@pytest.mark.process("git's own index decides which modules of the package are tracked")
def test_every_function_a_fence_defines_is_called(package_modules: list[Path]) -> None:
    """A fence that defines a function names it, so the example runs what it shows."""
    fences = [
        fence
        for doc in DOC_EXAMPLE_DOCS
        for fence in extract_fence_tests(
            harness_markdown_it(),
            (REPO_ROOT / doc).read_text(encoding="utf-8"),
            start_line_offset=0,
            source_path=REPO_ROOT / doc,
            markdown_type=doc.suffix.removeprefix("."),
        )
    ] + [
        fence
        for module in package_modules
        for hosted in docstrings(SourceText((REPO_ROOT / module).read_text(encoding="utf-8")))
        for fence in extract_fence_tests(
            harness_markdown_it(), hosted.text, hosted.start - 1, source_path=REPO_ROOT / module
        )
    ]
    uncalled = {
        f"{fence.source_path.relative_to(REPO_ROOT)}:{fence.start_line}": names
        for fence in fences
        if (names := _uncalled(FenceSource(fence.source)))
    }
    assert not uncalled, f"fences defining a function nothing in them runs: {uncalled}"


def test_a_defined_function_named_nowhere_is_found() -> None:
    """A definition the fence never names is reported; one it calls or passes is not."""
    assert _uncalled(FenceSource("async def watch():\n    pass\n")) == ["watch"]
    assert _uncalled(FenceSource("def f():\n    pass\n\nf()\n")) == []
    assert _uncalled(FenceSource("def f():\n    pass\n\nrun(f)\n")) == []

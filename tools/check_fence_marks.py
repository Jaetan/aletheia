# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Fence-mark gate: a fence opened with backticks is one a doc-example harness runs.

The documentation marks every fenced block by the way it opens. A fence opened
with three backticks is an example a harness compiles and runs: the first word
of its info string is a language one of the four harnesses reads (``py``,
``python`` or ``python3``; ``go``; ``cpp``; ``rust``), and each binding's own
gates hold every tracked document carrying one to that harness's list. Every
other fenced block, a shell session, a JSON message, a signature sketch, an
example written for a past release, opens with tildes, which no harness reads.
A reader tells checked code from unchecked code by the fence alone.

The Go, C++ and Rust extractors take only a fence opened with three backticks.
The Python harness collects through ``harness_markdown_it``, the parser this
module builds, which reads a tilde fence as a code block, so no harness runs a
tilde fence either.

The gate reads every tracked Markdown file as CommonMark (``tools._markdown``),
whose parser the harness's is built on, and refuses a fence opened with
backticks whose run is not exactly three or whose first info word is not one of
those languages: a suffixed word (``go,ignore``), an alias (``golang``) or
another language (``bash``) is refused alike.

Source files hold Markdown too, read by ``tools._hosted_markdown`` as the
harness of each host reads it, and the rule holds there with each host's own
language: a C++ file's ``//`` comments take ``cpp``, which the C++ harness runs
in the headers it lists; the doc comments of a Rust library crate's sources take
``rust`` alone, the info string rustdoc runs as it stands, so an attribute
(``no_run``, ``ignore``) or no language is refused, and so is a tilde fence
rustdoc would still compile (no language, rust, or an attribute); the docstrings
of the Python package take ``python``, ``py`` or ``python3``. A Rust doc comment
elsewhere, a module compiled only under ``cfg(test)`` among them, and a
docstring outside the package are read by no harness, so every backtick fence
there is refused. In those comments and docstrings an example is a fence: an
indented code block, and an ``Example:``, ``Examples:`` or ``Usage:`` section
whose lines run on indented below it, are refused, and in the package's
docstrings so are a doctest prompt and any other section whose indented lines
parse as Python that calls, binds or opens something, the Google prose sections
(``Args:``, ``Returns:`` and the rest) apart.

Run ``python -m tools.check_fence_marks`` from the repository root. Exit 0 =
clean, 1 = a backtick fence no harness runs, 2 = could-not-check (a tracked
file was unreadable, never reported as clean). Its rule is unit-tested by
``python/tests/test_check_fence_marks.py``.
"""

from __future__ import annotations

import argparse
import ast
import re
import sys
import textwrap
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath, git_ls_files, report_tree_scan, scan_tracked_tree
from tools._hosted_markdown import (
    HostedText,
    Owner,
    SourceText,
    UnnumberableDocstringError,
    cpp_comment_texts,
    docstrings,
    rust_doc_texts,
)
from tools._markdown import blocks, commonmark, fences

from aletheia.common_types import ExitStatus, PositiveInt, Prose

if TYPE_CHECKING:
    from markdown_it import MarkdownIt
    from markdown_it.rules_core import StateCore

REPO_ROOT = Path(__file__).resolve().parent.parent
DESCRIPTION = "Refuse a backtick fence no doc-example harness runs; unrun code opens with tildes."

# A Markdown document's text, and the index of a line within a text.
MarkdownText = NewType("MarkdownText", str)
LineIndex = NewType("LineIndex", int)

# The first info word of a fence's info string, the language a harness reads it as.
FenceLanguage = NewType("FenceLanguage", str)

# The first info words the four harnesses run.
RUN_LANGUAGES = frozenset(map(FenceLanguage, ("py", "python", "python3", "go", "cpp", "rust")))
# The one opening the Go, C++ and Rust extractors take.
RUN_FENCE = "```"
_MARKDOWN_SUFFIXES = (".md", ".mdx", ".svx")
_CPP_SUFFIXES = (".cpp", ".hpp", ".h")
# The sources rustdoc runs the doc comments of: the library crates'.
_RUST_LIBRARY_ROOTS = ("rust/src/", "rust/excel/src/")
# The package whose docstrings the Python harness runs (DOC_EXAMPLE_PACKAGE in tools/_ci_steps.py).
PYTHON_PACKAGE = "python/aletheia/"
_PYTHON_LANGUAGES = frozenset(map(FenceLanguage, ("py", "python", "python3")))
_CPP_LANGUAGES = frozenset({FenceLanguage("cpp")})
_RUST_LANGUAGES = frozenset({FenceLanguage("rust")})
_NO_LANGUAGE = frozenset[FenceLanguage]()
# The nodes that make an indented block code rather than prose.
_CODE_NODES = (
    ast.Call,
    ast.Assign,
    ast.AnnAssign,
    ast.AugAssign,
    ast.NamedExpr,
    ast.Await,
    ast.With,
    ast.AsyncWith,
    ast.Import,
    ast.ImportFrom,
)
# A section header whose indented block is an example, and the Google-style
# sections whose indented blocks are prose.
_EXAMPLE_SECTIONS = frozenset({"Example", "Examples", "Usage"})
_PROSE_SECTIONS = frozenset(
    {
        "Args",
        "Arguments",
        "Attributes",
        "Fields",
        "Keyword Args",
        "Keyword Arguments",
        "Methods",
        "Note",
        "Notes",
        "Other Parameters",
        "Parameters",
        "Raises",
        "References",
        "Return",
        "Returns",
        "See Also",
        "Todo",
        "Warning",
        "Warnings",
        "Warns",
        "Yield",
        "Yields",
    }
)
# What rustdoc reads in a fence's info string to skip, compile or expect a panic rather than run.
_RUSTDOC_ATTRIBUTE = re.compile(r"ignore|no_run|compile_fail|should_panic|test_harness|edition\d+")
# A module a Rust file declares compiled only under ``cfg(test)``, which rustdoc never documents.
_TEST_MODULE = re.compile(
    r"#\[cfg\(test\)\]\s*(?:#\[[^\]]*\]\s*)*(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*;"
)


def _tilde_fences_are_code_blocks(state: StateCore) -> None:
    """Retype every tilde fence as a code block, which no harness collects."""
    for token in state.tokens:
        if token.type == "fence" and token.markup.startswith("~"):
            token.type = "code_block"


def harness_markdown_it() -> MarkdownIt:
    """Return the reader's parser as the Python harness collects with it: no tilde fence."""
    parser = commonmark()
    parser.core.ruler.after("block", "tilde_fences_are_code_blocks", _tilde_fences_are_code_blocks)
    return parser


def _finding(rel: RelPath, line: PositiveInt, what: Prose) -> Prose:
    """Return a finding named by its file and line."""
    return Prose(f"{rel}:{line}: {what}")


def _refused(
    rel: RelPath, hosted: HostedText, languages: frozenset[FenceLanguage], *, rustdoc: bool = False
) -> list[Prose]:
    """Return one finding per fence of ``hosted`` whose opening its host's harness does not run.

    Under ``rustdoc`` a backtick fence runs when its info string is ``rust`` alone,
    and a tilde fence is refused when rustdoc would still compile it: no language,
    or rust, or one of its attributes.
    """
    findings: list[Prose] = []
    for fence in fences(hosted.text):
        words = fence.info.split()
        word = FenceLanguage(words[0] if words else "")
        line = hosted.lines[fence.line - 1]
        if fence.markup.startswith("`"):
            if (
                fence.markup == RUN_FENCE
                and word in languages
                and (not rustdoc or words == ["rust"])
            ):
                continue
            what = (
                f"a fence opened with {fence.markup} and {fence.info.strip()!r} is one rustdoc"
                + " does not run as it stands; write ```rust, or open it with tildes and a language"
                if rustdoc
                else f"a fence opened with {fence.markup} and {word or 'no info word'!r} is one no"
                + " harness runs; open it with tildes"
            )
            findings.append(_finding(rel, line, Prose(what)))
        elif rustdoc and (
            not words or words[0].split(",")[0] == "rust" or _RUSTDOC_ATTRIBUTE.match(word)
        ):
            findings.append(
                _finding(
                    rel,
                    line,
                    Prose(
                        "rustdoc compiles a tilde fence of "
                        + f"{fence.info.strip() or 'no language'!r};"
                        + " give it a language other than rust"
                    ),
                )
            )
    return findings


def scan_text(rel: RelPath, text: MarkdownText) -> list[Prose]:
    """Return one finding per backtick fence of ``text`` that no harness runs."""
    count = text.count("\n") + 1
    lines: tuple[PositiveInt, ...] = tuple(range(1, count + 1))
    return _refused(rel, HostedText(Owner("<document>"), lines, Prose(text)), RUN_LANGUAGES)


def _is_code(block: list[Prose]) -> bool:
    """Whether an indented block parses as Python that does something: a call, a binding, a with."""
    try:
        tree = compile(
            textwrap.dedent("\n".join(block)),
            "<docstring>",
            "exec",
            ast.PyCF_ONLY_AST | ast.PyCF_ALLOW_TOP_LEVEL_AWAIT,
        )
    except SyntaxError:
        return False
    return any(isinstance(node, _CODE_NODES) for node in ast.walk(tree))


def _example_section(name: Prose, body: list[Prose], *, docstring: bool) -> bool:
    """Whether a section of that name holding that body is an example.

    It is one by its name, and in a docstring also when its body parses as code and
    the name is no Google prose section's.
    """
    return name in _EXAMPLE_SECTIONS or (
        docstring and name not in _PROSE_SECTIONS and _is_code(body)
    )


def _unfenced(rel: RelPath, hosted: HostedText, *, docstring: bool) -> list[Prose]:
    """Return one finding per block of ``hosted`` that holds an example outside a fence.

    An indented code block is one in any host, and so is an example section whose
    lines run on indented below its header. In a docstring, a section whose
    indented lines parse as code is one unless it is a Google prose section, and so
    is any doctest prompt.
    """
    lines = [Prose(line) for line in hosted.text.split("\n")]
    findings: list[Prose] = []
    for block in blocks(hosted.text):
        at = hosted.lines[block.first - 1]
        if block.kind == "code":
            what = (
                "an indented code block is no fence: write it as a fence a harness runs,"
                + " or a tilde one"
            )
            findings.append(_finding(rel, at, Prose(what)))
            continue
        if block.kind != "paragraph":
            continue
        text = lines[block.first - 1 : block.last]
        header = text[0].strip()
        depth = len(text[0]) - len(text[0].lstrip())
        below = [line for line in text[1:] if line.strip()]
        indented = bool(below) and all(len(line) - len(line.lstrip()) > depth for line in below)
        name = Prose(header.removesuffix(":").split(" (")[0])
        if docstring and any(line.lstrip().startswith(">>>") for line in text):
            findings.append(
                _finding(rel, at, Prose("a doctest prompt runs nowhere; write a ```python fence"))
            )
        elif (
            header.endswith(":")
            and indented
            and _example_section(name, text[1:], docstring=docstring)
        ):
            what = (
                "an example written as an indented block runs nowhere; write it as a"
                + " fence a harness runs, or open unrun code with tildes"
            )
            findings.append(_finding(rel, at, Prose(what)))
    return findings


def _test_modules(sources: dict[RelPath, SourceText]) -> frozenset[RelPath]:
    """Return the Rust library files a ``#[cfg(test)]`` module declaration owns, nested ones too."""
    owned: set[RelPath] = set()
    for rel, text in sources.items():
        if not rel.startswith(_RUST_LIBRARY_ROOTS):
            continue
        path = PurePosixPath(rel)
        here = path.parent if path.name in {"lib.rs", "mod.rs"} else path.parent / path.stem
        for name in _TEST_MODULE.findall(text):
            owned.update(
                other
                for other in sources
                if other in {f"{here / name}.rs", f"{here / name}/mod.rs"}
                or other.startswith(f"{here / name}/")
            )
    return frozenset(owned)


def scan_file(
    rel: RelPath, text: SourceText, test_modules: frozenset[RelPath] = frozenset()
) -> list[Prose]:
    """Return every finding of the tracked file ``rel``, read as the host its suffix names."""
    if rel.endswith(_MARKDOWN_SUFFIXES):
        return scan_text(rel, MarkdownText(text))
    if rel.endswith(_CPP_SUFFIXES):
        return [
            finding
            for hosted in cpp_comment_texts(text)
            for finding in (
                *_refused(rel, hosted, _CPP_LANGUAGES),
                *_unfenced(rel, hosted, docstring=False),
            )
        ]
    if rel.endswith(".rs"):
        library = rel.startswith(_RUST_LIBRARY_ROOTS) and rel not in test_modules
        return [
            finding
            for hosted in rust_doc_texts(text)
            for finding in (
                (
                    *_refused(rel, hosted, _RUST_LANGUAGES, rustdoc=True),
                    *_unfenced(rel, hosted, docstring=False),
                )
                if library
                else _refused(rel, hosted, _NO_LANGUAGE)
            )
        ]
    try:
        hosted_texts = docstrings(text)
    except UnnumberableDocstringError as error:
        return [Prose(f"{rel}: {error}; write it as a raw docstring or with its newlines literal")]
    in_package = rel.startswith(PYTHON_PACKAGE)
    python = _PYTHON_LANGUAGES if in_package else _NO_LANGUAGE
    return [
        finding
        for hosted in hosted_texts
        for finding in (
            *_refused(rel, hosted, python),
            *(_unfenced(rel, hosted, docstring=True) if in_package else ()),
        )
    ]


def _is_not_read(rel: RelPath) -> bool:
    """Whether the tracked file ``rel`` is one the gate does not read."""
    return not rel.endswith((*_MARKDOWN_SUFFIXES, *_CPP_SUFFIXES, ".rs", ".py"))


def main() -> ExitStatus:
    """Report every backtick fence no harness runs; 2 if a file was unreadable, 1 if any found."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    rust = {
        RelPath(rel): SourceText((REPO_ROOT / rel).read_text(encoding="utf-8"))
        for rel in git_ls_files(REPO_ROOT, *(f"{root}*.rs" for root in _RUST_LIBRARY_ROOTS))
    }
    test_modules = _test_modules(rust)
    scan = scan_tracked_tree(
        REPO_ROOT,
        lambda rel: _is_not_read(RelPath(rel)),
        lambda rel, text: list(scan_file(RelPath(rel), SourceText(text), test_modules)),
    )
    return ExitStatus(
        report_tree_scan(
            "check_fence_marks",
            scan,
            found=f"{len(scan.findings)} backtick fence(s) no harness runs:",
            found_lines=scan.findings,
            clean="every backtick fence of the tracked Markdown and sources is one a harness runs.",
        )
    )


if __name__ == "__main__":
    sys.exit(main())

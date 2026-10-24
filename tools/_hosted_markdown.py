# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Markdown a source file holds in its comments or docstrings, read without running the file.

Three hosts carry it, each read as the harness that runs its fences reads it. A
C++ file's ``//`` comments are one text per run of consecutive comment lines,
each line read past its leading blanks, its slashes and one blank, as the C++
doc-example harness reads a header. A Rust file's doc comments are read as
rustdoc reads them: the outer (``///``) and the inner (``//!``) lines of a run
are two texts, an attribute or a blank line between doc lines of one kind does
not end the run, and the indentation every non-blank line shares is removed. A
Python file's docstrings, of the module, its classes and its functions, nested
ones included, are read with :mod:`ast` and cleaned as :func:`inspect.getdoc`
cleans them, so the file is never imported. Each text carries the file line of
each of its lines.
"""

from __future__ import annotations

import ast
import re
from typing import NamedTuple, NewType

from aletheia.common_types import PositiveInt, Prose

# A source file's text.
SourceText = NewType("SourceText", str)
# What holds a hosted text: a docstring's dotted owner, the module's own being
# ``<module>``, or the marker a comment run's lines open with.
Owner = NewType("Owner", str)

# A docstring's value as the source writes it, before cleaning, and a count of lines.
RawDocstring = NewType("RawDocstring", str)
LineCount = NewType("LineCount", int)

# A line that sits between the doc comment lines of one Rust item without ending them.
_RUST_BETWEEN = re.compile(r"^\s*(?:#!?\[.*\]\s*)?$")


class HostedText(NamedTuple):
    """A Markdown text a source file holds, with the file line each of its lines stands on."""

    owner: Owner
    lines: tuple[PositiveInt, ...]
    text: Prose

    @property
    def start(self) -> PositiveInt:
        """The file line the text's first line stands on."""
        return self.lines[0]


class UnnumberableDocstringError(ValueError):
    """A docstring whose escapes change its line count, so its lines map to none of the file's."""


def cpp_comment_texts(source: SourceText) -> list[HostedText]:
    """Return each run of ``//`` comment lines, each read past its slashes and one blank."""
    runs: list[HostedText] = []
    numbers: list[PositiveInt] = []
    lines: list[Prose] = []
    for number, line in enumerate([*source.split("\n"), ""], start=1):
        stripped = line.lstrip(" \t")
        if not stripped.startswith("//"):
            if lines:
                runs.append(HostedText(Owner("//"), tuple(numbers), Prose("\n".join(lines) + "\n")))
                numbers, lines = [], []
            continue
        text = stripped.lstrip("/")
        numbers.append(number)
        lines.append(Prose(text.removeprefix(" ")))
    return runs


def _unindented(lines: list[Prose]) -> list[Prose]:
    """Return ``lines`` with the indentation every non-blank one shares removed, as rustdoc does."""
    depth = min((len(line) - len(line.lstrip()) for line in lines if line.strip()), default=0)
    return [Prose(line[depth:]) for line in lines]


def rust_doc_texts(source: SourceText) -> list[HostedText]:
    """Return a Rust file's doc comment texts, outer and inner apart, as rustdoc groups them."""
    runs: list[HostedText] = []
    kind = ""
    numbers: list[PositiveInt] = []
    lines: list[Prose] = []

    def close() -> None:
        if lines:
            runs.append(
                HostedText(Owner(kind), tuple(numbers), Prose("\n".join(_unindented(lines)) + "\n"))
            )
            numbers.clear()
            lines.clear()

    for number, line in enumerate([*source.split("\n"), ""], start=1):
        stripped = line.lstrip(" \t")
        marker = next((m for m in ("//!", "///") if stripped.startswith(m)), "")
        if marker == "///" and stripped.startswith("////"):
            marker = ""
        if not marker:
            if not (lines and _RUST_BETWEEN.match(line)):
                close()
            continue
        if marker != kind:
            close()
            kind = marker
        numbers.append(number)
        lines.append(Prose(stripped.removeprefix(marker)))
    close()
    return runs


def _dropped_leading_lines(raw: RawDocstring) -> LineCount:
    """Return how many leading lines :func:`inspect.cleandoc` drops from ``raw``."""
    lines = raw.expandtabs().split("\n")
    margins = [len(line) - len(line.lstrip()) for line in lines[1:] if line.lstrip()]
    margin = min(margins, default=0)
    cleaned = [lines[0].lstrip(), *(line[margin:] for line in lines[1:])]
    return LineCount(next((i for i, line in enumerate(cleaned) if line), len(cleaned)))


def docstrings(source: SourceText) -> list[HostedText]:
    """Return the docstrings of a Python module, its classes and its functions, in source order.

    Raises:
        UnnumberableDocstringError: a docstring's value has another line count than its source.

    """
    found: list[HostedText] = []

    def visit(node: ast.AST, owner: Owner) -> None:
        if isinstance(node, ast.Module | ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef):
            text = ast.get_docstring(node)
            first = node.body[0] if node.body else None
            if (
                text is not None
                and isinstance(first, ast.Expr)
                and isinstance(first.value, ast.Constant)
            ):
                value = str(first.value.value)
                if (
                    first.end_lineno is not None
                    and value.count("\n") != first.end_lineno - first.lineno
                ):
                    msg = f"line {first.lineno}: the docstring's escapes change its line count"
                    raise UnnumberableDocstringError(msg)
                begin = first.lineno + _dropped_leading_lines(RawDocstring(value))
                count = text.count("\n") + 1
                lines: tuple[PositiveInt, ...] = tuple(range(begin, begin + count))
                found.append(HostedText(owner, lines, Prose(text)))
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef):
                visit(child, Owner(child.name if owner == "<module>" else f"{owner}.{child.name}"))
            else:
                visit(child, owner)

    visit(ast.parse(source), Owner("<module>"))
    return found

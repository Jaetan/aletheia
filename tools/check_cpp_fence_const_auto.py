# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the C++ examples the documentation carries to ``auto const``.

The C++ sources are formatted with ``QualifierAlignment: Right``
(``cpp/.clang-format``), so the clang-format step holds every qualifier after
what it qualifies: a const-qualified ``auto`` is written ``auto const``, never
``const auto``.  clang-format reads no Markdown and formats no comment, so the
C++ examples the documentation carries are held here: a fence whose info
string's first word is ``cpp``, in a tracked Markdown file or in the ``//``
comments of a C++ source, the fences the C++ doc-example harness compiles.  A
line of such a fence that writes ``const auto`` is refused.

Run ``python -m tools.check_cpp_fence_const_auto`` from the repository root.
Exit 0 = clean, 1 = a refused spelling, 2 = could-not-check (a tracked file
was unreadable, never reported as clean).  Unit-tested by
``python/tests/test_check_cpp_fence_const_auto.py``.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import NewType

from tools._common import RelPath, report_tree_scan
from tools._hosted_markdown import SourceText, cpp_comment_texts, scan_tracked_sources
from tools._markdown import commonmark

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent

# A 1-based line of a tracked file or of a comment's text.
LineNumber = NewType("LineNumber", int)

_MARKDOWN_SUFFIXES = (".md", ".mdx", ".svx")
_CPP_SUFFIXES = (".cpp", ".hpp", ".h")

# The spelling refused: `const` before `auto`, whatever space stands between.
_WEST_CONST_AUTO = re.compile(r"\bconst\s+auto\b")


def cpp_fence_lines(text: Prose) -> list[tuple[LineNumber, Prose]]:
    """Return each line of each ``cpp`` fence of ``text``, with its 1-based line in ``text``."""
    found: list[tuple[LineNumber, Prose]] = []
    for token in commonmark().parse(text):
        if token.type != "fence" or token.map is None:
            continue
        if (token.info.split() or [""])[0] != "cpp":
            continue
        # token.map[0] is the opening fence's 0-based line; its body starts on the next.
        body_start = token.map[0] + 2
        found.extend(
            (LineNumber(body_start + offset), Prose(line))
            for offset, line in enumerate(token.content.split("\n"))
        )
    return found


def _findings(rel: RelPath, lines: list[tuple[LineNumber, Prose]]) -> list[Prose]:
    """Return one finding per line of ``lines`` that writes ``const auto``."""
    return [
        Prose(f"{rel}:{number}: `const auto` where the sources write `auto const`: {line.strip()}")
        for number, line in lines
        if _WEST_CONST_AUTO.search(line)
    ]


def scan_file(rel: RelPath, text: SourceText) -> list[Prose]:
    """Return every finding of the tracked file ``rel``, read as the host its suffix names."""
    if rel.endswith(_MARKDOWN_SUFFIXES):
        return _findings(rel, cpp_fence_lines(Prose(text)))
    return _findings(
        rel,
        [
            (LineNumber(hosted.lines[number - 1]), line)
            for hosted in cpp_comment_texts(text)
            for number, line in cpp_fence_lines(hosted.text)
            if number <= len(hosted.lines)
        ],
    )


def _is_not_read(rel: RelPath) -> bool:
    """Whether the tracked file ``rel`` is one the gate does not read."""
    return not rel.endswith((*_MARKDOWN_SUFFIXES, *_CPP_SUFFIXES))


def main() -> ExitStatus:
    """Report every C++ example line that writes ``const auto``; 2 if a file was unreadable."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    scan = scan_tracked_sources(REPO_ROOT, _is_not_read, scan_file)
    return ExitStatus(
        report_tree_scan(
            "check_cpp_fence_const_auto",
            scan,
            found=f"{len(scan.findings)} C++ example line(s) writing `const auto`:",
            found_lines=scan.findings,
            clean="every C++ example of the tracked Markdown and sources writes `auto const`.",
        )
    )


if __name__ == "__main__":
    sys.exit(main())

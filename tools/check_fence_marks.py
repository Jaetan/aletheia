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

The gate reads every tracked Markdown file with a CommonMark parser and refuses
a fence opened with backticks whose run is not exactly three or whose first
info word is not one of those languages: a suffixed word (``go,ignore``), an
alias (``golang``) or another language (``bash``) is refused alike.

Run ``python -m tools.check_fence_marks`` from the repository root. Exit 0 =
clean, 1 = a backtick fence no harness runs, 2 = could-not-check (a tracked
file was unreadable, never reported as clean). Its rule is unit-tested by
``python/tests/test_check_fence_marks.py``.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType

from markdown_it import MarkdownIt

from tools._common import RelPath, report_tree_scan, scan_tracked_tree

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from markdown_it.rules_core import StateCore

REPO_ROOT = Path(__file__).resolve().parent.parent
DESCRIPTION = "Refuse a backtick fence no doc-example harness runs; unrun code opens with tildes."

# A Markdown document's text.
MarkdownText = NewType("MarkdownText", str)

# The first info words the four harnesses run.
RUN_LANGUAGES = frozenset({"py", "python", "python3", "go", "cpp", "rust"})
# The one opening the Go, C++ and Rust extractors take.
RUN_FENCE = "```"
_MARKDOWN_SUFFIXES = (".md", ".mdx", ".svx")


def _tilde_fences_are_code_blocks(state: StateCore) -> None:
    """Retype every tilde fence as a code block, which no harness collects."""
    for token in state.tokens:
        if token.type == "fence" and token.markup.startswith("~"):
            token.type = "code_block"


def harness_markdown_it() -> MarkdownIt:
    """Return the CommonMark parser the Python harness collects with: a tilde fence is not one."""
    parser = MarkdownIt("commonmark")
    parser.core.ruler.after("block", "tilde_fences_are_code_blocks", _tilde_fences_are_code_blocks)
    return parser


def scan_text(rel: RelPath, text: MarkdownText) -> list[Prose]:
    """Return one finding per backtick fence of ``text`` that no harness runs."""
    findings: list[Prose] = []
    for token in MarkdownIt("commonmark").parse(text):
        if token.type != "fence" or not token.markup.startswith("`") or not token.map:
            continue
        word = (token.info.split() or [""])[0]
        if token.markup != RUN_FENCE or word not in RUN_LANGUAGES:
            findings.append(
                Prose(
                    f"{rel}:{token.map[0] + 1}: a fence opened with {token.markup} and "
                    + f"{word or 'no info word'!r} is one no harness runs; open it with tildes"
                )
            )
    return findings


def _is_not_markdown(rel: RelPath) -> bool:
    """Whether the tracked file ``rel`` is one the gate does not read."""
    return not rel.endswith(_MARKDOWN_SUFFIXES)


def main() -> ExitStatus:
    """Report every backtick fence no harness runs; 2 if a file was unreadable, 1 if any found."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    scan = scan_tracked_tree(
        REPO_ROOT,
        lambda rel: _is_not_markdown(RelPath(rel)),
        lambda rel, text: list(scan_text(RelPath(rel), MarkdownText(text))),
    )
    return ExitStatus(
        report_tree_scan(
            "check_fence_marks",
            scan,
            found=f"{len(scan.findings)} backtick fence(s) no harness runs:",
            found_lines=scan.findings,
            clean="every backtick fence of the tracked Markdown is one a harness runs.",
        )
    )


if __name__ == "__main__":
    sys.exit(main())

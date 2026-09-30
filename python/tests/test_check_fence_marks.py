# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The fence-mark gate: a backtick fence is one a harness runs, and unrun code opens with tildes."""

from __future__ import annotations

from typing import NewType

import pytest

from tools._common import RelPath
from tools.check_fence_marks import MarkdownText, harness_markdown_it, scan_text

# A line opening a fence: its run of backticks or tildes and its info string.
FenceOpening = NewType("FenceOpening", str)

_DOC = RelPath("docs/x.md")
_RUN = ("```python", "```py", "```python3", "```go", "```cpp", "```rust", "```python continuation")
_NOT_RUN = ("```bash", "```json", "```text", "```", "```golang", "```go,ignore", "```python,notest")
_TILDE = ("~~~bash", "~~~", "~~~go", "~~~python", "~~~~json")


@pytest.mark.parametrize("opening", [FenceOpening(line) for line in _RUN])
def test_a_backtick_fence_in_a_language_a_harness_runs_passes(opening: FenceOpening) -> None:
    """A language one of the four harnesses reads, opened with three backticks, passes."""
    assert not scan_text(_DOC, MarkdownText(f"{opening}\nx\n```\n"))


@pytest.mark.parametrize("opening", [FenceOpening(line) for line in (*_NOT_RUN, "````go")])
def test_a_backtick_fence_no_harness_runs_is_refused(opening: FenceOpening) -> None:
    """Another language, none, an alias, a suffix or a longer run: each is refused on its line."""
    closing = "`" * (len(opening) - len(opening.lstrip("`")))
    findings = scan_text(_DOC, MarkdownText(f"# Title\n\n{opening}\nx\n{closing}\n"))
    assert len(findings) == 1
    assert findings[0].startswith("docs/x.md:3: ")


@pytest.mark.parametrize("opening", [FenceOpening(line) for line in _TILDE])
def test_a_tilde_fence_passes_whatever_its_language(opening: FenceOpening) -> None:
    """A tilde fence is code no check runs, in any language."""
    closing = "~" * (len(opening) - len(opening.lstrip("~")))
    assert not scan_text(_DOC, MarkdownText(f"{opening}\nx\n{closing}\n"))


def test_inline_code_opens_no_fence() -> None:
    """Three backticks inside a paragraph are inline code, as CommonMark reads them."""
    assert not scan_text(_DOC, MarkdownText("Every ```python``` / ```go``` block runs.\n"))


def test_the_harness_parser_reads_a_tilde_fence_as_code() -> None:
    """The Python harness collects fences through a parser that sees no tilde fence."""
    tokens = harness_markdown_it().parse("~~~python\nx = 1\n~~~\n\n```python\nx = 1\n```\n")
    assert [(t.type, t.markup) for t in tokens if t.type in {"fence", "code_block"}] == [
        ("code_block", "~~~"),
        ("fence", "```"),
    ]

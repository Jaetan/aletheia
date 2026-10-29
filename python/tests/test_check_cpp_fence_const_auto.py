# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The C++ example gate: a ``cpp`` fence in a document or a C++ comment writes ``auto const``."""

from __future__ import annotations

from tools._common import RelPath
from tools._hosted_markdown import SourceText
from tools.check_cpp_fence_const_auto import scan_file

_DOC = RelPath("docs/x.md")
_HEADER = RelPath("cpp/include/aletheia/x.hpp")


def test_a_cpp_fence_writing_const_auto_is_refused_on_its_line() -> None:
    """The finding names the document line the spelling stands on."""
    text = SourceText("# Title\n\n```cpp\nint main() {\n    const auto x = 1;\n}\n```\n")
    findings = scan_file(_DOC, text)
    assert len(findings) == 1, findings
    assert findings[0].startswith("docs/x.md:5: "), findings


def test_a_cpp_fence_writing_auto_const_passes() -> None:
    """The east-const spelling, and `auto const&`, are what the sources write."""
    text = SourceText("```cpp\nauto const x = 1;\nauto const& y = x;\n```\n")
    assert not scan_file(_DOC, text)


def test_another_language_and_prose_are_not_read() -> None:
    """Only a fence whose first info word is `cpp` is C++; prose mentions are not declarations."""
    text = SourceText(
        "Prose may say const auto.\n\n```python\nconst auto = 1\n```\n\n~~~\nconst auto x;\n~~~\n"
    )
    assert not scan_file(_DOC, text)


def test_a_fence_in_a_cpp_comment_is_refused_on_its_file_line() -> None:
    """A C++ source's `//` comments hold Markdown; its fence's line maps back to the file."""
    text = SourceText(
        "#pragma once\n"
        + "// Example:\n"
        + "//\n"
        + "// ```cpp\n"
        + "// const auto client = make();\n"
        + "// ```\n"
        + "int f();\n"
    )
    findings = scan_file(_HEADER, text)
    assert len(findings) == 1, findings
    assert findings[0].startswith("cpp/include/aletheia/x.hpp:5: "), findings


def test_code_outside_a_comment_is_left_to_clang_format() -> None:
    """A source's own code is the clang-format step's, not this gate's."""
    assert not scan_file(_HEADER, SourceText("const auto x = 1;\n"))

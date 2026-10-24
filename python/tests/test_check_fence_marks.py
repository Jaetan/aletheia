# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The fence-mark gate: a backtick fence is one a harness runs, and unrun code opens with tildes."""

from __future__ import annotations

from typing import TYPE_CHECKING, NewType

import pytest

from tools._common import RelPath
from tools._hosted_markdown import SourceText, docstrings
from tools.check_fence_marks import (
    FenceLanguage,
    MarkdownText,
    harness_markdown_it,
    scan_file,
    scan_text,
)

if TYPE_CHECKING:
    from aletheia.common_types import PositiveInt, Prose

# A line opening a fence: its run of backticks or tildes and its info string.
FenceOpening = NewType("FenceOpening", str)
# A source text whose fence language is left to fill in, a docstring line opening
# a block, and a whole source file's text.
SourceTemplate = NewType("SourceTemplate", str)
BlockOpener = NewType("BlockOpener", str)

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


def test_a_refused_fence_is_named_by_its_line_run_and_word() -> None:
    """The finding names the line, the opening run and the first info word."""
    assert scan_text(_DOC, MarkdownText("# T\n\n```bash\nx\n```\n")) == [
        "docs/x.md:3: a fence opened with ``` and 'bash' is one no harness runs; "
        + "open it with tildes"
    ]


# The C++, Rust and Python hosts, each with the backtick fence its harness runs there.
_HOSTS = (
    (
        RelPath("cpp/include/aletheia/x.hpp"),
        SourceTemplate("// x\n//\n// ```{word}\n// y\n// ```\n"),
        FenceLanguage("cpp"),
    ),
    (
        RelPath("cpp/include/aletheia/y.hpp"),
        SourceTemplate("/// x\n///\n/// ```{word}\n/// y\n/// ```\n"),
        FenceLanguage("cpp"),
    ),
    (
        RelPath("rust/src/x.rs"),
        SourceTemplate("//! x\n//!\n//! ```{word}\n//! y\n//! ```\n"),
        FenceLanguage("rust"),
    ),
    (
        RelPath("python/aletheia/x.py"),
        SourceTemplate('"""x\n\n```{word}\ny\n```\n"""\n'),
        FenceLanguage("python"),
    ),
)
_PY = RelPath("python/aletheia/x.py")
_RS = RelPath("rust/src/x.rs")
_INDENTED = "an indented code block is no fence: write it as a fence a harness runs, or a tilde one"
_EXAMPLE = (
    "an example written as an indented block runs nowhere; write it as a fence a harness"
    + " runs, or open unrun code with tildes"
)


@pytest.mark.parametrize(("rel", "template", "word"), _HOSTS, ids=str)
def test_a_source_fence_runs_in_its_host_language_alone(
    rel: RelPath, template: SourceTemplate, word: FenceLanguage
) -> None:
    """A source file's fence passes in the language its host's harness runs, and no other."""
    assert not scan_file(rel, SourceText(template.format(word=word)))
    findings = scan_file(rel, SourceText(template.format(word="go")))
    assert len(findings) == 1
    assert findings[0].startswith(f"{rel}:3: a fence opened with ``` and ")


@pytest.mark.parametrize(
    "opening",
    ["rust no_run", "rust,no_run", "rust ignore", "rust\tcompile_fail", "", "should_panic"],
)
def test_a_library_doc_fence_runs_as_rust_alone(opening: FenceOpening) -> None:
    """Rustdoc runs ```rust as it stands; an attribute, no language or another word is refused."""
    findings = scan_file(_RS, SourceText(f"/// ```{opening}\n/// x\n/// ```\nfn f() {{}}\n"))
    assert len(findings) == 1
    assert "is one rustdoc does not run as it stands" in findings[0]


@pytest.mark.parametrize("opening", ["~~~", "~~~rust", "~~~no_run"])
def test_a_library_tilde_fence_rustdoc_would_compile_is_refused(opening: FenceOpening) -> None:
    """Rustdoc compiles a code block of no language or of rust, so a tilde fence needs another."""
    assert scan_file(_RS, SourceText(f"/// {opening}\n/// x\n/// ~~~\nfn f() {{}}\n"))
    assert not scan_file(_RS, SourceText("/// ~~~text\n/// x\n/// ~~~\nfn f() {}\n"))


def test_rust_doc_lines_group_as_rustdoc_groups_them() -> None:
    """Inner and outer lines are two texts; an attribute between one item's lines is one text."""
    split = "//! ```rust\n//! x\n/// ```bash\n/// y\n/// ```\nfn f() {}\n"
    assert scan_file(_RS, SourceText(split)) == [
        f"{_RS}:3: a fence opened with ``` and 'bash' is one rustdoc does not run as it stands;"
        + " write ```rust, or open it with tildes and a language"
    ]
    joined = "/// ```rust\n/// let x = 1;\n#[inline]\n/// ```\nfn f() {}\n"
    assert not scan_file(_RS, SourceText(joined))


def test_rust_doc_lines_lose_the_indentation_they_share() -> None:
    """Rustdoc removes the indentation every line shares, so a deeply indented fence is a fence."""
    assert scan_file(_RS, SourceText("///     ```bash\n///     y\n///     ```\nfn f() {}\n"))


@pytest.mark.parametrize(
    "rel", [RelPath("rust/examples/x.rs"), RelPath("rust/tests/x.rs")], ids=str
)
def test_a_rust_doc_fence_outside_a_library_crate_is_refused(rel: RelPath) -> None:
    """Rustdoc runs the library crates' doc comments alone, so a rust fence elsewhere is refused."""
    assert scan_file(rel, SourceText("//! ```rust\n//! x\n//! ```\n"))
    assert not scan_file(rel, SourceText("//! ~~~sh\n//! x\n//! ~~~\n"))


def test_a_test_only_module_is_no_library_source() -> None:
    """A module compiled only under cfg(test) is never documented, so its rust fence is refused."""
    owned = frozenset({RelPath("rust/src/tests.rs")})
    fence = SourceText("//! ```rust\n//! x\n//! ```\n")
    assert scan_file(RelPath("rust/src/tests.rs"), fence, owned)
    assert not scan_file(RelPath("rust/src/lib.rs"), fence, owned)


def test_a_docstring_fence_outside_the_package_is_refused() -> None:
    """No harness reads a docstring outside the package, so its python fence is refused."""
    findings = scan_file(RelPath("tools/x.py"), SourceText('"""x\n\n```python\ny\n```\n"""\n'))
    assert findings == [
        "tools/x.py:3: a fence opened with ``` and 'python' is one no harness runs; "
        + "open it with tildes"
    ]


@pytest.mark.parametrize(
    ("docstring", "line", "what"),
    [
        ('"""Do.\n\nExample::\n\n    x = 1\n"""\n', 5, _INDENTED),
        ('"""Do.\n\nUse it so.\n\n::\n\n    aletheia validate\n"""\n', 7, _INDENTED),
        ('"""Do.\n\nUsage:\n    run(x)\n"""\n', 3, _EXAMPLE),
        ('"""Do.\n\nExamples:\n    x = 1\n"""\n', 3, _EXAMPLE),
        ('"""Do.\n\nUse it so:\n    client.start_stream()\n"""\n', 3, _EXAMPLE),
        ('"""Do.\n\nUse it so:\n    x: int = 3\n"""\n', 3, _EXAMPLE),
        ('"""Do.\n\nUse it so:\n    async with client:\n        pass\n"""\n', 3, _EXAMPLE),
        (
            '"""Do.\n\n>>> client.start_stream()\n"""\n',
            3,
            "a doctest prompt runs nowhere; write a ```python fence",
        ),
    ],
)
def test_an_example_outside_a_fence_is_refused(
    docstring: SourceText, line: PositiveInt, what: Prose
) -> None:
    """In the package's docstrings an example is a fence; one written otherwise is named."""
    assert scan_file(_PY, SourceText(docstring)) == [f"{_PY}:{line}: {what}"]
    assert not scan_file(RelPath("tools/x.py"), SourceText(docstring))


@pytest.mark.parametrize(
    "docstring",
    [
        '"""Do.\n\nArgs:\n    value: The value to send.\n    callback: Called per frame, as\n'
        + '        callback(frame)\n"""\n',
        '"""Do.\n\nReturns:\n    The response, or None.\n"""\n',
        '"""Do.\n\nNote:\n    foo(bar)\n"""\n',
        '"""Do.\n\nExample:\n```python\nif x:\n    client.start_stream()\n```\n"""\n',
        '"""Do.\n\nExample:\n\n  ```python\n  x = 1\n  ```\n"""\n',
    ],
    ids=["an Args section", "a Returns section", "a Note section", "a fence", "an indented fence"],
)
def test_a_prose_section_or_a_fenced_example_passes(docstring: SourceText) -> None:
    """Prose a Google section indents, and code a fence holds, are no unfenced example."""
    assert not scan_file(_PY, SourceText(docstring))


def test_an_indented_code_block_in_a_header_comment_is_refused() -> None:
    """A C++ comment's example is a fence too: an indented code block there is named."""
    source = SourceText("// Do.\n//\n//     auto x = f();\n")
    assert scan_file(RelPath("cpp/include/aletheia/x.hpp"), source) == [
        f"cpp/include/aletheia/x.hpp:3: {_INDENTED}"
    ]


@pytest.mark.parametrize(
    ("source", "starts"),
    [
        ('def f():\n    """\n        \n    Text\n    """\n', [3]),
        ('def f():\n    """\n\n    Text\n    """\n', [4]),
        ('def f():\n    """Text."""\n', [2]),
    ],
    ids=["a blank line wider than the margin stays", "a blank line goes", "one line"],
)
def test_a_docstring_is_numbered_from_the_line_cleandoc_keeps_first(
    source: SourceText, starts: list[PositiveInt]
) -> None:
    """A docstring's first text line stands where inspect.getdoc's first line comes from."""
    assert [hosted.start for hosted in docstrings(SourceText(source))] == starts


def test_a_docstring_whose_escapes_move_its_lines_is_named() -> None:
    """A docstring whose value has another line count than its source cannot be numbered."""
    findings = scan_file(_PY, SourceText('def f():\n    """Text with a \\n escape."""\n'))
    assert len(findings) == 1
    assert "the docstring's escapes change its line count" in findings[0]

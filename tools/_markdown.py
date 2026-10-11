# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The one reader of Markdown structure: CommonMark, read through markdown-it-py's tokens.

Every tool that asks what a document's blocks, headings, links, code spans, tables
or prose are asks here, so each reads a document as GitHub renders it: CommonMark
with GitHub's tables and strikethrough.  GitHub's bare-URL links and task lists are
not read, since no claim rests on them.  A text is parsed once and every answer
comes from that parse.  A line ends at LF, CRLF or a lone CR, as CommonMark ends
it, so a form feed or U+2028 is text within a line; lines count from one.

The parser departs from CommonMark in one way the reader keeps: markdown-it-py
trims every Unicode space (Python's ``str.strip``) around a heading's, a
paragraph's and a table cell's text and at the end of a reference definition,
where CommonMark trims spaces and tabs.  A line such a trim empties keeps its
number all the same, since the reader records the line each paragraph's text
starts on.

The reader serves the tree-wide prose gates as well as the documentation arms,
so it sits beside them rather than in ``tools.docs_arms``; ``tools._common``
imports nothing outside the standard library, so it cannot hold it.
"""

from __future__ import annotations

import functools
import re
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, Literal, NamedTuple, NewType, TypedDict, cast

from markdown_it import MarkdownIt
from markdown_it.rules_block import lheading, paragraph
from markdown_it.rules_inline import autolink, backtick, image, link

from tools._common import MARKDOWN_SUFFIXES, RelPath

from aletheia.common_types import PositiveInt, Prose

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator, Sequence
    from typing import Concatenate

    from markdown_it.rules_block import StateBlock
    from markdown_it.rules_core import StateCore
    from markdown_it.rules_inline import StateInline
    from markdown_it.token import Token
    from markdown_it.utils import EnvType

# A link's destination as CommonMark reads it, escapes and entities resolved, and an
# email autolink's address given CommonMark's ``mailto:``; nothing else changed: a
# path, an anchor or a URL, any text a document may write.
Destination = NewType("Destination", str)
# An offset into the text of one inline, the source of a paragraph, heading or cell.
Offset = NewType("Offset", int)

type BlockKind = Literal[
    "paragraph", "heading", "fence", "code", "html", "rule", "table", "quote", "list", "item"
]
type HeadingLevel = Literal[1, 2, 3, 4, 5, 6]
type LinkKind = Literal["link", "image", "autolink"]
# The tokens whose source span the parser records: code spans, links, autolinks and images.
type _Stamped = Literal["code_inline", "link_open", "image"]
type _InlineRule = Callable[[StateInline, bool], bool]

_NEWLINE = re.compile(r"\r\n?")
_TEXT = frozenset({"text", "text_special"})
_BREAKS = frozenset({"softbreak", "hardbreak"})
# The blocks whose lines hold inline text, so a line of theirs no text reaches is empty.
_INLINE_BLOCKS = frozenset({"paragraph_open", "heading_open", "tr_open"})


class _BlockToken(NamedTuple):
    """A token type that opens or is a block, and the kind of block it is."""

    token: Literal[
        "paragraph_open",
        "heading_open",
        "fence",
        "code_block",
        "html_block",
        "hr",
        "table_open",
        "blockquote_open",
        "bullet_list_open",
        "ordered_list_open",
        "list_item_open",
    ]
    kind: BlockKind


_BLOCK_TOKENS = (
    _BlockToken("paragraph_open", "paragraph"),
    _BlockToken("heading_open", "heading"),
    _BlockToken("fence", "fence"),
    _BlockToken("code_block", "code"),
    _BlockToken("html_block", "html"),
    _BlockToken("hr", "rule"),
    _BlockToken("table_open", "table"),
    _BlockToken("blockquote_open", "quote"),
    _BlockToken("bullet_list_open", "list"),
    _BlockToken("ordered_list_open", "list"),
    _BlockToken("list_item_open", "item"),
)


class _Level(NamedTuple):
    """A heading's tag and the level it carries."""

    tag: Literal["h1", "h2", "h3", "h4", "h5", "h6"]
    level: HeadingLevel


_LEVELS = (
    _Level("h1", 1),
    _Level("h2", 2),
    _Level("h3", 3),
    _Level("h4", 4),
    _Level("h5", 5),
    _Level("h6", 6),
)


class Block(NamedTuple):
    """A block of a document: its kind, its first and last lines, and the containers holding it.

    ``within`` names the quotes, lists and list items around it, outermost first.
    """

    kind: BlockKind
    first: PositiveInt
    last: PositiveInt
    within: tuple[BlockKind, ...]


class Heading(NamedTuple):
    """A heading: its line, its level, its text as written and as a reader sees it.

    ``source`` is the inline text between the opening and closing marks, code spans
    and escapes as written; ``text`` is what renders, code spans' content included.
    ``setext`` is whether a line of ``=`` or ``-`` under its text makes it a heading,
    rather than a run of ``#`` before it; ``opening_code`` is the content of the code
    span its text opens on, None when it opens on anything else; ``nested`` is whether
    a quote or a list holds it.
    """

    line: PositiveInt
    level: HeadingLevel
    source: Prose
    text: Prose
    setext: bool
    opening_code: Prose | None
    nested: bool


class Link(NamedTuple):
    """A link, an image or an autolink: its line, and the prose a reader meets in and after it.

    ``prose`` is its text, or an image's description, without code spans; ``after``
    is the text that follows it up to the next child that is neither text nor a
    line break.  ``written_here`` is
    whether the destination is written in the link itself, as an inline link,
    image or autolink writes it, rather than in a reference definition.
    """

    line: PositiveInt
    kind: LinkKind
    destination: Destination
    prose: Prose
    after: Prose
    written_here: bool


class Definition(NamedTuple):
    """A reference definition: its first line and its destination."""

    line: PositiveInt
    destination: Destination


class Fence(NamedTuple):
    """A fenced code block: its opening line, its run of backticks or tildes, its info.

    ``info`` is the rest of the opening line as written, which is what every
    doc-example harness reads.
    """

    line: PositiveInt
    markup: Prose
    info: Prose


class Row(NamedTuple):
    """A table row, a header row among them: its line and each cell's inline text.

    A cell is as written, but for an escaped pipe, which reads as a pipe.
    """

    line: PositiveInt
    cells: tuple[Prose, ...]


class Section(NamedTuple):
    """The lines a heading opens: from the line ``first`` after it up to the line ``end``.

    ``end`` is the next heading of the same level or shallower, or one past the
    document's last line.
    """

    heading: Heading
    first: PositiveInt
    end: PositiveInt


class _Reference(TypedDict):
    """A reference definition as the parser keeps it, by the keys read here."""

    href: Prose
    map: list[PositiveInt]


class _Parsed(NamedTuple):
    """One text, parsed: its lines, its tokens, its reference definitions."""

    lines: tuple[Prose, ...]
    tokens: tuple[Token, ...]
    definitions: tuple[Definition, ...]


class _Span(NamedTuple):
    """Where a recorded token sits in its inline's text: its start and end offsets."""

    start: Offset
    end: Offset


def _stamped(rule: _InlineRule, made: _Stamped) -> _InlineRule:
    """Wrap the inline ``rule`` so the ``made`` token it pushes records its source span."""

    def stamped(state: StateInline, silent: bool) -> bool:  # noqa: FBT001 -- markdown-it's signature
        start, pushed = Offset(state.pos), len(state.tokens)
        matched = rule(state, silent)
        made_here = next((token for token in state.tokens[pushed:] if token.type == made), None)
        if made_here is not None:
            made_here.meta["span"] = _Span(start, Offset(state.pos))
        return matched

    return stamped


def _records_first_line[**P](
    rule: Callable[Concatenate[StateBlock, P], bool],
) -> Callable[Concatenate[StateBlock, P], bool]:
    """Wrap the block ``rule`` so the inline it pushes records the line its text starts on.

    The parser trims the block's text with ``str.strip``, which drops a leading line
    of Unicode spaces whole, while the inline's map still opens on that line.
    """

    def recorded(state: StateBlock, *args: P.args, **kwargs: P.kwargs) -> bool:
        start, pushed = state.line, len(state.tokens)
        matched = rule(state, *args, **kwargs)
        inline = next((token for token in state.tokens[pushed:] if token.type == "inline"), None)
        if inline is not None:
            raw = state.getLines(start, state.line, state.blkIndent, keepLastLF=False)
            inline.meta["line"] = start + raw[: len(raw) - len(raw.lstrip())].count("\n") + 1
        return matched

    return recorded


def _inline_lines(state: StateCore) -> None:
    """Record on every inline no block rule recorded the line its text starts on: its first."""
    for token in state.tokens:
        if token.type == "inline" and token.map is not None:
            _ = token.meta.setdefault("line", token.map[0] + 1)


def commonmark() -> MarkdownIt:
    """Return a CommonMark parser with GitHub's tables and strikethrough, recording where text sits.

    Code spans, links, autolinks and images record their spans in their inline's text, and every
    inline the line its text starts on.  Every destination is kept as CommonMark reads
    it and is a link whatever its scheme: the parser's own normalisation
    percent-encodes a destination, punycodes a host and trims the Unicode spaces at
    its ends, and its validation refuses some schemes.
    """
    parser = MarkdownIt("commonmark").enable(["table", "strikethrough"])
    parser.normalizeLink = lambda url: url
    parser.validateLink = lambda url: url >= ""  # true of every destination
    parser.block.ruler.at("paragraph", _records_first_line(paragraph))
    parser.block.ruler.at("lheading", _records_first_line(lheading))
    parser.core.ruler.after("block", "inline_lines", _inline_lines)
    parser.inline.ruler.at("backticks", _stamped(backtick, "code_inline"))
    parser.inline.ruler.at("link", _stamped(link, "link_open"))
    parser.inline.ruler.at("image", _stamped(image, "image"))
    parser.inline.ruler.at("autolink", _stamped(autolink, "link_open"))
    return parser


_PARSER = commonmark()


@functools.cache
def _parse(text: Prose) -> _Parsed:
    """Parse ``text`` once; the readers below answer from the result and never change it."""
    env: EnvType = {}
    tokens = tuple(_PARSER.parse(text, env))
    normalized = _NEWLINE.sub("\n", text).replace("\0", "�")
    references = cast("dict[Prose, _Reference]", env.get("references", {}))
    return _Parsed(
        tuple(Prose(line) for line in normalized.split("\n")),
        tokens,
        tuple(
            Definition(found["map"][0] + 1, Destination(found["href"]))
            for found in references.values()
        ),
    )


def _span(token: Token) -> _Span:
    """Return where ``token``, a code span, link, autolink or image, sits in its inline's text."""
    return cast("_Span", token.meta["span"])


def _line(inline: Token) -> PositiveInt:
    """Return the line the text of ``inline`` starts on."""
    return cast("PositiveInt", inline.meta["line"])


def _code_spans_in(children: Sequence[Token], base: Offset) -> Iterator[_Span]:
    """Yield every code span among ``children`` and inside their images, offset by ``base``.

    An image's description is parsed on its own, its offsets counted from the
    character after the image's ``![``.
    """
    for child in children:
        if child.type == "code_inline":
            span = _span(child)
            yield _Span(Offset(base + span.start), Offset(base + span.end))
        elif child.type == "image":
            span = _span(child)
            yield from _code_spans_in(child.children or [], Offset(base + span.start + 2))


def _masked(inline: Token) -> Prose:
    """Return the text of ``inline`` with each code span dropped, keeping the line breaks in one."""
    text = inline.content
    out: list[Prose] = []
    at = 0
    for span in sorted(_code_spans_in(inline.children or [], Offset(0))):
        out.extend(
            (Prose(text[at : span.start]), Prose("\n" * text.count("\n", span.start, span.end)))
        )
        at = span.end
    out.append(Prose(text[at:]))
    return Prose("".join(out))


def _prose(children: Sequence[Token]) -> Prose:
    """Return the text a reader meets in ``children``: no code span, a break as a newline."""
    return Prose(
        "".join(
            child.content if child.type in _TEXT else "\n"
            for child in children
            if child.type in _TEXT | _BREAKS
        )
    )


def _rendered(children: Sequence[Token]) -> Prose:
    """Return the text ``children`` render, code spans' content included, a break as a newline."""
    shown = _TEXT | {"code_inline"}
    return Prose(
        "".join(
            child.content if child.type in shown else "\n"
            for child in children
            if child.type in shown | _BREAKS
        )
    )


def _level(token: Token) -> HeadingLevel:
    """Return the level of the heading ``token`` opens, from its ``h1`` to ``h6`` tag."""
    return next(pair.level for pair in _LEVELS if pair.tag == token.tag)


def _heading(line: PositiveInt, opening: Token, inline: Token) -> Heading:
    """Return the heading ``opening`` opens on ``line``, whose text is the ``inline`` after it."""
    children = inline.children or []
    first = children[0] if children else None
    return Heading(
        line,
        _level(opening),
        Prose(inline.content),
        _rendered(children),
        opening.markup in {"=", "-"},
        Prose(first.content) if first is not None and first.type == "code_inline" else None,
        opening.level > 0,
    )


def lines(text: Prose) -> tuple[Prose, ...]:
    """Return the lines of ``text`` as CommonMark ends them, one empty after a final newline."""
    return _parse(text).lines


def _kind(token: Token) -> BlockKind | None:
    """Return the kind of block ``token`` opens or is, or None for any other token."""
    return next((pair.kind for pair in _BLOCK_TOKENS if pair.token == token.type), None)


def blocks(text: Prose) -> list[Block]:
    """Return every block of ``text`` the parser makes a token for, in document order.

    A nested block comes after the one holding it.  A reference definition makes no
    token: ``definitions`` reads them.
    """
    out: list[Block] = []
    open_kinds: list[BlockKind | None] = []
    for token in _parse(text).tokens:
        kind = _kind(token)
        if kind is not None and token.map is not None:
            within = tuple(
                open_kind for open_kind in open_kinds if open_kind in {"quote", "list", "item"}
            )
            out.append(
                Block(kind, token.map[0] + 1, token.map[1], cast("tuple[BlockKind, ...]", within))
            )
        if token.nesting == 1:
            open_kinds.append(kind)
        elif token.nesting == -1:
            _ = open_kinds.pop()
    return out


def headings(text: Prose) -> list[Heading]:
    """Return every heading of ``text``, ATX and setext, in any container, in document order."""
    tokens = _parse(text).tokens
    return [
        _heading(token.map[0] + 1, token, tokens[i + 1])
        for i, token in enumerate(tokens)
        if token.type == "heading_open" and token.map is not None
    ]


def sections(text: Prose, heading: Prose) -> list[Section]:
    """Return every section of ``text`` the heading spelled ``heading`` opens, in order.

    ``heading`` is read as Markdown: ``## Results`` names each level-two heading whose
    text is written ``Results``, whether by a run of ``#``, with a closing run or not,
    or as a setext heading.  Only a heading outside every quote and list opens or ends
    a section.  A ``heading`` that is not one heading raises ValueError.
    """
    match headings(heading):
        case [wanted]:
            return _sections(_parse(text), wanted)
        case _:
            msg = f"{heading!r} is not one heading"
            raise ValueError(msg)


def section(text: Prose, heading: Prose) -> Section | None:
    """Return the first section of ``text`` the heading spelled ``heading`` opens, or None."""
    found = sections(text, heading)
    return found[0] if found else None


def _sections(parsed: _Parsed, wanted: Heading) -> list[Section]:
    """Return the sections the top-level headings of ``wanted``'s level and source open."""
    out: list[Section] = []
    opened: Section | None = None
    for i, token in enumerate(parsed.tokens):
        if token.type != "heading_open" or token.map is None or token.level:
            continue
        if opened is not None and _level(token) <= wanted.level:
            out.append(opened._replace(end=token.map[0] + 1))
            opened = None
        inline = parsed.tokens[i + 1]
        if _level(token) == wanted.level and inline.content == wanted.source:
            found = _heading(token.map[0] + 1, token, inline)
            opened = Section(found, token.map[1] + 1, len(parsed.lines) + 1)
    if opened is not None:
        out.append(opened)
    return out


def _links_in(inline: Token) -> Iterator[Link]:
    """Yield the links, images and autolinks of one inline."""
    children = inline.children or []
    for i, child in enumerate(children):
        if child.type == "link_open":
            close = next(
                (j for j in range(i + 1, len(children)) if children[j].type == "link_close"),
                len(children),
            )
            kind: LinkKind = "autolink" if child.markup == "autolink" else "link"
            written, prose, rest = (
                child.attrs.get("href", ""),
                _prose(children[i + 1 : close]),
                close + 1,
            )
        elif child.type == "image":
            kind = "image"
            written, prose, rest = child.attrs.get("src", ""), _prose(child.children or []), i + 1
        else:
            continue
        after = next(
            (j for j in range(rest, len(children)) if children[j].type not in _TEXT | _BREAKS),
            len(children),
        )
        span = _span(child)
        yield Link(
            _line(inline) + inline.content[: span.start].count("\n"),
            kind,
            Destination(str(written)),
            prose,
            _prose(children[rest:after]),
            inline.content[span.end - 1] in {")", ">"},
        )


def links(text: Prose) -> list[Link]:
    """Return every link, image and autolink of ``text``, in headings, paragraphs and cells."""
    return [
        found
        for token in _parse(text).tokens
        if token.type == "inline"
        for found in _links_in(token)
    ]


def definitions(text: Prose) -> list[Definition]:
    """Return each reference definition's destination, the first per label, in order."""
    return list(_parse(text).definitions)


def code_spans(text: Prose) -> list[Prose]:
    """Return the content of every code span of ``text``, as CommonMark normalises it, in order.

    An image's description renders as plain text, so a code span inside one is not
    read.
    """
    return [
        Prose(child.content)
        for token in _parse(text).tokens
        if token.type == "inline"
        for child in token.children or []
        if child.type == "code_inline"
    ]


def html(text: Prose) -> list[Prose]:
    """Return the raw HTML ``text`` carries, in order.

    Each HTML block is one entry, and so are the inline tags of each paragraph,
    heading or cell, joined in their order (empty for one holding none), so a tag
    inside an inline ``<script>`` reads as its text.
    """
    out: list[Prose] = []
    for token in _parse(text).tokens:
        if token.type == "html_block":
            out.append(Prose(token.content))
        elif token.type == "inline":
            tags = [child.content for child in token.children or [] if child.type == "html_inline"]
            out.append(Prose("".join(tags)))
    return out


def code_blocks(text: Prose) -> list[Prose]:
    """Return the content of every fenced and indented code block of ``text``, in order."""
    return [
        Prose(token.content)
        for token in _parse(text).tokens
        if token.type in {"fence", "code_block"}
    ]


def fences(text: Prose) -> list[Fence]:
    """Return every fenced code block of ``text``, in any container, in document order."""
    return [
        Fence(token.map[0] + 1, Prose(token.markup), Prose(token.info))
        for token in _parse(text).tokens
        if token.type == "fence" and token.map is not None
    ]


def table_rows(text: Prose) -> list[Row]:
    """Return every row of every table of ``text``, header rows among them, in order."""
    out: list[Row] = []
    tokens = iter(_parse(text).tokens)
    for token in tokens:
        if token.type == "tr_open" and token.map is not None:
            cells: list[Prose] = []
            for inner in tokens:  # the row's own tokens, up to its close
                if inner.type == "tr_close":
                    break
                if inner.type == "inline":
                    cells.append(Prose(inner.content))
            out.append(Row(token.map[0] + 1, tuple(cells)))
    return out


def prose_lines(rel: RelPath, text: Prose) -> list[tuple[PositiveInt, Prose]]:
    """Return each line of the file ``rel`` whose text is ``text`` that is prose, numbered from one.

    A file that is not Markdown is prose whole, since a comment in a source file is
    the project speaking; its lines end at a newline, never at a form feed or
    another separator ``str.splitlines`` honours.  In a Markdown file a fenced or
    indented code block's lines are dropped.  A line of a paragraph, heading or
    table row is its inline text with each code span dropped and the marks of the
    block (a list marker, a ``>``, a heading's ``#`` runs or setext underline, a
    table's pipes around its cells) left out, empty when it holds none of the text;
    a table row's cells are joined by ``" | "``.  Any other line, blank lines, HTML
    and reference definitions among them, is returned as written.
    """
    if PurePosixPath(rel).suffix not in MARKDOWN_SUFFIXES:
        numbered = [(number, Prose(line)) for number, line in enumerate(text.split("\n"), start=1)]
        if text.endswith("\n"):
            _ = numbered.pop()
        return numbered
    parsed = _parse(text)
    pieces: dict[PositiveInt, list[Prose]] = {}
    code: set[PositiveInt] = set()
    for token in parsed.tokens:
        if token.type in {"fence", "code_block"} and token.map is not None:
            code.update(range(token.map[0] + 1, token.map[1] + 1))
        elif token.type in _INLINE_BLOCKS and token.map is not None:
            for number in range(token.map[0] + 1, token.map[1] + 1):
                _ = pieces.setdefault(number, [])
        elif token.type == "inline":
            for k, piece in enumerate(str(_masked(token)).split("\n")):
                pieces[_line(token) + k].append(Prose(piece))
    numbered = list(enumerate(parsed.lines, start=1))
    if text.endswith(("\n", "\r")):
        _ = numbered.pop()
    return [
        (number, Prose(" | ".join(pieces[number])) if number in pieces else line)
        for number, line in numbered
        if number not in code
    ]

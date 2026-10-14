# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for ``tools._markdown``, the one reader of Markdown structure.

Each test holds one reading against CommonMark as markdown-it-py parses it,
with GitHub's tables: what a block, a heading, a link, a code span, a table row
or a line of prose is.  The documentation arms and the prose gates rest on
these readings; their own claims are tested beside them.
"""

from __future__ import annotations

import re

import pytest

from tools._common import RelPath
from tools._markdown import (
    Block,
    Definition,
    Destination,
    Fence,
    Heading,
    Link,
    Row,
    Section,
    blocks,
    code_blocks,
    code_spans,
    definitions,
    fences,
    headings,
    html,
    lines,
    links,
    prose_lines,
    section,
    sections,
    table_rows,
)

from aletheia.common_types import PositiveInt, Prose

_DOC = RelPath("a.md")


def _sources(text: Prose) -> list[Prose]:
    return [heading.source for heading in headings(text)]


def test_a_heading_shaped_line_in_a_fence_is_code_and_a_code_span_stays() -> None:
    """A heading-shaped line in a fence is code; a code span stays in the heading as written."""
    text = Prose("# One\n```\n# Not a heading\n```\n## Two `code` ##\n")
    assert headings(text) == [
        Heading(1, 1, Prose("One"), Prose("One"), setext=False, opening_code=None, nested=False),
        Heading(
            5,
            2,
            Prose("Two `code`"),
            Prose("Two code"),
            setext=False,
            opening_code=None,
            nested=False,
        ),
    ]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("#\tTitle\n"), [Prose("Title")]),
        (Prose("#\u00a0Title\n"), list[Prose]()),
        (Prose("#\n"), [Prose("")]),
        (Prose("####### Seven\n"), list[Prose]()),
    ],
    ids=["tab", "no-break-space", "run-alone", "seven"],
)
def test_a_run_of_one_to_six_opens_a_heading_before_a_space_a_tab_or_the_end(
    text: Prose, expected: list[Prose]
) -> None:
    """A run of one to six opens a heading before a space, a tab or the line's end."""
    assert _sources(text) == expected


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("##  \tTitle \t##  \n"), Prose("Title")),
        (Prose("## Title#\n"), Prose("Title#")),
        (Prose("## Title \\#\n"), Prose("Title \\#")),
        (Prose("## Title ## more\n"), Prose("Title ## more")),
        (Prose("   ## Title\n"), Prose("Title")),
        (Prose("> ## Title\n"), Prose("Title")),
        (Prose("- ## Title\n"), Prose("Title")),
    ],
    ids=[
        "spaces-tabs-and-closing-run",
        "closing-run-without-a-space",
        "escaped-closing-mark",
        "run-inside-the-text",
        "indented-three",
        "in-a-quote",
        "in-a-list-item",
    ],
)
def test_a_headings_text_is_what_commonmark_reads(text: Prose, expected: Prose) -> None:
    """A closing run needs a space before it; an indent under four, or a container, keeps one."""
    assert _sources(text) == [expected]


def test_four_spaces_of_indent_make_code_not_a_heading() -> None:
    """A heading-shaped line indented by four spaces is indented code."""
    assert headings(Prose("Text\n\n    ## Code\n")) == list[Heading]()


@pytest.mark.parametrize(
    "text",
    [Prose("# \u00a0Title\n"), Prose("# Title\u00a0\n")],
    ids=["leading", "trailing"],
)
def test_the_parser_trims_every_unicode_space_around_a_headings_text(text: Prose) -> None:
    """markdown-it-py trims a no-break space around the text, where CommonMark keeps it."""
    assert _sources(text) == [Prose("Title")]


def test_a_setext_heading_is_read_and_marked() -> None:
    """A paragraph over a line of = or - is a heading of level one or two, marked setext."""
    text = Prose("Top\n===\n\nNext\nline\n---\n")
    assert headings(text) == [
        Heading(1, 1, Prose("Top"), Prose("Top"), setext=True, opening_code=None, nested=False),
        Heading(
            4,
            2,
            Prose("Next\nline"),
            Prose("Next\nline"),
            setext=True,
            opening_code=None,
            nested=False,
        ),
    ]


def test_a_headings_rendered_text_resolves_escapes_entities_emphasis_and_links() -> None:
    """What renders: no backslash, an entity as its character, no markup, a link's text alone."""
    text = Prose("# a \\* &amp; *b* [c](d.md) `e`\n")
    assert [heading.text for heading in headings(text)] == [Prose("a * & b c e")]


def test_a_line_ends_at_a_newline_alone() -> None:
    """A form feed, a vertical tab, U+2028 and U+2029 are text; CRLF and a lone CR end a line."""
    text = Prose("a\x0cb\x0bc\u2028d\u2029e\r\nf\rg\n")
    assert lines(text) == (
        Prose("a\x0cb\x0bc\u2028d\u2029e"),
        Prose("f"),
        Prose("g"),
        Prose(""),
    )


def test_a_file_other_than_markdown_is_prose_whole_line_by_newline() -> None:
    """A source file's fences and code spans are its own text, and only a newline ends a line."""
    text = Prose("```\nx = `y`\x0cz\n```\n")
    assert prose_lines(RelPath("a.py"), text) == [(1, "```"), (2, "x = `y`\x0cz"), (3, "```")]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("~~~\n```\n~~~\nprose\n"), [(4, Prose("prose"))]),
        (Prose("````\n```\nstill code\n````\nprose\n"), [(5, Prose("prose"))]),
        (
            Prose("Text\n\n    ```\nprose\n"),
            [(1, Prose("Text")), (2, Prose("")), (4, Prose("prose"))],
        ),
        (Prose("  ```\ncode\n   ```\nprose\n"), [(4, Prose("prose"))]),
        (Prose("```\ncode\n\t```\nstill code\n"), list[tuple[PositiveInt, Prose]]()),
        (Prose("```\ncode never closed\n"), list[tuple[PositiveInt, Prose]]()),
        (Prose("- item\n  ```\n  code\n  ```\n"), [(1, Prose("item"))]),
    ],
    ids=[
        "backticks-in-a-tilde-fence",
        "longer-fence-closes-on-its-length",
        "four-spaces-are-code",
        "indented-three-close",
        "tab-indented-line-closes-nothing",
        "unclosed-runs-to-the-end",
        "fence-in-an-item",
    ],
)
def test_code_blocks_are_what_commonmark_reads_as_code(
    text: Prose, expected: list[tuple[PositiveInt, Prose]]
) -> None:
    """A fence closes on its own mark at its length or more; four spaces of indent are code."""
    assert prose_lines(_DOC, text) == expected


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("a `b` c\n"), Prose("a  c")),
        (Prose("a ``b`c`` d\n"), Prose("a  d")),
        (Prose("a `` ` `` b\n"), Prose("a  b")),
        (Prose("a `` b\n"), Prose("a `` b")),
        (Prose("a \\`b` c\n"), Prose("a \\`b` c")),
        (Prose("![a `b`](c.png) d\n"), Prose("![a ](c.png) d")),
        (Prose("[a](b.md`c`) d\n"), Prose("[a](b.md`c`) d")),
    ],
    ids=[
        "single",
        "double-holding-one",
        "spaced-backtick",
        "unmatched-run",
        "escaped-opener",
        "in-an-image-description",
        "backticks-in-a-destination",
    ],
)
def test_a_code_span_is_dropped_as_commonmark_finds_it(text: Prose, expected: Prose) -> None:
    """A span closes on a run of its own length; an escaped or unmatched run is text."""
    assert prose_lines(_DOC, text) == [(1, expected)]


def test_a_code_span_across_lines_keeps_the_lines_apart() -> None:
    """A span that runs onto the next line drops from both, each line keeping its number."""
    assert prose_lines(_DOC, Prose("a `b\nc` d\n")) == [(1, Prose("a ")), (2, Prose(" d"))]


def test_the_marks_opening_a_block_are_not_prose() -> None:
    """A list marker, a quote mark, a heading's run and a table's pipes are left out."""
    text = Prose("# Head\n\n- item\n\n> quote\n\n| a | `b` |\n|---|---|\n| c | d |\n")
    assert prose_lines(_DOC, text) == [
        (1, Prose("Head")),
        (2, Prose("")),
        (3, Prose("item")),
        (4, Prose("")),
        (5, Prose("quote")),
        (6, Prose("")),
        (7, Prose("a | ")),
        (8, Prose("|---|---|")),
        (9, Prose("c | d")),
    ]


def test_html_and_definitions_are_prose_as_written() -> None:
    """An HTML block and a reference definition are neither code nor inline text: kept whole."""
    text = Prose("<div>\n`x`\n</div>\n\n[a]: `b`\n")
    assert prose_lines(_DOC, text) == [
        (1, Prose("<div>")),
        (2, Prose("`x`")),
        (3, Prose("</div>")),
        (4, Prose("")),
        (5, Prose("[a]: `b`")),
    ]


@pytest.mark.parametrize("ending", [Prose("\r\n"), Prose("\r")], ids=["crlf", "cr"])
def test_a_closing_line_end_of_any_kind_adds_no_line(ending: Prose) -> None:
    """A text ending in CRLF or a lone CR has as many lines as one ending in LF."""
    assert prose_lines(_DOC, Prose(f"a{ending}b{ending}")) == [(1, Prose("a")), (2, Prose("b"))]


def test_links_are_read_with_their_line_kind_prose_and_what_follows() -> None:
    """Inline links, images and reference links, in headings, paragraphs and cells, in order."""
    text = Prose(
        '# [h](h.md)\n\nSee [the `x` guide](g.md "T") § 2,\nthen ![pic](p.png)\n'
        + "and [r][R] *x*.\n\n| [c](c.md) |\n|---|\n\n[R]: r.md\n"
    )
    assert links(text) == [
        Link(1, "link", Destination("h.md"), Prose("h"), Prose(""), written_here=True),
        Link(
            3,
            "link",
            Destination("g.md"),
            Prose("the  guide"),
            Prose(" § 2,\nthen "),
            written_here=True,
        ),
        Link(4, "image", Destination("p.png"), Prose("pic"), Prose("\nand "), written_here=True),
        Link(5, "link", Destination("r.md"), Prose("r"), Prose(" "), written_here=False),
        Link(7, "link", Destination("c.md"), Prose("c"), Prose(""), written_here=True),
    ]


def test_an_autolink_is_a_link_of_its_own_kind() -> None:
    """An autolink is written where it stands, its address as its destination, on its own line."""
    text = Prose("Text\nand <https://example.com>, <a@example.com>\n")
    assert links(text) == [
        Link(
            2,
            "autolink",
            Destination("https://example.com"),
            Prose("https://example.com"),
            Prose(", "),
            written_here=True,
        ),
        Link(
            2,
            "autolink",
            Destination("mailto:a@example.com"),
            Prose("a@example.com"),
            Prose(""),
            written_here=True,
        ),
    ]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("[a](x\\_y.md)"), Destination("x_y.md")),
        (Prose("[a](x&amp;y.md)"), Destination("x&y.md")),
        (Prose("[a](<x y.md>)"), Destination("x y.md")),
        (Prose("[a](javascript:x)"), Destination("javascript:x")),
        (Prose("[a](file:///x.md)"), Destination("file:///x.md")),
        (Prose("[a](data:text/html,x)"), Destination("data:text/html,x")),
        (Prose("[a](https://exämple.com/x)"), Destination("https://exämple.com/x")),
        (Prose("[a](x%20y.md)"), Destination("x%20y.md")),
        (Prose("[a](\u00a0x.md)"), Destination("\u00a0x.md")),
        (Prose("[a](x.md\u00a0)"), Destination("x.md\u00a0")),
        (Prose("[a](x.md`y`)"), Destination("x.md`y`")),
        (Prose("[a](100%.md)"), Destination("100%.md")),
    ],
    ids=[
        "escape",
        "entity",
        "pointy",
        "javascript",
        "file",
        "data",
        "unicode-host",
        "percent-as-written",
        "leading-nbsp",
        "trailing-nbsp",
        "backticks",
        "bare-percent",
    ],
)
def test_a_destination_is_what_its_spelling_names(text: Prose, expected: Destination) -> None:
    """Escapes and entities are resolved and nothing else: no scheme refused, nothing encoded."""
    assert [found.destination for found in links(text)] == [expected]


def test_definitions_are_read_where_commonmark_reads_them() -> None:
    """The first per label wins; a quote holds one; a paragraph's line or code holds none."""
    text = Prose(
        "[a]: one.md\n[a]: again.md\n\n> [b]:\n>   two.md\n\nText\n[c]: no.md\n\n    [d]: no.md\n"
    )
    assert definitions(text) == [
        Definition(1, Destination("one.md")),
        Definition(4, Destination("two.md")),
    ]


def test_code_spans_are_normalised_as_commonmark_does() -> None:
    """One space each side is dropped, a line end is a space, and an image description is text."""
    text = Prose("`a` `` b `` `c\nd` ![`e`](f.png)\n\n```\n`g`\n```\n")
    assert code_spans(text) == [Prose("a"), Prose("b"), Prose("c d")]


def test_html_comes_from_html_blocks_and_tags_alone() -> None:
    """A block whole, each inline's tags joined in order (empty for none), and nothing from code."""
    text = Prose(
        '# Head\n\n<div id="d">\nx\n</div>\n\nText <b id="y">z</b> `<i id="w">`\n\n'
        + '```\n<a id="v">\n```\n'
    )
    assert html(text) == [
        Prose(""),
        Prose('<div id="d">\nx\n</div>\n'),
        Prose('<b id="y"></b>'),
    ]


def test_fences_carry_their_line_mark_and_info() -> None:
    """Every fenced block, in any container, with its opening run and its info string."""
    text = Prose("```py x\na\n```\n\n- ~~~~\n  b\n  ~~~~\n")
    assert fences(text) == [
        Fence(1, Prose("```"), Prose("py x")),
        Fence(5, Prose("~~~~"), Prose("")),
    ]


def test_table_rows_are_cells_as_github_splits_them() -> None:
    """Header and body rows; an escaped pipe stays in its cell; a short row is padded."""
    text = Prose("| a | b |\n|---|---|\n| c \\| d | `e` |\n| f |\n\n| g |\n")
    assert table_rows(text) == [
        Row(1, (Prose("a"), Prose("b")), (Prose("a"), Prose("b")), header=True),
        Row(3, (Prose("c | d"), Prose("`e`")), (Prose("c | d"), Prose("e")), header=False),
        Row(4, (Prose("f"), Prose("")), (Prose("f"), Prose("")), header=False),
    ]


def test_a_cells_shown_text_is_what_it_renders() -> None:
    """Emphasis marks go, a code span keeps its content and an escaped mark reads as itself."""
    text = Prose("| **a** | `[b]` | *c* d | \\*e |\n|---|---|---|---|\n")
    assert [row.shown for row in table_rows(text)] == [
        (Prose("a"), Prose("[b]"), Prose("c d"), Prose("*e"))
    ]


def test_a_tables_first_row_alone_is_its_header() -> None:
    """Each table's header row is marked, its body rows not, in every table of the text."""
    text = Prose("| a |\n|---|\n| b |\n| c |\n\n| d |\n|---|\n| e |\n")
    assert [row.header for row in table_rows(text)] == [True, False, False, True, False]


def test_a_section_runs_to_the_next_heading_of_its_level_or_shallower() -> None:
    """Deeper headings and a fenced heading-shaped line stay in it; a setext heading ends it."""
    text = Prose("# T\n## A ##\nx\n### Deep\n```\n## no\n```\nEnd\n---\nafter\n")
    found = section(text, Prose("## A"))
    assert found == Section(
        Heading(2, 2, Prose("A"), Prose("A"), setext=False, opening_code=None, nested=False), 3, 8
    )


def test_a_section_with_no_closing_heading_runs_to_the_end() -> None:
    """The last section ends one past the last line; the first heading of a name opens it."""
    text = Prose("## A\nx\n## A\ny\n")
    assert section(text, Prose("## A")) == Section(
        Heading(1, 2, Prose("A"), Prose("A"), setext=False, opening_code=None, nested=False), 2, 3
    )
    assert section(Prose("## B\n"), Prose("## A")) is None
    assert section(Prose("# A\n"), Prose("## A")) is None


@pytest.mark.parametrize("spelled", [Prose("A"), Prose("## A\n## B")], ids=["none", "two"])
def test_a_section_must_be_named_by_one_heading(spelled: Prose) -> None:
    """A spelling that is not one heading names no section, and asking for it is an error."""
    with pytest.raises(ValueError, match=rf"^{re.escape(repr(spelled))} is not one heading$"):
        _ = section(Prose("## A\n"), spelled)


def test_blocks_carry_their_lines_kinds_and_containers() -> None:
    """Each block of every kind, its first and last lines, and the containers around it."""
    text = Prose(
        "# H\n\nPara\n\n> - item\n>   more\n>\n>   second\n\n1. one\n\n"
        + "<div>\nx\n</div>\n\n| a |\n|---|\n| b |\n\n---\n\n    code\n\n```\nf\n```\n"
    )
    assert blocks(text) == [
        Block("heading", 1, 1, ()),
        Block("paragraph", 3, 3, ()),
        Block("quote", 5, 8, ()),
        Block("list", 5, 8, ("quote",)),
        Block("item", 5, 8, ("quote", "list")),
        Block("paragraph", 5, 6, ("quote", "list", "item")),
        Block("paragraph", 8, 8, ("quote", "list", "item")),
        Block("list", 10, 11, ()),
        Block("item", 10, 11, ("list",)),
        Block("paragraph", 10, 10, ("list", "item")),
        Block("html", 12, 14, ()),
        Block("table", 16, 18, ()),
        Block("rule", 20, 20, ()),
        Block("code", 22, 22, ()),
        Block("fence", 24, 26, ()),
    ]


@pytest.mark.parametrize(
    "space",
    [Prose("\u00a0"), Prose("\x0c"), Prose("\u2028"), Prose("\u3000"), Prose("\x85")],
    ids=["nbsp", "form-feed", "line-separator", "ideographic", "next-line"],
)
def test_a_leading_line_the_parser_trims_keeps_every_number(space: Prose) -> None:
    """A paragraph whose first line holds only a space str.strip drops keeps its line numbers."""
    text = Prose(f"{space}\nfoo `x` [a](b.md)\n")
    assert prose_lines(_DOC, text) == [(1, Prose("")), (2, Prose("foo  [a](b.md)"))]
    assert [found.line for found in links(text)] == [2]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("> \u00a0\n> foo `x`\n"), [(1, Prose("")), (2, Prose("foo "))]),
        (Prose("> foo `x`\n> \u00a0\n"), [(1, Prose("foo ")), (2, Prose(""))]),
        (Prose("- \u3000\n  foo `x`\n"), [(1, Prose("")), (2, Prose("foo "))]),
        (Prose("\u00a0\nfoo `x`\n===\n"), [(1, Prose("")), (2, Prose("foo ")), (3, Prose(""))]),
        (Prose("\u00a0\na `b\nc` d\n"), [(1, Prose("")), (2, Prose("a ")), (3, Prose(" d"))]),
    ],
    ids=["quote-leading", "quote-trailing", "item-leading", "setext", "span-across-lines"],
)
def test_lines_the_parser_trims_are_empty_and_the_rest_keep_their_numbers(
    text: Prose, expected: list[tuple[PositiveInt, Prose]]
) -> None:
    """In a quote, an item or a setext heading, a trimmed line is empty and the marks are gone."""
    assert prose_lines(_DOC, text) == expected


def test_a_reference_definitions_trailing_unicode_space_is_trimmed_by_the_parser() -> None:
    """markdown-it-py trims a no-break space ending a definition's block, which CommonMark keeps."""
    assert definitions(Prose("[a]: x.md\u00a0\n")) == [Definition(1, Destination("x.md"))]


def test_an_images_description_keeps_its_escapes_and_entities() -> None:
    """An escaped mark and an entity in a description read as what they render."""
    found = links(Prose("![a \\* &amp; b](p.png)\n"))
    assert [link.prose for link in found] == [Prose("a * & b")]


def test_a_hard_break_reads_as_a_newline_in_link_text_after_it_and_in_a_heading() -> None:
    """A backslash or two spaces before a line end is a break, read as a newline."""
    found = links(Prose("[a\\\nb](x.md) c  \nd\n"))
    assert [(link.prose, link.after) for link in found] == [(Prose("a\nb"), Prose(" c\nd"))]
    assert [heading.text for heading in headings(Prose("a  \nb\n===\n"))] == [Prose("a\nb")]


def test_text_struck_through_renders_without_its_marks() -> None:
    """GitHub's strikethrough is markup, so a heading's rendered text has no tildes."""
    assert [heading.text for heading in headings(Prose("# a ~~b~~ c\n"))] == [Prose("a b c")]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("[](a.md) after\n"), [(Prose(""), Prose(" after"))]),
        (Prose("[a](x.md)[b](y.md) z\n"), [(Prose("a"), Prose("")), (Prose("b"), Prose(" z"))]),
    ],
    ids=["empty-text", "adjacent"],
)
def test_a_links_text_ends_at_its_own_close(
    text: Prose, expected: list[tuple[Prose, Prose]]
) -> None:
    """An empty text and a link right after another end where their own brackets do."""
    assert [(link.prose, link.after) for link in links(text)] == expected


def test_a_code_span_in_an_image_away_from_the_start_is_dropped() -> None:
    """The description's offsets count from the image's own position in the line."""
    assert prose_lines(_DOC, Prose("x ![a `b`](c.png) d\n")) == [(1, Prose("x ![a ](c.png) d"))]


def test_a_nul_reads_as_the_replacement_character() -> None:
    """The parser reads U+0000 as U+FFFD, and so do the lines."""
    assert lines(Prose("a\0b\n")) == (Prose("a\ufffdb"), Prose(""))


@pytest.mark.parametrize(
    ("text", "end"),
    [(Prose("## A\nx\n"), 4), (Prose("## A\nx"), 3)],
    ids=["closing-newline", "no-closing-newline"],
)
def test_a_last_section_ends_one_past_the_last_line(text: Prose, end: PositiveInt) -> None:
    """The end counts the empty line a closing newline leaves, as ``lines`` does."""
    found = section(text, Prose("## A"))
    assert found is not None
    assert (found.first, found.end) == (2, end)


@pytest.mark.parametrize(
    ("closing", "end"),
    [(Prose("> ## B"), 6), (Prose("- # B"), 6), (Prose("B\n="), 4)],
    ids=["in-a-quote", "in-an-item", "setext"],
)
def test_only_a_top_level_heading_closes_a_section(closing: Prose, end: PositiveInt) -> None:
    """A heading in a quote or a list item stays in the section; an underlined one ends it."""
    found = section(Prose(f"## A\nx\n\n{closing}\n"), Prose("## A"))
    assert found is not None
    assert found.end == end


def test_only_a_top_level_heading_opens_a_section() -> None:
    """A heading of the name in a quote is no section's; every top-level one opens its own."""
    text = Prose("> ## A\n\n## A\nx\n## A\ny\n")
    assert [(found.first, found.end) for found in sections(text, Prose("## A"))] == [(4, 5), (6, 8)]
    found = section(text, Prose("## A"))
    assert found is not None
    assert found.first == 4


def test_a_heading_says_whether_a_container_holds_it() -> None:
    """A heading in a quote or a list item is nested; one at the top level is not."""
    text = Prose("# Top\n\n> # Quoted\n\n- # Listed\n")
    assert [heading.nested for heading in headings(text)] == [False, True, True]


def test_code_blocks_are_every_fenced_and_indented_blocks_content() -> None:
    """A fence's content without its fence lines, an indented block's without its indent."""
    text = Prose("```\na\n```\n\n    b\n\n- ~~~\n  c\n  ~~~\n")
    assert code_blocks(text) == [Prose("a\n"), Prose("b\n"), Prose("c\n")]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("#### `a` b\n"), Prose("a")),
        (Prose("#### `` a` `` b\n"), Prose("a`")),
        (Prose("#### b `a`\n"), None),
        (Prose("#### `a``\n"), None),
    ],
    ids=["single", "double", "span-not-first", "unclosed"],
)
def test_a_headings_opening_code_is_the_span_it_opens_on(
    text: Prose, expected: Prose | None
) -> None:
    """The content of the code span the heading's text opens on, of any backtick run."""
    assert [heading.opening_code for heading in headings(text)] == [expected]


def test_table_rows_are_read_in_a_quote_and_in_a_list_item() -> None:
    """A table inside a container has rows like any other."""
    text = Prose("> | a |\n> |---|\n> | b |\n\n- | c |\n  |---|\n")
    assert table_rows(text) == [
        Row(1, (Prose("a"),), (Prose("a"),), header=True),
        Row(3, (Prose("b"),), (Prose("b"),), header=False),
        Row(5, (Prose("c"),), (Prose("c"),), header=True),
    ]


def test_an_empty_destination_in_pointy_brackets_is_a_link() -> None:
    """``[a](<>)`` links to the empty destination, as CommonMark has it."""
    assert [found.destination for found in links(Prose("[a](<>)\n"))] == [Destination("")]


def test_a_paragraph_of_a_trimmed_space_alone_is_one_empty_line() -> None:
    """A paragraph holding only a no-break space is its one line, empty."""
    assert prose_lines(_DOC, Prose("\u00a0\n")) == [(1, Prose(""))]


def test_a_paragraph_before_a_table_adds_no_cell() -> None:
    """Text outside a table is no row's cell."""
    assert table_rows(Prose("Text\n\n| a |\n|---|\n\nMore\n")) == [
        Row(3, (Prose("a"),), (Prose("a"),), header=True)
    ]


def test_every_heading_level_is_read() -> None:
    """A run of one to six, and the two underlines, give the levels they spell."""
    text = Prose("# a\n## b\n### c\n#### d\n##### e\n###### f\n\ng\n=\n\nh\n-\n")
    assert [heading.level for heading in headings(text)] == [1, 2, 3, 4, 5, 6, 1, 2]

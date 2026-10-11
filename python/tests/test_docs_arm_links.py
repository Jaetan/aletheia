# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The link arm of the documentation gate, run over planted trees.

A clean fixture holds every shape of link the arm resolves or leaves alone and
yields nothing; each planted defect yields exactly its one finding, naming the
document that holds the link.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import plant, run_planted

from tools._common import RelPath
from tools.docs_arms.links import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_GUIDE = RelPath("docs/guide.md")
_OTHER = Prose(
    "# Other\n\n## Same Name\n\n## Same Name\n\n## Change Detection & Stability\n\n"
    + '<a id="Kept-Anchor"></a>\n'
)
_CLEAN = Prose(
    "# Guide\n\n## Local Part\n\n"
    + "[file](other.md) [dir](../src) [root](../) [here](#local-part) [case](#Local-Part)\n"
    + "[there](other.md#change-detection--stability) [repeat](other.md#same-name-1)\n"
    + "[html](other.md#kept-anchor) [code line](../src/main.py#L1)\n"
    + '[titled](other.md "Other") [web](http://example.com/x) [tls](https://example.com/x)\n'
    + "[mail](mailto:a@example.com) [phone](tel:123) [route](#!/x) <https://example.com/auto>\n"
    + "[ref]: other.md\n"
    + "```\n[fenced](nope.md)\n```\n"
    + "Inline `[span](nope.md)` is code.\n"
)


def _repo(tmp_path: Path, guide: Prose = _CLEAN) -> Path:
    """Return a planted tree holding the guide, the document it links and a source."""
    return plant(
        tmp_path / "repo",
        {
            _GUIDE: guide,
            RelPath("docs/other.md"): _OTHER,
            RelPath("src/main.py"): Prose("print()\n"),
        },
    )


def _run(repo: Path) -> list[Prose]:
    return run_planted(findings, repo)


def test_every_resolving_shape_is_clean(tmp_path: Path) -> None:
    """Files, directories, the root, anchors of every kind, titles and schemes: no finding."""
    assert _run(_repo(tmp_path)) == list[Prose]()


@pytest.mark.parametrize(
    ("line", "finding"),
    [
        (Prose("[gone](nope.md)"), Prose("broken link -> nope.md")),
        (Prose("[gone]: nope.md"), Prose("broken link -> nope.md")),
        (Prose("[](nope.md)"), Prose("broken link -> nope.md")),
        (Prose("   [gone]: nope.md"), Prose("broken link -> nope.md")),
        (Prose("[`gone`]: nope.md"), Prose("broken link -> nope.md")),
        (
            Prose("[out](../../../../etc/passwd)"),
            Prose("link escapes the repo -> ../../../../etc/passwd"),
        ),
        (Prose("[here](#missing)"), Prose("broken anchor -> #missing")),
        (Prose("[there](other.md#missing)"), Prose("broken anchor -> other.md#missing")),
        (Prose("[third](other.md#same-name-2)"), Prose("broken anchor -> other.md#same-name-2")),
    ],
    ids=[
        "link",
        "reference",
        "empty-text",
        "indented-reference",
        "code-span-label",
        "escape",
        "same-file-anchor",
        "cross-file-anchor",
        "repeat-past-last",
    ],
)
def test_a_planted_defect_is_its_one_finding(tmp_path: Path, line: Prose, finding: Prose) -> None:
    """Each defect is reported once, against the document holding the link."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{line}\n"))
    assert _run(repo) == [Prose(f"{_GUIDE}: {finding}")]


@pytest.mark.parametrize("separator", [Prose(" "), Prose("\t")], ids=["space", "tab"])
def test_a_title_after_any_whitespace_is_not_part_of_the_target(
    tmp_path: Path, separator: Prose
) -> None:
    """A title after a space or a tab is dropped, the finding naming the destination alone."""
    repo = _repo(tmp_path, Prose(f'{_CLEAN}\n[titled](nope.md{separator}"Nope")\n'))
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> nope.md")]


@pytest.mark.parametrize(
    "link",
    [
        Prose("[gone\nlink](nope.md)"),
        Prose('[gone](nope.md\n"Nope")'),
        Prose("[run\n`make`\nnow](nope.md)"),
    ],
    ids=["text", "title", "code-span-line"],
)
def test_a_link_running_onto_the_next_line_is_read(tmp_path: Path, link: Prose) -> None:
    """A link whose text or title runs onto later lines, one holding only a code span, is read."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> nope.md")]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        (Prose("[a\n\nb](nope.md)"), []),
        (
            Prose("[a](x.md\n\n[b]: y.md\n\nSee (note)."),
            [Prose(f"{_GUIDE}: broken link -> y.md")],
        ),
        (Prose("[a](x.md\n```\ncode\n```\nb) c"), []),
    ],
    ids=["text", "destination", "fence"],
)
def test_no_link_crosses_a_paragraph_break(
    tmp_path: Path, text: Prose, expected: list[Prose]
) -> None:
    """A blank line or fenced code ends a paragraph, where a link's text or destination stops."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{text}\n"))) == expected


@pytest.mark.parametrize(
    "text",
    [
        Prose("[a]:\n\nfoo bar"),
        Prose("\u00a0[a]: nope.md"),
        Prose("A paragraph\n[a]: nope.md"),
        Prose("    [a]: nope.md"),
    ],
    ids=["blank-line", "no-break-space-indent", "paragraph-continuation", "indented-code"],
)
def test_what_commonmark_reads_as_no_definition_is_no_link(tmp_path: Path, text: Prose) -> None:
    """A destination past a blank line, a no-break space indent, a paragraph's line, code: none."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{text}\n"))) == list[Prose]()


@pytest.mark.parametrize(
    ("text", "target"),
    [
        (Prose("[a]:\n  nope.md"), Prose("nope.md")),
        (Prose("[a]: `x`\nfoo"), Prose("`x`")),
        (Prose("> [a]: nope.md"), Prose("nope.md")),
        (Prose("[a](nope.md`x`)"), Prose("nope.md`x`")),
        (Prose("[a](<nope.md>)"), Prose("nope.md")),
        (Prose("[a](<my nope.md>)"), Prose("my nope.md")),
        (Prose("[a](nope\\_x.md)"), Prose("nope_x.md")),
    ],
    ids=[
        "destination-on-the-next-line",
        "backticks-in-a-definition",
        "definition-in-a-quote",
        "backticks-in-a-destination",
        "pointy-brackets",
        "pointy-brackets-with-a-space",
        "escape",
    ],
)
def test_a_destination_is_read_as_commonmark_writes_it(
    tmp_path: Path, text: Prose, target: Prose
) -> None:
    """A destination on the definition's next line, holding backticks, in a quote, in brackets."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{text}\n"))) == [
        Prose(f"{_GUIDE}: broken link -> {target}")
    ]


@pytest.mark.parametrize(
    "link",
    [
        Prose("[a](\n`x`\nnope.md)"),
        Prose("[a](`x` nope.md)"),
        Prose("[a](nope.md `x`)"),
    ],
    ids=["own-line", "first", "after-destination"],
)
def test_text_after_a_destination_that_is_no_title_makes_no_link(
    tmp_path: Path, link: Prose
) -> None:
    """Words after a destination that no quotes or parentheses make a title leave no link."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))) == list[Prose]()


@pytest.mark.parametrize(
    "link", [Prose("[a](my%20file.md)"), Prose("[a](<my file.md>)")], ids=["encoded", "pointy"]
)
def test_a_destination_names_the_file_its_encoding_spells(tmp_path: Path, link: Prose) -> None:
    """A percent-encoded space and a space between pointy brackets both name ``my file.md``."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    _ = plant(repo, {RelPath("docs/my file.md"): Prose("# Mine\n")})
    assert _run(repo) == list[Prose]()


def test_an_image_inside_a_link_leaves_both_read(tmp_path: Path) -> None:
    """A badge image inside a link names two targets: the link's, opening first, then its own."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[![badge](nope.svg)](gone.md)\n"))
    assert _run(repo) == [
        Prose(f"{_GUIDE}: broken link -> gone.md"),
        Prose(f"{_GUIDE}: broken link -> nope.svg"),
    ]


def test_a_reference_link_is_read_once_at_its_definition(tmp_path: Path) -> None:
    """A link naming a definition holds no target of its own; the definition's is read once."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[a][gone] and [gone]\n\n[gone]: nope.md\n"))
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> nope.md")]


def test_a_code_span_in_a_links_text_leaves_it_read(tmp_path: Path) -> None:
    """A link whose text holds a code span is read, the finding naming its destination."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[the `x` call](nope.md)\n"))
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> nope.md")]


@pytest.mark.parametrize(
    "link", [Prose("[nbsp](g\u00a0b.md)"), Prose("[nbsp]: g\u00a0b.md")], ids=["link", "reference"]
)
def test_a_no_break_space_stays_in_the_destination(tmp_path: Path, link: Prose) -> None:
    """A link to a tracked path holding a no-break space resolves, that space being no separator."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    _ = plant(repo, {RelPath("docs/g\u00a0b.md"): Prose("# G\n")})
    assert _run(repo) == list[Prose]()


def test_findings_follow_the_links_through_the_document(tmp_path: Path) -> None:
    """Inline links and reference definitions are reported in the order the document holds them."""
    guide = Prose(f"{_CLEAN}\n[a]: one.md\n\n[b](two.md)\n\n[c]: three.md\n\n[d](four.md)\n")
    assert _run(_repo(tmp_path, guide)) == [
        Prose(f"{_GUIDE}: broken link -> {name}.md") for name in ("one", "two", "three", "four")
    ]


def test_a_blank_destination_links_its_own_document(tmp_path: Path) -> None:
    """A destination of whitespace alone names the document holding the link: no finding."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n[self]( )\n"))) == list[Prose]()


def test_a_file_on_disk_that_git_does_not_track_is_a_broken_link(tmp_path: Path) -> None:
    """A fresh checkout lacks an untracked file, so a link to it is broken here too."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[local](local.html)\n"))
    _ = (repo / "docs" / "local.html").write_text("<p>local</p>\n", encoding="utf-8")
    untracked = {RelPath("docs/local.html")}
    assert run_planted(findings, repo, untracked=untracked) == [
        Prose(f"{_GUIDE}: broken link -> local.html")
    ]


@pytest.mark.parametrize(
    "link",
    [Prose("[web](https://example.com)"), Prose('[web]( https://example.com "Web")')],
    ids=["scheme", "scheme-after-a-space"],
)
def test_documents_carrying_no_link_are_a_finding(tmp_path: Path, link: Prose) -> None:
    """With nothing to resolve the scan holds nothing, which is reported."""
    repo = plant(tmp_path / "repo", {_GUIDE: Prose(f"# Guide\n\n{link}\n")})
    assert _run(repo) == [Prose("README.md: no document read carries a link to resolve")]


def test_a_scheme_after_a_no_break_space_is_a_link_to_resolve(tmp_path: Path) -> None:
    """A no-break space opens the destination, so the link is resolved and the scan holds it."""
    repo = plant(
        tmp_path / "repo", {_GUIDE: Prose("# Guide\n\n[web](\u00a0https://example.com)\n")}
    )
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> \u00a0https://example.com")]


def test_a_linked_document_the_work_tree_lacks_is_named_and_still_resolves(tmp_path: Path) -> None:
    """A tracked target the work tree lacks still resolves; the read names it, anchors unchecked."""
    repo = _repo(tmp_path)
    other = RelPath("docs/other.md")
    (repo / other).unlink()
    assert run_planted(findings, repo, absent={other}) == [
        Prose(f"{other}: could not be read, so what it says is unchecked")
    ]


def test_every_document_the_work_tree_lacks_leaves_no_link(tmp_path: Path) -> None:
    """With the one document unread there is nothing to resolve, which is reported."""
    repo = plant(tmp_path / "repo", {RelPath("src/main.py"): Prose("print()\n")})
    assert run_planted(findings, repo, absent={_GUIDE}) == [
        Prose(f"{_GUIDE}: could not be read, so what it says is unchecked"),
        Prose("README.md: no document read carries a link to resolve"),
    ]


@pytest.mark.parametrize(
    "target",
    [Prose("telnope.md"), Prose("http/nope.md"), Prose("mailtonope.md")],
    ids=["tel", "http", "mailto"],
)
def test_only_a_whole_scheme_leaves_a_target_unresolved(tmp_path: Path, target: Prose) -> None:
    """A path that begins like a scheme but is not one is resolved like any other."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[x]({target})\n"))
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> {target}")]


def test_links_on_one_line_are_reported_in_their_order(tmp_path: Path) -> None:
    """Two broken links on one line come in the order they are written, not sorted."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[b](zz.md) [a](aa.md)\n"))
    assert _run(repo) == [
        Prose(f"{_GUIDE}: broken link -> zz.md"),
        Prose(f"{_GUIDE}: broken link -> aa.md"),
    ]


def test_an_encoded_hash_names_a_file_not_an_anchor(tmp_path: Path) -> None:
    """``%23`` is decoded after the anchor is split off, so it names a ``#`` in the file."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[h](a%23b.md)\n"))
    _ = plant(repo, {RelPath("docs/a#b.md"): Prose("# A\n")})
    assert _run(repo) == list[Prose]()


def test_an_encoded_anchor_is_compared_decoded(tmp_path: Path) -> None:
    """An anchor spelled with percent-escapes names the heading whose slug it decodes to."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n## Café\n\n[c](#caf%C3%A9)\n"))
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    "target",
    [
        Prose("HTTPS://example.com"),
        Prose("ftp://example.com/x"),
        Prose("javascript:void"),
        Prose("C:/x.md"),
    ],
    ids=["upper-case", "ftp", "javascript", "drive-letter"],
)
def test_a_target_with_any_scheme_is_absolute(tmp_path: Path, target: Prose) -> None:
    """A URI scheme in any case, a ``javascript:`` link included, makes a target absolute."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[x]({target})\n"))
    assert _run(repo) == list[Prose]()


def test_an_autolink_is_never_resolved(tmp_path: Path) -> None:
    """An autolink holds an absolute address, whatever its scheme."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n<ftp://example.com/x> <file:///x.md>\n"))
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    ("link", "found"),
    [
        (Prose("[q](other.md?plain=1)"), list[Prose]()),
        (Prose("[q](other.md?plain=1#same-name)"), list[Prose]()),
        (Prose("[q](q?b.md)"), [Prose(f"{_GUIDE}: broken link -> q?b.md")]),
        (Prose("[q](q%3Fb.md)"), list[Prose]()),
    ],
    ids=["query", "query-and-anchor", "question-mark-starts-a-query", "encoded-question-mark"],
)
def test_a_query_is_dropped_before_the_path_is_read(
    tmp_path: Path, link: Prose, found: list[Prose]
) -> None:
    """A ``?`` starts a query, so a file named with one is linked as ``%3F``."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    _ = plant(repo, {RelPath("docs/q?b.md"): Prose("# Q\n")})
    assert _run(repo) == found


@pytest.mark.parametrize(
    ("link", "found"),
    [
        (Prose("[r](/src/main.py)"), list[Prose]()),
        (Prose("[r](/docs/other.md#same-name)"), list[Prose]()),
        (Prose("[r](/nope.md)"), [Prose(f"{_GUIDE}: broken link -> /nope.md")]),
        (Prose("[r](other.md/)"), [Prose(f"{_GUIDE}: broken link -> other.md/")]),
        (Prose("[r](../src/)"), list[Prose]()),
    ],
    ids=[
        "root-relative",
        "root-relative-anchor",
        "root-relative-broken",
        "slash-after-a-file",
        "slash-after-a-directory",
    ],
)
def test_a_path_is_read_as_a_url_path(tmp_path: Path, link: Prose, found: list[Prose]) -> None:
    """A path opening on ``/`` starts at the root; one ending in ``/`` must be a directory."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))) == found


def test_a_symlink_git_does_not_track_is_a_broken_link(tmp_path: Path) -> None:
    """A link to an untracked symlink is broken even when the symlink leads to a tracked file."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[s](ln.md)\n"))
    (repo / "docs" / "ln.md").symlink_to("other.md")
    untracked = {RelPath("docs/ln.md")}
    assert run_planted(findings, repo, untracked=untracked) == [
        Prose(f"{_GUIDE}: broken link -> ln.md")
    ]


@pytest.mark.parametrize(
    "target",
    [Prose("//example.com/x"), Prose("///example.com/x")],
    ids=["network-path", "three-slashes"],
)
def test_a_host_after_two_slashes_is_absolute(tmp_path: Path, target: Prose) -> None:
    """A target opening on ``//`` names another host, even when a path of its name is tracked."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[n]({target})\n"))
    _ = plant(repo, {RelPath("example.com/x"): Prose("x\n")})
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    "target",
    [Prose("..%2Fsrc%2Fmain.py"), Prose("a%FF.md")],
    ids=["encoded-slash", "not-utf8"],
)
def test_a_segment_no_tracked_path_can_name_is_broken(tmp_path: Path, target: Prose) -> None:
    """An encoded ``/`` stays inside its segment, and a segment must decode as UTF-8."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[s]({target})\n"))
    _ = plant(repo, {RelPath("docs/a\ufffd.md"): Prose("# A\n")})
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> {target}")]


def test_a_parent_step_from_the_root_escapes(tmp_path: Path) -> None:
    """``..`` from a document at the root leaves the repository."""
    repo = _repo(tmp_path)
    _ = plant(repo, {RelPath("README.md"): Prose("# Root\n\n[up](..)\n")})
    assert _run(repo) == [Prose("README.md: link escapes the repo -> ..")]


def test_a_name_opening_on_two_dots_is_a_file(tmp_path: Path) -> None:
    """``..x.md`` is a file name, not a step out of the directory."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[d](..x.md)\n"))
    _ = plant(repo, {RelPath("docs/..x.md"): Prose("# D\n")})
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    ("link", "found"),
    [
        (Prose("[x](a//../b.md)"), [Prose(f"{_GUIDE}: broken link -> a//../b.md")]),
        (Prose("[x](a//b.md)"), list[Prose]()),
        (Prose("[x](a/./b.md)"), list[Prose]()),
        (Prose("[x](other.md/.)"), [Prose(f"{_GUIDE}: broken link -> other.md/.")]),
        (Prose("[x](//nope.example/x)"), list[Prose]()),
        (Prose("[x](a/b%2Fc.md)"), [Prose(f"{_GUIDE}: broken link -> a/b%2Fc.md")]),
    ],
    ids=[
        "empty-segment-dropped-before-a-parent",
        "empty-segment-dropped",
        "dot-segment",
        "dot-after-a-file",
        "network-path",
        "encoded-slash-in-a-later-segment",
    ],
)
def test_a_path_resolves_as_urljoin_resolves_it(
    tmp_path: Path, link: Prose, found: list[Prose]
) -> None:
    """urllib.parse.urljoin drops empty segments and dot segments; a final ``.`` is a directory."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    _ = plant(
        repo, {RelPath("docs/a/b.md"): Prose("# B\n"), RelPath("docs/a/b/c.md"): Prose("# C\n")}
    )
    assert _run(repo) == found


def test_a_name_opening_on_two_dots_at_the_root_is_a_file(tmp_path: Path) -> None:
    """From a document at the root, ``..x.md`` is a file beside it, not a step out."""
    repo = _repo(tmp_path)
    _ = plant(
        repo,
        {RelPath("README.md"): Prose("# Root\n\n[d](..x.md)\n"), RelPath("..x.md"): Prose("x\n")},
    )
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    ("link", "found"),
    [
        (Prose("[x](/a:b.md)"), list[Prose]()),
        (Prose("[x](< //example.com/x>)"), list[Prose]()),
        (Prose("[x](< //[::1>)"), [Prose(f"{_GUIDE}: broken link -> \x20//[::1")]),
        (Prose("[x](<other.md#\tsame-name>)"), list[Prose]()),
        (Prose("[x](/a/../../b.md)"), [Prose(f"{_GUIDE}: link escapes the repo -> /a/../../b.md")]),
    ],
    ids=[
        "colon-in-a-root-path",
        "spaced-host",
        "refused-host",
        "tab-in-the-fragment",
        "parent-above-the-root",
    ],
)
def test_a_link_is_read_once_by_urllib_parse(
    tmp_path: Path, link: Prose, found: list[Prose]
) -> None:
    """A root path keeps its slash, the scheme and host are urlsplit's, a refusal is broken."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))
    _ = plant(repo, {RelPath("a:b.md"): Prose("x\n")})
    assert _run(repo) == found

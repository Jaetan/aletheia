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
    + "[mail](mailto:a@example.com) [phone](tel:123) [route](#!/x) [auto](<nope.md>)\n"
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
    "definition",
    [Prose("[a]:\n\nfoo bar"), Prose("[a]: `x`\nfoo"), Prose("\u00a0[a]: nope.md")],
    ids=["blank-line", "code-span", "no-break-space-indent"],
)
def test_a_definition_is_read_on_its_own_line(tmp_path: Path, definition: Prose) -> None:
    """A definition opens after spaces or tabs alone, and its destination is on its own line."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{definition}\n"))) == list[Prose]()


@pytest.mark.parametrize(
    "link",
    [
        Prose("[a](\n`x`\nnope.md)"),
        Prose("[a](`x` nope.md)"),
        Prose("[a](nope.md `x`)"),
    ],
    ids=["own-line", "first", "after-destination"],
)
def test_a_code_span_in_a_links_parentheses_makes_no_link(tmp_path: Path, link: Prose) -> None:
    """A code span in a link's parentheses, before or after its destination, makes no link."""
    assert _run(_repo(tmp_path, Prose(f"{_CLEAN}\n{link}\n"))) == list[Prose]()


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
    guide = Prose(f"{_CLEAN}\n[a]: one.md\n[b](two.md)\n[c]: three.md\n[d](four.md)\n")
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

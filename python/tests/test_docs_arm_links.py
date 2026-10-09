# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The link arm of the documentation gate, run over throwaway repositories.

A clean fixture holds every shape of link the arm resolves or leaves alone and
yields nothing; each planted defect yields exactly its one finding, naming the
document that holds the link.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import committed

from tools._common import RelPath
from tools.check_docs import run_arm
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
    """Return a committed repository holding the guide, the document it links and a source."""
    return committed(
        tmp_path / "repo",
        {
            _GUIDE: guide,
            RelPath("docs/other.md"): _OTHER,
            RelPath("src/main.py"): Prose("print()\n"),
        },
    )


def _run(repo: Path) -> list[Prose]:
    return run_arm(findings, repo)


def test_every_resolving_shape_is_clean(tmp_path: Path) -> None:
    """Files, directories, the root, anchors of every kind, titles and schemes: no finding."""
    assert _run(_repo(tmp_path)) == []


@pytest.mark.parametrize(
    ("line", "finding"),
    [
        (Prose("[gone](nope.md)"), Prose("broken link -> nope.md")),
        (Prose("[gone]: nope.md"), Prose("broken link -> nope.md")),
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


def test_a_file_on_disk_that_git_does_not_track_is_a_broken_link(tmp_path: Path) -> None:
    """A fresh checkout lacks an untracked file, so a link to it is broken here too."""
    repo = _repo(tmp_path, Prose(f"{_CLEAN}\n[local](local.html)\n"))
    _ = (repo / "docs" / "local.html").write_text("<p>local</p>\n", encoding="utf-8")
    assert _run(repo) == [Prose(f"{_GUIDE}: broken link -> local.html")]


def test_documents_carrying_no_link_are_a_finding(tmp_path: Path) -> None:
    """With nothing to resolve the scan holds nothing, which is reported."""
    repo = committed(tmp_path / "repo", {_GUIDE: Prose("# Guide\n\n[web](https://example.com)\n")})
    assert _run(repo) == [Prose("README.md: no tracked document carries a link to resolve")]

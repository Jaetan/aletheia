# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate's arm over the pip extras the READMEs name.

A README naming an extra the manifest does not define is a finding naming the
README and the extra; a README naming only defined extras, in a code span or in
an install command, is clean; a set of READMEs naming no extra at all is a
finding, as is a manifest defining none.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import run_planted

from tools._common import RelPath
from tools.docs_arms.readme_extras import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

_MANIFEST = Prose("""[project]
name = "aletheia"

[project.optional-dependencies]
can = ["python-can"]
yaml = ["pyyaml"]
all = ["aletheia[can,yaml]"]
""")
_CLEAN_README = Prose("""# Aletheia

Install with `pip install -e '.[can]'` under `python/`.

```sh
pip install -e '.[can,yaml]'
```

Loading checks needs the `[yaml]` extra (or `[all]`), or `pip install 'aletheia[all]'`.

A checklist box shown as `[ ]` names no extra.
""")
_NO_EXTRA_README = Prose("""# Aletheia

Install with `pip install -e .` under `python/`.
""")


def _undefined(rel: RelPath, extra: Prose) -> Prose:
    """Return the finding for ``extra`` named by the README at ``rel``."""
    return Prose(
        f"{rel}: names the pip extra [{extra}], which python/pyproject.toml does not define"
    )


def _repo(tmp_path: Path, readme: Prose, manifest: Prose = _MANIFEST) -> Path:
    """Return a tree holding ``readme`` at the root and ``manifest`` at python/."""
    repo = tmp_path / "repo"
    (repo / "python").mkdir(parents=True)
    _ = (repo / "README.md").write_text(readme, encoding="utf-8")
    _ = (repo / "python" / "pyproject.toml").write_text(manifest, encoding="utf-8")
    return repo.resolve()


def _run(repo: Path) -> list[Prose]:
    return run_planted(findings, repo)


def test_clean_readme_has_no_finding(tmp_path: Path) -> None:
    """Every extra the README names, in a span or an install command, is defined."""
    assert _run(_repo(tmp_path, _CLEAN_README)) == list[Prose]()


def test_undefined_extra_is_a_finding(tmp_path: Path) -> None:
    """An extra the README names and the manifest lacks is reported with its README."""
    readme = Prose(_CLEAN_README + "\nThe log reader needs `pip install -e '.[gps,can]'`.\n")
    assert _run(_repo(tmp_path, readme)) == [_undefined(RelPath("README.md"), Prose("gps"))]


def test_nested_readme_is_scanned(tmp_path: Path) -> None:
    """A README below the root is held to the same manifest."""
    repo = _repo(tmp_path, _CLEAN_README)
    _ = (repo / "python" / "README.md").write_text(
        Prose("# Binding\n\nNeeds the `[excel]` extra.\n"), encoding="utf-8"
    )
    assert _run(repo) == [_undefined(RelPath("python/README.md"), Prose("excel"))]


def test_no_extra_named_anywhere_is_a_finding(tmp_path: Path) -> None:
    """A set of READMEs naming no extra leaves the claim nothing to hold."""
    assert _run(_repo(tmp_path, _NO_EXTRA_README)) == [
        Prose("README.md: no README names a pip extra; no install sentence is left")
    ]


def test_manifest_without_extras_is_a_finding(tmp_path: Path) -> None:
    """A manifest defining no extra cannot hold the README's names."""
    repo = _repo(tmp_path, _CLEAN_README, Prose('[project]\nname = "aletheia"\n'))
    assert _run(repo) == [
        Prose("python/pyproject.toml: defines no extra under [project.optional-dependencies]")
    ]


def test_untracked_manifest_is_a_finding(tmp_path: Path) -> None:
    """A manifest git does not track is absent from a checkout, so nothing holds the names."""
    repo = _repo(tmp_path, _CLEAN_README)
    assert run_planted(findings, repo, untracked={RelPath("python/pyproject.toml")}) == [
        Prose("python/pyproject.toml: not tracked, so the extras the READMEs name cannot be held")
    ]


@pytest.mark.parametrize(
    "span",
    [Prose("`[can,]`"), Prose("`pip install -e '.[can,,yaml]'`"), Prose("`[,can]`")],
    ids=["span", "install", "leading"],
)
def test_an_empty_member_of_an_extras_list_is_a_finding(tmp_path: Path, span: Prose) -> None:
    """A leading, trailing or doubled comma names an empty extra, which no manifest defines."""
    readme = Prose(f"{_CLEAN_README}\nAlso {span}.\n")
    assert _run(_repo(tmp_path, readme)) == [_undefined(RelPath("README.md"), Prose(""))]


@pytest.mark.parametrize(
    ("span", "extra"),
    [
        (Prose("`pip install -e '.[can, nosuch]'`"), Prose("nosuch")),
        (Prose("`[yaml, nosuch]`"), Prose("nosuch")),
        (Prose("`pip install -e '.[can-fd]'`"), Prose("can-fd")),
        (Prose("`pip install -e '.[can2]'`"), Prose("can2")),
        (Prose("`pip install -e '.[3]'`"), Prose("3")),
        (Prose("`pip install -e '.[can.fd]'`"), Prose("can.fd")),
        (Prose("`pip install -e '.[can_fd]'`"), Prose("can_fd")),
        (Prose("`[ nosuch]`"), Prose("nosuch")),
        (Prose("`[nosuch ]`"), Prose("nosuch")),
    ],
    ids=[
        "install-space",
        "span-space",
        "hyphen",
        "digit",
        "digits-only",
        "dot",
        "underscore",
        "space-after-bracket",
        "space-before-bracket",
    ],
)
def test_every_spelling_pep_508_allows_is_read(tmp_path: Path, span: Prose, extra: Prose) -> None:
    """A space around a name, and a name with a hyphen, digit, dot or underscore, are read."""
    readme = Prose(f"{_CLEAN_README}\nAlso {span}.\n")
    assert _run(_repo(tmp_path, readme)) == [_undefined(RelPath("README.md"), extra)]


@pytest.mark.parametrize(
    "text",
    [Prose("`extras[nosuch]`"), Prose("`[nosuch] or more`"), Prose("see [nosuch](x.md)")],
    ids=["indexing-span", "span-going-on", "link-text"],
)
def test_a_bracket_neither_alone_in_a_span_nor_installed_names_no_extra(
    tmp_path: Path, text: Prose
) -> None:
    """A bracket after other code in a span, before more of it, or as link text is no extra."""
    readme = Prose(f"{_CLEAN_README}\nAlso {text}.\n")
    assert _run(_repo(tmp_path, readme)) == list[Prose]()


def test_an_undefined_extra_of_the_package_install_is_a_finding(tmp_path: Path) -> None:
    """An install of the package by name, aletheia[...], names its extras too."""
    readme = Prose(f"{_CLEAN_README}\n```sh\npip install 'aletheia[bogus]'\n```\n")
    assert _run(_repo(tmp_path, readme)) == [_undefined(RelPath("README.md"), Prose("bogus"))]


def test_a_document_that_is_not_a_readme_is_not_read(tmp_path: Path) -> None:
    """Only a README is held to the manifest; a design note may name an extra still to come."""
    repo = _repo(tmp_path, _CLEAN_README)
    (repo / "docs").mkdir()
    _ = (repo / "docs" / "DESIGN.md").write_text(
        Prose("# Design\n\nA future `[arxml]` extra.\n"), encoding="utf-8"
    )
    assert _run(repo) == list[Prose]()


def test_one_readme_naming_an_extra_is_enough(tmp_path: Path) -> None:
    """A README naming no extra, read after one that names some, leaves no finding."""
    repo = _repo(tmp_path, _CLEAN_README)
    _ = (repo / "python" / "README.md").write_text(
        Prose("# Binding\n\nNo extra here.\n"), encoding="utf-8"
    )
    assert _run(repo) == list[Prose]()


def test_a_space_inside_a_name_is_part_of_the_name(tmp_path: Path) -> None:
    """Only the spaces around a comma separate extras: one inside a name stays in it."""
    readme = Prose(f"{_CLEAN_README}\nAlso `[can fd]`.\n")
    assert _run(_repo(tmp_path, readme)) == [_undefined(RelPath("README.md"), Prose("can fd"))]


def test_a_readmes_undefined_extras_are_reported_in_name_order(tmp_path: Path) -> None:
    """Several undefined extras of one README are reported one each, in name order."""
    readme = Prose(f"{_CLEAN_README}\nAlso `[delta]`, `[alpha]`, `[charlie]` and `[bravo]`.\n")
    assert _run(_repo(tmp_path, readme)) == [
        _undefined(RelPath("README.md"), Prose(extra))
        for extra in ("alpha", "bravo", "charlie", "delta")
    ]


def test_readmes_are_read_in_the_order_of_the_documents(tmp_path: Path) -> None:
    """The READMEs' findings come in the order the documents are handed, not resorted by path."""
    repo = _repo(tmp_path, _CLEAN_README)
    nested, top = RelPath("python/README.md"), RelPath("README.md")
    documents = {nested: Prose("Needs `[excel]`.\n"), top: Prose("Needs `[gps]`.\n")}
    tracked = [nested, top, RelPath("python/pyproject.toml")]
    assert findings(repo, tracked, documents) == [
        _undefined(nested, Prose("excel")),
        _undefined(top, Prose("gps")),
    ]

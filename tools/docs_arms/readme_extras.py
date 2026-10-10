# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every pip extra a README names is one ``python/pyproject.toml`` defines.

A README names an extra as a bracketed token, either shown on its own in an
inline code span such as ``[can]`` or inside an install command such as
``pip install -e '.[can]'`` or ``pip install 'aletheia[can]'``; a bracket may
hold several extras separated by commas, with or without a space, each name
spelled in lowercase letters, digits, dots, hyphens or underscores.  Each name
is held to the keys of ``[project.optional-dependencies]`` in
``python/pyproject.toml``, so a reader who follows an install sentence pulls a
loader that exists.  Fences are read too, since that is where the install
commands sit.

A manifest that is untracked, unread or defines no extra is a finding, and so
is a set of READMEs that names no extra at all: either leaves the claim with
nothing to hold.  A byte of the manifest that is not UTF-8 reads as U+FFFD.
"""

from __future__ import annotations

import re
import tomllib
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, TypedDict, cast

from tools._common import RelPath
from tools.docs_arms import Unread, missing, read_tracked

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

_MANIFEST = RelPath("python/pyproject.toml")
_ROOT_README = RelPath("README.md")
_EXTRAS_UNCHECKED = Prose("the extras the READMEs name cannot be held")

# The extras a bracket holds: names, commas and spaces, with one name character at
# least.  A list is read with any commas it holds, so a stray one names an empty
# extra, which nothing defines.
_EXTRAS = r"(?=[^\]]*[a-z0-9])([a-z0-9._, -]+)"
# `[can]` or `[can, yaml]` shown on its own in an inline code span.
_SPAN_EXTRA = re.compile(rf"`\[{_EXTRAS}\]`")
# The extras of an install command: `.[can]`, `'.[all,dev]'`, `aletheia[excel]`.
_INSTALL_EXTRA = re.compile(rf"(?:\.|aletheia)\[{_EXTRAS}\]")

# The manifest, by the keys read here.
_Project = TypedDict("_Project", {"optional-dependencies": dict[Prose, list[Prose]]}, total=False)


class _Manifest(TypedDict, total=False):
    project: _Project


def defined_extras(manifest: Prose) -> set[Prose]:
    """Return the keys of ``[project.optional-dependencies]`` in the manifest text ``manifest``."""
    data = cast("_Manifest", tomllib.loads(manifest))
    return set(data.get("project", {}).get("optional-dependencies", {}))


def named_extras(text: Prose) -> set[Prose]:
    """Return every extra ``text`` names, each comma group split into its stripped members."""
    groups = [*_SPAN_EXTRA.findall(text), *_INSTALL_EXTRA.findall(text)]
    return {Prose(name.strip()) for group in groups for name in group.split(",")}


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per extra a README names that the manifest does not define.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        A finding per undefined extra, naming the README and the extra, the
        READMEs in the order of ``documents`` and each one's extras in name
        order; one finding when the manifest is untracked, unread or defines no extra;
        one when no README names an extra.

    """
    if _MANIFEST not in tracked:
        return [missing(_MANIFEST, tracked, _EXTRAS_UNCHECKED)]
    manifest = read_tracked(root, _MANIFEST, _EXTRAS_UNCHECKED)
    if isinstance(manifest, Unread):
        return [manifest.finding]
    defined = defined_extras(manifest)
    if not defined:
        return [Prose(f"{_MANIFEST}: defines no extra under [project.optional-dependencies]")]
    out: list[Prose] = []
    named_anywhere = False
    for rel, text in documents.items():
        if PurePosixPath(rel).name != "README.md":
            continue
        named = named_extras(text)
        named_anywhere = named_anywhere or bool(named)
        out.extend(
            Prose(f"{rel}: names the pip extra [{extra}], which {_MANIFEST} does not define")
            for extra in sorted(named - defined)
        )
    if not named_anywhere:
        out.append(
            Prose(f"{_ROOT_README}: no README read names a pip extra; no install sentence is left")
        )
    return out

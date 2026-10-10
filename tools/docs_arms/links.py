# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every relative link and anchor in a tracked document resolves in a fresh checkout.

The document is read as CommonMark (``tools._markdown``): an inline link or image
``[text](target)`` and a reference definition ``[id]: target`` name a target, read
where it is written, so a reference link counts at its definition.  Each target is
read once by ``urllib.parse``: one ``urlsplit`` reads with a scheme or a host, an
autolink among them, is absolute and not resolved, and neither is a ``#!`` route,
which names a page of a client-side router rather than an anchor.  Any other is a
URL reference, resolved by ``urljoin`` against the document's own URL, a path
opening on ``/`` taken from the repository root as GitHub rewrites it in rendered
Markdown.  The query is dropped, and each segment of the path is percent-decoded
as UTF-8, so ``%23`` and ``%3F`` are a ``#`` and a ``?`` inside a file name, while
a ``%2F`` names no tracked path, no file name holding a ``/``; a target
``urllib.parse`` refuses is broken.  The path resolves when git tracks it, as a
file or as a directory on the way to one, or when it is the repository root, and
one ending in ``/`` must be a directory: a fresh checkout holds what git tracks,
so neither a gitignored file nor a symlink in one working tree counts. A path
leading out of the repository, ``..`` above its root included, is a finding even
when something is there. The fragment, percent-decoded, must be one of the target
document's anchors, compared without case: a heading's GitHub slug, suffixed
``-1``, ``-2`` for a repeat, or an HTML fragment, any element's ``id`` or an ``a``
element's ``name``. An anchor into any other file is not checked. A tree whose
documents carry no link to resolve is a finding, the scan holding nothing. An
anchor into a document the work tree cannot give goes unchecked here: the gate
names that document as unread.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal, NamedTuple
from urllib.parse import quote, unquote, urljoin, urlsplit, urlunsplit

from tools import _markdown
from tools._common import RelPath
from tools.docs_arms import header_slugs, tracked_dirs

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

# The URL a document is read under: its path below the repository's own root segment, so
# a link whose resolved path leaves that segment leaves the repository.
_ROOT_PATH = "/root/"
_BASE = f"https://repository.invalid{_ROOT_PATH}"
# The repository root, as a link that resolves to it names it: the empty path.
_ROOT = RelPath("")


class Checkout(NamedTuple):
    """What a fresh checkout holds: each tracked file, the root and each directory above one."""

    files: frozenset[RelPath]
    dirs: frozenset[RelPath]

    def holds(self, rel: RelPath) -> bool:
        """Whether ``rel``, repo-relative, is a tracked file or a directory of the checkout."""
        return rel in self.files or rel in self.dirs


def links(text: Prose) -> list[Prose]:
    """Return the target written at each link, image, autolink and definition of ``text``, in order.

    A reference link has no target of its own: it counts at its definition.
    """
    written = [
        *((found.line, found.destination) for found in _markdown.links(text) if found.written_here),
        *((found.line, found.destination) for found in _markdown.definitions(text)),
    ]
    return [Prose(target) for _, target in sorted(written, key=lambda pair: pair[0])]


class _Named(NamedTuple):
    """The repository path a link names, whether it writes a directory, and its anchor."""

    path: RelPath
    directory: bool
    anchor: Prose


# What a link reads as when it names no path and is not broken: absolute, or leaving the repository.
type _Unnamed = Literal["absolute", "escapes"]


def _read(rel: RelPath, link: Prose) -> _Named | _Unnamed | None:
    """Return what ``link`` of document ``rel`` names, read once by ``urllib.parse``.

    A ``#!`` route, and a link ``urlsplit`` reads with a scheme or a host, are
    absolute.  Any other is resolved by ``urljoin`` against the document's own URL, a
    path opening on ``/`` from the repository root, as GitHub rewrites it; the query
    is dropped, a path out of the repository escapes, and each segment is
    percent-decoded as UTF-8, a segment that cannot be, one decoding to hold a ``/``,
    or a link ``urllib.parse`` refuses being broken, None.
    """
    if link.startswith("#!"):
        return "absolute"
    try:
        written = urlsplit(link)
        if written.scheme or written.netloc:
            return "absolute"
        if written.path.startswith("/"):
            written = written._replace(path=_ROOT_PATH.removesuffix("/") + written.path)
        joined = urlsplit(urljoin(_BASE + quote(rel), urlunsplit(written)))
    except ValueError:
        return None
    if not joined.path.startswith(_ROOT_PATH):
        return "escapes"
    inner = joined.path.removeprefix(_ROOT_PATH)
    path = _decoded(Prose(inner.removesuffix("/")))
    if path is None:
        return None
    return _Named(path, inner.endswith("/"), Prose(unquote(joined.fragment)))


def _decoded(inner: Prose) -> RelPath | None:
    """Return the repository path ``inner``, each segment percent-decoded; None when one can't be.

    A segment that is not UTF-8 once decoded, or that decodes to one holding a
    ``/``, names no tracked path.
    """
    try:
        segments = [unquote(segment, errors="strict") for segment in inner.split("/")]
    except UnicodeDecodeError:
        return None
    if any("/" in segment for segment in segments):
        return None
    return RelPath("/".join(segments))


def _link_finding(
    rel: RelPath,
    link: Prose,
    checkout: Checkout,
    anchors: Mapping[RelPath, set[Prose]],
) -> Prose | None:
    """Return the finding for one link of document ``rel``, or None when it resolves.

    ``anchors`` holds each document's anchors in lower case, as they are compared.
    """
    named = _read(rel, link)
    if named == "absolute":
        return None
    if named == "escapes":
        return Prose(f"{rel}: link escapes the repo -> {link}")
    if (
        named is None
        or not checkout.holds(named.path)
        or (named.directory and named.path not in checkout.dirs)
    ):
        return Prose(f"{rel}: broken link -> {link}")
    if named.anchor and named.path in anchors and named.anchor.lower() not in anchors[named.path]:
        return Prose(f"{rel}: broken anchor -> {link}")
    return None


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per link of a tracked document that does not resolve.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Each tracked Markdown file's text the work tree gives, by repo-relative path.

    Returns:
        The findings, each naming the document that holds the link.

    """
    del root
    checkout = Checkout(frozenset(tracked), frozenset({_ROOT, *tracked_dirs(tracked)}))
    anchors = {
        rel: {Prose(slug.lower()) for slug in header_slugs(text)} for rel, text in documents.items()
    }
    found = [(rel, link) for rel, text in documents.items() for link in links(text)]
    if all(_read(rel, link) == "absolute" for rel, link in found):
        return [Prose("README.md: no document read carries a link to resolve")]
    return [
        finding
        for rel, link in found
        if (finding := _link_finding(rel, link, checkout, anchors)) is not None
    ]

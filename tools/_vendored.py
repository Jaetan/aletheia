# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The third-party files the tree keeps verbatim, under ``tools/_vendor/``.

Each directory there holds files copied byte for byte from one upstream
release, beside a record, ``UPSTREAM.toml``, naming the release's tag, the
toolchain version the bytes were checked at where a toolchain pins one, and
each file's git blob sha upstream.  A verbatim file is upstream's text, not the
tree's, so the gates holding the tree's own code to its rules (the linters,
the type-hint lens) leave the directory alone, the licence header gate leaves
out the files a record names while holding the record itself, and the
source-length gate exempts a file there only while its blob sha is the one its
record names, since an edited copy is the tree's own again.
"""

from __future__ import annotations

import hashlib
import tomllib
from pathlib import PurePosixPath
from typing import TYPE_CHECKING, NewType, TypedDict, cast

from tools._common import RelPath

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path

# The directory every vendored file sits under, and the name of the record in each directory there.
VENDOR = RelPath("tools/_vendor/")
RECORD = "UPSTREAM.toml"

# The bytes of a tracked file.
FileBytes = NewType("FileBytes", bytes)
# The name git gives an object, its hex sha-1: ``24b737139dba8da1384a5a42ea1caa9a99bd8f56``.
BlobSha = NewType("BlobSha", str)
# A vendored file's name in its directory: ``cindex.py``.
VendoredName = NewType("VendoredName", str)
# An upstream release tag: ``llvmorg-23.1.5``.
UpstreamTag = NewType("UpstreamTag", str)
# An upstream version, as a toolchain pin names it: ``23.1.6``.
UpstreamVersion = NewType("UpstreamVersion", str)


class UnreadRecordError(Exception):
    """A record under the vendor directory that cannot be read, named with the reason."""


class Upstream(TypedDict, total=False):
    """A record: the upstream release's tag, the pinned toolchain version, each file's blob sha."""

    tag: UpstreamTag
    toolchain: UpstreamVersion
    blobs: dict[VendoredName, BlobSha]


def blob_sha(data: FileBytes) -> BlobSha:
    """Return the name git gives ``data`` as a blob, the one ``git hash-object`` prints."""
    header = f"blob {len(data)}\0".encode()
    return BlobSha(hashlib.sha1(header + data, usedforsecurity=False).hexdigest())


def read_record(path: Path) -> Upstream:
    """Return the record at ``path``; raise OSError or ValueError where it cannot be read."""
    return cast("Upstream", tomllib.loads(path.read_text(encoding="utf-8")))


def recorded_blobs(repo: Path, tracked: Iterable[RelPath]) -> dict[RelPath, BlobSha]:
    """Return each vendored file's recorded blob sha by its path.

    The records read are the ones ``tracked`` lists under the vendor directory,
    each naming the files of its own directory; one that cannot be read raises
    ``UnreadRecordError`` naming it.
    """
    blobs: dict[RelPath, BlobSha] = {}
    for rel in tracked:
        path = PurePosixPath(rel)
        if not rel.startswith(VENDOR) or path.name != RECORD:
            continue
        try:
            record = read_record(repo / rel)
        except (OSError, ValueError) as unread:
            raise UnreadRecordError(Prose(f"{rel}: {unread}")) from unread
        for name, sha in record.get("blobs", {}).items():
            blobs[RelPath((path.parent / name).as_posix())] = sha
    return blobs

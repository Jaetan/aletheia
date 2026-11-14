# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Source-length gate: no code file in the tracked tree is over 1000 lines.

A file a reader cannot hold whole is split along a seam it already has: a test
file by the subject its cases test, a source file by the type or concern it
implements. The cap is the one pylint holds Python to (``max-module-lines``),
applied to every language the tree compiles or interprets, with no allowlist
and one exemption, upstream's code kept verbatim: any other file over it is
split, never listed.

## What is a code file

A tracked file whose suffix names a language a compiler or an interpreter
reads (``_CODE_SUFFIXES``), or a build program by its name: ``CMakeLists.txt``,
``Dockerfile``, and a ``Dockerfile.<variant>`` whatever its variant
(``_CODE_NAMES``, ``_CODE_PREFIXES``). A template (``.in``) is judged by the
file it becomes. Data a program reads (YAML, TOML, JSON, snapshots), prose (Markdown)
and package descriptions (``.cabal``, ``.agda-lib``) are not code and are not
measured.

## How a line is counted

As ``wc -l`` counts it: one per newline byte. A file without a final newline
is one line shorter than a reader sees, which is the direction that never
fails a file the shell would pass.

## What is exempt

A file under ``tools/_vendor/`` whose git blob sha is the one its directory's
``UPSTREAM.toml`` records (``tools/_vendored.py``): it is upstream's text,
kept whole, and splitting it would make it the tree's own.  The exemption is
by path and sha both, so a vendored file edited in the tree, or the same bytes
anywhere else, is measured like any other code.

Run ``python -m tools.check_source_length`` from the repository root. Exit 0 =
clean, 1 = a code file over the cap, 2 = could-not-check (a tracked code file
or a vendored file's record was unreadable, never reported as clean). Its
rules are unit-tested by ``python/tests/test_check_source_length.py``.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NewType

from tools._common import RelPath, TreeScan, git_ls_files, report_tree_scan
from tools._vendored import BlobSha, FileBytes, UnreadRecordError, blob_sha, recorded_blobs

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping

REPO = Path(__file__).resolve().parent.parent

LineCount = NewType("LineCount", int)

MAX_LINES = LineCount(1000)

_CODE_SUFFIXES = frozenset(
    {
        ".agda",
        ".c",
        ".cmake",
        ".cpp",
        ".fish",
        ".go",
        ".h",
        ".hpp",
        ".hs",
        ".hsc",
        ".py",
        ".pyi",
        ".rs",
        ".sh",
    }
)
_CODE_NAMES = frozenset({"CMakeLists.txt", "Dockerfile"})
_CODE_PREFIXES = ("Dockerfile.",)
_TEMPLATE_SUFFIX = ".in"


def is_code_file(rel: RelPath) -> bool:
    """Return True when tracked file ``rel`` is source a compiler or interpreter reads."""
    path = Path(rel)
    if path.suffix == _TEMPLATE_SUFFIX:
        path = path.with_suffix("")
    return (
        path.suffix in _CODE_SUFFIXES
        or path.name in _CODE_NAMES
        or path.name.startswith(_CODE_PREFIXES)
    )


def count_lines(data: FileBytes) -> LineCount:
    """Return the line count of ``data`` as ``wc -l`` reports it: one per newline."""
    return LineCount(data.count(b"\n"))


def finding(rel: RelPath, lines: LineCount) -> Prose | None:
    """Return the finding for a file of ``lines`` lines, or None when it is within the cap."""
    if lines <= MAX_LINES:
        return None
    return Prose(f"{rel}: {lines} lines, over {MAX_LINES}; split it along a seam it has")


def is_verbatim(rel: RelPath, data: FileBytes, verbatim: Mapping[RelPath, BlobSha]) -> bool:
    """Say whether ``rel``, holding ``data``, is a vendored file at its recorded blob sha."""
    return rel in verbatim and verbatim[rel] == blob_sha(data)


def check_tree(repo: Path = REPO) -> TreeScan:
    """Measure every tracked code file of ``repo`` against the cap, but a verbatim vendored one."""
    scan = TreeScan([], [])
    tracked = git_ls_files(repo)
    try:
        verbatim = recorded_blobs(repo, tracked)
    except UnreadRecordError as unread:
        scan.unreadable.append(str(unread))
        verbatim = {}
    for rel in tracked:
        if not is_code_file(rel):
            continue
        try:
            data = FileBytes((repo / rel).read_bytes())
        except OSError as exc:
            scan.unreadable.append(f"{rel}: {exc.strerror or exc}")
            continue
        if is_verbatim(rel, data, verbatim):
            continue
        found = finding(rel, count_lines(data))
        if found is not None:
            scan.findings.append(found)
    return scan


def main(*, repo: Path = REPO) -> ExitStatus:
    """Report every code file over the cap; 2 if a file was unreadable, 1 if any found."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    scan = check_tree(repo)
    return ExitStatus(
        report_tree_scan(
            "check_source_length",
            scan,
            found=f"{len(scan.findings)} code file(s) over {MAX_LINES} lines:",
            found_lines=scan.findings,
            clean=f"every tracked code file is within {MAX_LINES} lines.",
        )
    )


if __name__ == "__main__":
    sys.exit(main())

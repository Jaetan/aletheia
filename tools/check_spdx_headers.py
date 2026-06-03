#!/usr/bin/env python3
"""SPDX license-header gate for the Aletheia source tree.

Every source/build file must carry a two-line SPDX header::

    <comment> SPDX-FileCopyrightText: 2025 Nicolas Pelletier
    <comment> SPDX-License-Identifier: BSD-2-Clause

where ``<comment>`` is the file's native line-comment marker (``#`` for
Python/TOML/YAML/shell/CMake, ``//`` for C/C++/Go, ``--`` for Agda/Haskell/
Cabal).  The pair must be adjacent and in that order.

Scope is an *allowlist* of source/build/config extensions (see ``_EXT_COMMENT``
and ``_BASENAME_COMMENT``).  Everything else is excluded by construction:
documentation (``*.md``), archived review-finding data (``.archive/``),
files with no comment syntax (``*.json``), binaries (``*.xlsx``, ``*.bin``),
and generated artefacts (``go.sum``, ``*.snapshot``, Go ``*_string.go``,
anything carrying a ``DO NOT EDIT`` marker).

Placement respects each language's leading-line rules:

* a ``#!`` shebang stays on line 1; the header follows it,
* a Go build constraint (``//go:build`` / ``// +build``) stays first, followed
  by the conventional blank line, then the header,
* otherwise the header is the first thing in the file (for Agda this lands the
  ``--`` comments above the mandatory ``{-# OPTIONS #-}`` pragma, which keeps
  ``--safe`` fully in force -- verified empirically).

Usage::

    python -m tools.check_spdx_headers            # report-only (CI gate)
    python -m tools.check_spdx_headers --apply     # insert/repair headers

The ``--check`` definition of *compliant* is the single source of truth;
``--apply`` does exactly enough to satisfy it and is idempotent.
"""

from __future__ import annotations

import argparse
import re
import sys
from itertools import pairwise
from typing import TYPE_CHECKING

from tools._common import emit, find_executable, git_toplevel, run_capture

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path

COPYRIGHT_YEAR = "2025"
COPYRIGHT_HOLDER = "Nicolas Pelletier"
LICENSE_ID = "BSD-2-Clause"

_COPYRIGHT_BODY = f"SPDX-FileCopyrightText: {COPYRIGHT_YEAR} {COPYRIGHT_HOLDER}"
_LICENSE_BODY = f"SPDX-License-Identifier: {LICENSE_ID}"

_HASH = "#"
_SLASH = "//"
_DASH = "--"

# Allowlist: file extension -> native line-comment marker.  Membership here
# (or in _BASENAME_COMMENT) is what makes a file in scope for the gate.
_EXT_COMMENT: dict[str, str] = {
    ".agda": _DASH,
    ".agda-lib": _DASH,
    ".c": _SLASH,
    ".cabal": _DASH,
    ".cpp": _SLASH,
    ".go": _SLASH,
    ".h": _SLASH,
    ".hpp": _SLASH,
    ".hs": _DASH,
    ".py": _HASH,
    ".pyi": _HASH,
    ".sh": _HASH,
    ".toml": _HASH,
    ".yaml": _HASH,
    ".yml": _HASH,
}
_BASENAME_COMMENT: dict[str, str] = {"CMakeLists.txt": _HASH}

# Path prefixes (repo-relative) holding data records rather than source.
_EXCLUDED_PREFIXES: tuple[str, ...] = (".archive/",)

# Leading-line markers that must precede the header.
_GO_BUILD_MARKERS: tuple[str, ...] = ("//go:build", "// +build")

_HEADER_SCAN_LINES = 15  # how far down to look for an existing header pair
_GENERATED_SCAN_LINES = 3  # how far down to look for a "generated" marker


def _comment_style(path: Path) -> str | None:
    """Return the line-comment marker for ``path``, or None if out of scope."""
    by_ext = _EXT_COMMENT.get(path.suffix)
    if by_ext is not None:
        return by_ext
    return _BASENAME_COMMENT.get(path.name)


def _is_generated(path: Path, lines: list[str]) -> bool:
    """Return True for machine-generated files (a header would be clobbered)."""
    if path.name.endswith("_string.go"):
        return True
    head = "\n".join(lines[:_GENERATED_SCAN_LINES])
    return "DO NOT EDIT" in head or "Code generated" in head


def _header_pair(style: str) -> tuple[str, str]:
    """Return the (copyright, license) header lines for a comment ``style``."""
    return f"{style} {_COPYRIGHT_BODY}", f"{style} {_LICENSE_BODY}"


def _is_compliant(lines: list[str], style: str) -> bool:
    """Return True if the adjacent, ordered header pair is in the header region."""
    copyright_line, license_line = _header_pair(style)
    head = lines[:_HEADER_SCAN_LINES]
    return any(prev == copyright_line and cur == license_line for prev, cur in pairwise(head))


def _go_header_index(lines: list[str]) -> int:
    """Return where a fresh Go header goes: after any build-constraint block.

    Go build constraints must precede the ``package`` clause, so the header is
    inserted after the constraint line(s) and the single blank line that
    conventionally follows them.
    """
    constraint_end = 0
    for line in lines:
        if line.startswith(_GO_BUILD_MARKERS):
            constraint_end += 1
        else:
            break
    idx = constraint_end
    if constraint_end and idx < len(lines) and lines[idx] == "":
        idx += 1
    return idx


def _leading_skip(lines: list[str], suffix: str) -> int:
    """Return how many leading lines must stay above a fresh header.

    A ``#!`` shebang (line 1) and a Cabal ``cabal-version:`` field (which must
    be the literal first line for spec >= 2.2, ahead of any comment) cannot be
    displaced by the header.
    """
    if not lines:
        return 0
    if lines[0].startswith("#!"):
        return 1
    if suffix == ".cabal" and lines[0].startswith("cabal-version"):
        return 1
    return 0


def _apply_header(lines: list[str], style: str, suffix: str) -> list[str]:
    """Return ``lines`` rewritten to carry the compliant header pair.

    Handles the three real cases: an existing license line missing its
    copyright partner (the legacy one-line files -> insert the copyright line
    directly above it), the symmetric case, and a missing header entirely
    (insert a fresh adjacent block at the language-correct position).
    """
    copyright_line, license_line = _header_pair(style)
    head = lines[:_HEADER_SCAN_LINES]
    if license_line in head and copyright_line not in head:
        at = lines.index(license_line)
        return [*lines[:at], copyright_line, *lines[at:]]
    if copyright_line in head and license_line not in head:
        at = lines.index(copyright_line)
        return [*lines[: at + 1], license_line, *lines[at + 1 :]]
    if suffix == ".go":
        at = _go_header_index(lines)
        separator = [""] if at < len(lines) and lines[at] != "" else []
        return [*lines[:at], copyright_line, license_line, *separator, *lines[at:]]
    at = _leading_skip(lines, suffix)
    return [*lines[:at], copyright_line, license_line, *lines[at:]]


def _candidates(repo_root: Path) -> Iterator[tuple[Path, str]]:
    """Yield (path, comment-style) for every in-scope tracked file."""
    listed = run_capture(
        [find_executable("git"), "-C", str(repo_root), "ls-files"],
        check=True,
    )
    for rel in listed.stdout.splitlines():
        if any(rel.startswith(prefix) for prefix in _EXCLUDED_PREFIXES):
            continue
        path = repo_root / rel
        style = _comment_style(path)
        if style is not None:
            yield path, style


def _license_year_error(repo_root: Path) -> str | None:
    """Return an error string if LICENSE.md's year diverges from the header.

    The header copyright year must never drift from the project license; this
    couples the two so a future year bump touches both in the same change.
    """
    license_path = repo_root / "LICENSE.md"
    if not license_path.exists():
        return "LICENSE.md not found"
    match = re.search(r"Copyright\s+(\d{4})", license_path.read_text(encoding="utf-8"))
    if match is None:
        return "LICENSE.md has no 'Copyright <year>' line"
    if match.group(1) != COPYRIGHT_YEAR:
        return f"LICENSE.md year {match.group(1)} != header year {COPYRIGHT_YEAR}"
    return None


def main() -> int:
    """Check (or, with ``--apply``, repair) SPDX headers across the source tree."""
    parser = argparse.ArgumentParser(description="SPDX license-header gate.")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="insert or repair headers in place (default: report only)",
    )
    args = parser.parse_args()
    repo_root = git_toplevel()

    year_error = _license_year_error(repo_root)
    if year_error is not None:
        emit(f"SPDX: {year_error}")
        return 1

    offenders: list[Path] = []
    fixed: list[Path] = []
    for path, style in _candidates(repo_root):
        lines = path.read_text(encoding="utf-8").split("\n")
        if _is_generated(path, lines):
            continue
        if _is_compliant(lines, style):
            continue
        if args.apply:
            path.write_text("\n".join(_apply_header(lines, style, path.suffix)), encoding="utf-8")
            fixed.append(path)
        else:
            offenders.append(path)

    if args.apply:
        emit(f"SPDX: applied headers to {len(fixed)} file(s).")
        return 0
    if offenders:
        emit(f"SPDX: {len(offenders)} file(s) missing the header:")
        for path in offenders:
            emit(f"  {path.relative_to(repo_root)}")
        emit("Run: python -m tools.check_spdx_headers --apply")
        return 1
    emit("SPDX: all in-scope files carry the header.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

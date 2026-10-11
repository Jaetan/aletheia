# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_changelog.py — Enforce CHANGELOG entries on notable changes.

Offline enforcer for CHANGELOG discipline.  Invoked as a Shake phony
(``shake check-changelog``) and as a pre-push hook step.

Strategy: branch-level granularity.

1. Compute merge-base with the comparison ref (default ``main``).
2. List files changed between merge-base and HEAD.
3. If any *watched* path is changed, require ``CHANGELOG.md`` to be
   changed too.

Whatever the diff holds, the ``## [Unreleased]`` section carries each of its
``###`` category headers once: a second ``### Changed`` is where an entry
lands out of sight of the first, and merging the two by hand is what the
gate exists to make unnecessary.

Watched paths are the user-visible surface of each binding (public API)
PLUS the build system, CI, and tooling — the project convention is that
``CHANGELOG.md`` documents ALL notable changes wherever they appear, not
only public-symbol moves (user directive 2026-06-15).  Test files and
Markdown docs are excluded by the regex filter.

Exit codes:
  0 — no watched change, OR a watched change accompanied by a CHANGELOG.md edit.
  1 — a watched change without a CHANGELOG.md edit, no ``## [Unreleased]``
      section, a category header repeated under it, or a header there that is
      not a Keep-a-Changelog category.
  2 — usage error / git failure / a CHANGELOG.md that cannot be read as UTF-8.

v0 limitations (deliberate; see PROJECT_STATUS.md for v1+ plan):
  * Presence-of-CHANGELOG-modification is sufficient; the script does NOT
    verify the change appears under ``## [Unreleased]``.
  * Branch-level (not per-commit); a branch with one CHANGELOG commit
    covers any number of notable commits on the same branch.
  * Path-based; an internal refactor under a watched dir that changes no
    observable surface still triggers the gate.  Workaround: add a CHANGELOG
    entry under ``### Changed`` noting "internal — no behavior change".
"""

from __future__ import annotations

import argparse
import re
import sys
from enum import StrEnum
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

from tools._common import RelPath, emit, find_executable, run_capture
from tools._markdown import headings, sections

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Iterable

DESCRIPTION = "Enforce CHANGELOG entries on notable (public-API + build/CI/tooling) changes."

GIT_FAILURE_EXIT = 2

# Public-API surface of each binding.
API_PATTERNS = [
    re.compile(r"^python/aletheia/"),
    re.compile(r"^go/aletheia/[^/]+\.go$"),
    re.compile(r"^cpp/include/aletheia/"),
    re.compile(r"^rust/src/"),
    re.compile(r"^haskell-shim/ffi-exports\.snapshot$"),
]

# Build system, CI, and tooling.  Not the public-API surface, but the project
# convention is that CHANGELOG.md documents ALL notable changes (user directive
# 2026-06-15) — a substantial build/CI/tooling change is notable even when no
# public symbol moved.  Agda sources (``src/``) are deliberately absent: a
# behavioral src/ change reaches users through the bindings (already watched
# above), and most src/ edits are proof-internal.
INFRA_PATTERNS = [
    re.compile(r"^Shakefile\.hs$"),
    re.compile(r"^shake\.cabal$"),
    re.compile(r"^aletheia\.agda-lib$"),
    re.compile(r"^haskell-shim/"),
    re.compile(r"^tools/"),
    re.compile(r"^\.github/workflows/"),
]

WATCHED_PATTERNS = [*API_PATTERNS, *INFRA_PATTERNS]

# Paths that never require a CHANGELOG entry, even under a watched dir: test
# files (their behavior is covered by what they test) and Markdown docs (.md is
# always documentation, never a notable code change — CHANGELOG.md is itself .md
# and handled separately below).
TEST_EXCLUSIONS = re.compile(r"_test\.go$|/tests?/|^python/aletheia/.*/test_|^cpp/tests/")
DOC_EXCLUSIONS = re.compile(r"\.md$")

CHANGELOG_RE = re.compile(r"^CHANGELOG\.md$")
# The level of a category header under a release, ``###``.
_CATEGORY_LEVEL = 3
UNRELEASED_HEADER = "## [Unreleased]"


class Category(StrEnum):
    """The six Keep-a-Changelog categories, the only words a ``###`` header may carry."""

    ADDED = "Added"
    CHANGED = "Changed"
    DEPRECATED = "Deprecated"
    REMOVED = "Removed"
    FIXED = "Fixed"
    SECURITY = "Security"


class UnreleasedHeaders(NamedTuple):
    """What the ``## [Unreleased]`` section's ``###`` headers say about themselves.

    ``repeated`` names each category that heads two blocks, once, in the order
    its second block appears; ``unknown`` is every header that is not a category,
    as it reads; ``missing`` is whether the changelog has no ``## [Unreleased]``
    section at all.  Both lists empty and a section found is what the gate wants.
    """

    repeated: list[Category]
    unknown: list[str]
    missing: bool = False


def unreleased_headers(changelog: str) -> UnreleasedHeaders:
    """Audit the ``###`` headers under ``## [Unreleased]``.

    The changelog is read as CommonMark (``tools._markdown``): each section a
    top-level ``## [Unreleased]`` opens runs to the next top-level heading of level
    two or shallower, every such section is read, and a header is a top-level
    level-three heading inside one, whose category is the whole of what it
    renders, trimmed.  A heading-shaped line in code is neither.
    """
    seen: set[Category] = set()
    repeated: list[Category] = []
    unknown: list[str] = []
    text = Prose(changelog)
    unreleased = sections(text, Prose(UNRELEASED_HEADER))
    if not unreleased:
        return UnreleasedHeaders(repeated, unknown, missing=True)
    for heading in headings(text):
        if heading.level != _CATEGORY_LEVEL or heading.nested:
            continue
        if not any(found.first <= heading.line < found.end for found in unreleased):
            continue
        word = heading.text.strip()
        try:
            category = Category(word)
        except ValueError:
            unknown.append(word)
            continue
        if category in seen and category not in repeated:
            repeated.append(category)
        seen.add(category)
    return UnreleasedHeaders(repeated, unknown)


def watched_files(changed_files: Iterable[RelPath]) -> list[RelPath]:
    """Return the changed files that require a CHANGELOG entry (watched, non-test/doc)."""
    return [
        f
        for f in changed_files
        if not (TEST_EXCLUSIONS.search(f) or DOC_EXCLUSIONS.search(f))
        and any(p.search(f) for p in WATCHED_PATTERNS)
    ]


def _git(*args: str) -> str:
    out = run_capture([find_executable("git"), *args])
    if out.returncode != 0:
        _ = sys.stderr.write(f"check-changelog: git {' '.join(args)} failed\n")
        _ = sys.stderr.write(out.stderr)
        sys.exit(GIT_FAILURE_EXIT)
    return out.stdout


def _changed_files(base: str) -> list[RelPath] | None:
    """List the files changed since the merge-base with ``base``, or None when git cannot say."""
    verify = run_capture([find_executable("git"), "rev-parse", "--verify", base])
    if verify.returncode != 0:
        _ = sys.stderr.write(f"check-changelog: comparison ref '{base}' not found\n")
        return None
    merge_base = _git("merge-base", "HEAD", base).strip()
    if not merge_base:
        _ = sys.stderr.write(f"check-changelog: failed to compute merge-base with '{base}'\n")
        return None
    changed_text = _git("diff", "--name-only", f"{merge_base}..HEAD")
    return [RelPath(line) for line in changed_text.splitlines() if line]


def headers_refused(headers: UnreleasedHeaders) -> bool:
    """Write the refusal for a missing section or a repeated or unknown header; say if one was."""
    if headers.missing:
        _ = sys.stderr.write(
            f"check-changelog: FAIL — CHANGELOG.md has no '{UNRELEASED_HEADER}' section.\n"
        )
        return True
    if headers.repeated:
        named = ", ".join(f"### {category}" for category in headers.repeated)
        _ = sys.stderr.write(
            "check-changelog: FAIL — a category header appears more than once under "
            + f"'{UNRELEASED_HEADER}': {named}.\nMerge its entries under the first header.\n"
        )
        return True
    if headers.unknown:
        named = ", ".join(f"### {word}" for word in headers.unknown)
        allowed = ", ".join(category.value for category in Category)
        _ = sys.stderr.write(
            f"check-changelog: FAIL — a header under '{UNRELEASED_HEADER}' is not a "
            + f"Keep-a-Changelog category: {named}.\nThe categories are {allowed}.\n"
        )
        return True
    return False


def _changelog_refused(toplevel: Path) -> ExitStatus | None:
    """Audit the CHANGELOG.md under ``toplevel``; return the exit status refusing it, or None.

    A file that cannot be read as UTF-8 is 2, a refused ``[Unreleased]`` section 1.
    """
    changelog = toplevel / "CHANGELOG.md"
    try:
        text = str(changelog.read_bytes(), "utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        _ = sys.stderr.write(f"check-changelog: FAIL — {changelog} cannot be read: {exc}\n")
        return ExitStatus(GIT_FAILURE_EXIT)
    return ExitStatus(1) if headers_refused(unreleased_headers(text)) else None


def main() -> int:
    """Fail on a refused ``[Unreleased]`` section or a watched path changed without an entry."""
    ap = argparse.ArgumentParser(description=DESCRIPTION)
    ap.add_argument(
        "base",
        nargs="?",
        default="main",
        help="comparison ref (default: main)",
    )
    args = ap.parse_args()

    refused = _changelog_refused(Path(_git("rev-parse", "--show-toplevel").strip()))
    if refused is not None:
        return refused

    changed_files = _changed_files(args.base)
    if changed_files is None:
        return GIT_FAILURE_EXIT

    if not changed_files:
        emit(f"check-changelog: ok (no changes since merge-base with {args.base})")
        return 0

    watched = watched_files(changed_files)

    if not watched:
        emit(f"check-changelog: ok (no notable changes since merge-base with {args.base})")
        return 0

    if any(CHANGELOG_RE.match(f) for f in changed_files):
        emit("check-changelog: ok (notable changes accompanied by CHANGELOG.md edit)")
        return 0

    _ = sys.stderr.write(
        "check-changelog: FAIL — notable changes detected without a "
        + "CHANGELOG.md entry.\n\n"
        + "Changed files requiring a CHANGELOG entry:\n"
    )
    for f in watched:
        _ = sys.stderr.write(f"  {f}\n")
    _ = sys.stderr.write(
        "\n"
        + "Required: add an entry to CHANGELOG.md under '## [Unreleased]' "
        + "before merging.  Use one of:\n\n"
        + "  ### Added       — new public/user-visible surface\n"
        + "  ### Changed     — modified existing surface (incl. BREAKING)\n"
        + "  ### Removed     — dropped surface\n"
        + "  ### Fixed       — behavior fix on existing surface\n\n"
        + "If the diff has no observable behavior change (an internal refactor, a\n"
        + "build/CI/tooling tweak, or a dependency bump), add a one-line note under\n"
        + '"### Changed" saying so (e.g. "internal — no behavior change") so the\n'
        + "reviewer can verify by inspection.  This is the escape hatch for routine\n"
        + "infra edits and bot dependency bumps.\n\n"
        + "Reference: CHANGELOG discipline (AGENTS.md § Universal Rules).\n"
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())

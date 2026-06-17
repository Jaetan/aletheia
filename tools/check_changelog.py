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

Watched paths are the user-visible surface of each binding (public API)
PLUS the build system, CI, and tooling — the project convention is that
``CHANGELOG.md`` documents ALL notable changes wherever they appear, not
only public-symbol moves (user directive 2026-06-15).  Test files and
Markdown docs are excluded by the regex filter.

Exit codes:
  0 — no watched change, OR a watched change accompanied by a CHANGELOG.md edit.
  1 — a watched change without a CHANGELOG.md edit.
  2 — usage error / git failure.

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
from typing import TYPE_CHECKING

from tools._common import emit, find_executable, run_capture

if TYPE_CHECKING:
    from collections.abc import Iterable

DESCRIPTION = "Enforce CHANGELOG entries on notable (public-API + build/CI/tooling) changes."

GIT_FAILURE_EXIT = 2

# Public-API surface of each binding.
API_PATTERNS = [
    re.compile(r"^python/aletheia/"),
    re.compile(r"^go/aletheia/[^/]+\.go$"),
    re.compile(r"^cpp/include/aletheia/"),
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


def watched_files(changed_files: Iterable[str]) -> list[str]:
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


def main() -> int:
    """Fail when a watched path changed without a matching CHANGELOG.md edit."""
    ap = argparse.ArgumentParser(description=DESCRIPTION)
    ap.add_argument(
        "base",
        nargs="?",
        default="main",
        help="comparison ref (default: main)",
    )
    args = ap.parse_args()

    verify = run_capture(
        [find_executable("git"), "rev-parse", "--verify", args.base],
    )
    if verify.returncode != 0:
        _ = sys.stderr.write(f"check-changelog: comparison ref '{args.base}' not found\n")
        return GIT_FAILURE_EXIT

    merge_base = _git("merge-base", "HEAD", args.base).strip()
    if not merge_base:
        _ = sys.stderr.write(f"check-changelog: failed to compute merge-base with '{args.base}'\n")
        return GIT_FAILURE_EXIT

    changed_text = _git("diff", "--name-only", f"{merge_base}..HEAD")
    changed_files = [line for line in changed_text.splitlines() if line]

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

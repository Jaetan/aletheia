#!/usr/bin/env python3
"""tools/check_changelog.py — Enforce CHANGELOG entries on public-API changes.

Offline enforcer for Public API stability and CHANGELOG discipline.
Invoked as a Shake phony (``shake check-changelog``) and as a pre-push
hook step.

Strategy: branch-level granularity.

1. Compute merge-base with the comparison ref (default ``main``).
2. List files changed between merge-base and HEAD.
3. If any public-API path is changed, require ``CHANGELOG.md`` to be
   changed too.

Public-API paths are the user-visible surface of each binding.  Test
files and lowercase-private Go identifiers are excluded by the regex
filter.

Exit codes:
  0 — public-API unchanged, OR public-API changed and CHANGELOG.md changed.
  1 — public-API changed but CHANGELOG.md not changed.
  2 — usage error / git failure.

v0 limitations (deliberate; see PROJECT_STATUS.md for v1+ plan):
  * Presence-of-CHANGELOG-modification is sufficient; the script does NOT
    verify the change appears under ``## [X.Y.Z] — Unreleased``.
  * Branch-level (not per-commit); a branch with one CHANGELOG commit
    covers any number of public-API commits on the same branch.
  * Path-based; refactors of internal ``_helpers.py`` that don't change
    surface still trigger the gate.  Workaround: add a CHANGELOG entry
    under ``### Changed`` describing the internal refactor.
"""

from __future__ import annotations

import argparse
import re
import sys

from tools._common import emit, find_executable, run_capture

DESCRIPTION = "Enforce CHANGELOG entries on public-API changes."

GIT_FAILURE_EXIT = 2

API_PATTERNS = [
    re.compile(r"^python/aletheia/"),
    re.compile(r"^go/aletheia/[^/]+\.go$"),
    re.compile(r"^cpp/include/aletheia/"),
    re.compile(r"^haskell-shim/ffi-exports\.snapshot$"),
]

TEST_EXCLUSIONS = re.compile(r"_test\.go$|/tests/|^python/aletheia/.*/test_|^cpp/tests/")

CHANGELOG_RE = re.compile(r"^CHANGELOG\.md$")


def _git(*args: str) -> str:
    out = run_capture([find_executable("git"), *args])
    if out.returncode != 0:
        _ = sys.stderr.write(f"check-changelog: git {' '.join(args)} failed\n")
        _ = sys.stderr.write(out.stderr)
        sys.exit(GIT_FAILURE_EXIT)
    return out.stdout


def main() -> int:
    """Fail when public-API files changed without a matching CHANGELOG.md edit."""
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

    api_changed: list[str] = []
    for f in changed_files:
        if TEST_EXCLUSIONS.search(f):
            continue
        if any(p.search(f) for p in API_PATTERNS):
            api_changed.append(f)

    if not api_changed:
        emit(f"check-changelog: ok (no public-API changes since merge-base with {args.base})")
        return 0

    if any(CHANGELOG_RE.match(f) for f in changed_files):
        emit("check-changelog: ok (public-API changes accompanied by CHANGELOG.md edit)")
        return 0

    _ = sys.stderr.write(
        "check-changelog: FAIL — public-API changes detected without a "
        + "CHANGELOG.md entry.\n\n"
        + "Changed public-API files:\n"
    )
    for f in api_changed:
        _ = sys.stderr.write(f"  {f}\n")
    _ = sys.stderr.write(
        "\n"
        + "Required: add an entry to CHANGELOG.md under '## [X.Y.Z] — Unreleased' "
        + "before merging.  Use one of:\n\n"
        + "  ### Added       — new public surface\n"
        + "  ### Changed     — modified existing surface (incl. BREAKING)\n"
        + "  ### Removed     — dropped surface\n"
        + "  ### Fixed       — behavior fix on existing surface\n\n"
        + "If the diff is an internal-only refactor (no observable surface change),\n"
        + "add a note under '### Changed' explaining \"internal refactor — no behavior\n"
        + 'change" so reviewers can verify by inspection.\n\n'
        + "Reference: Public API stability and CHANGELOG discipline.\n"
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())

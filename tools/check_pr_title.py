# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_pr_title.py — Hold a pull request's title to the commit-subject vocabulary.

The title is the subject the squash commit lands with on the comparison ref, so
it reads ``type(scope)!: text`` in the closed vocabulary of
``tools/commit_subjects.py``; it names a shipped scope, or none, when the branch
changes what users get; and the branch edits ``CHANGELOG.md`` exactly when that
module's table says the title owes it an entry, the release preparation apart
(``cuts_a_release``).  The branch's own commits and the CHANGELOG's shape are
``tools/check_changelog.py``'s.

The workflow ``.github/workflows/pr-title.yml`` runs it on every title edit and
every push to a pull request, on a bare interpreter: nothing it imports needs a
package beyond the standard library and the project's own.

Exit codes:
  0 — the title reads in the vocabulary, its label fits the branch's files, and
      the branch edits the CHANGELOG exactly when the title owes it an entry,
      the release preparation apart.
  1 — the vocabulary refuses the title, it names an internal scope on a branch
      that changes what users get, it owes an entry the branch leaves out, or
      it owes none, cuts no release, and the branch edits the CHANGELOG.
  2 — git cannot answer (no comparison ref, no merge-base, no top level), or the
      runtime-closure snapshot cannot be read as UTF-8.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from tools._common import RelPath, emit
from tools.commit_subjects import (
    RUNTIME_CLOSURE,
    Branch,
    Refusal,
    Revision,
    Subject,
    cuts_a_release,
    kernel_sources,
    mislabelled,
    owed_entry,
    parse,
    read_branch,
    toplevel,
)

from aletheia.common_types import ExitStatus, Prose

DESCRIPTION = (
    "Hold a pull request's title to the commit-subject vocabulary, the files its branch "
    + "changes, and the CHANGELOG entry it owes or does not."
)
TOOL = Prose("check-pr-title")
CHANGELOG = RelPath("CHANGELOG.md")
COULD_NOT_CHECK = ExitStatus(2)


def _kernel() -> frozenset[RelPath] | None:
    """Read the kernel's shipped sources from the runtime-closure snapshot, or None and why not."""
    top = toplevel(TOOL)
    if top is None:
        return None
    snapshot = Path(top) / RUNTIME_CLOSURE
    try:
        return kernel_sources(Prose(str(snapshot.read_bytes(), "utf-8")))
    except (OSError, UnicodeDecodeError) as exc:
        _ = sys.stderr.write(f"check-pr-title: FAIL — {snapshot} cannot be read: {exc}\n")
        return None


def verdict(title: Prose, read: Subject, branch: Branch, kernel: frozenset[RelPath]) -> ExitStatus:
    """Judge an accepted title against its branch: its label against the files, then the entry."""
    shipped = mislabelled(branch.changed, kernel, [read])
    if shipped:
        _ = sys.stderr.write(
            f"check-pr-title: FAIL — {title!r} names an internal scope, and the branch "
            + f"changes what users get: {', '.join(shipped)}.\n"
        )
        return ExitStatus(1)
    where = owed_entry(read)
    if where is None and CHANGELOG in branch.changed:
        if cuts_a_release(read):
            emit(f"check-pr-title: ok ({title!r} cuts a release; the branch edits CHANGELOG.md)")
            return ExitStatus(0)
        _ = sys.stderr.write(
            f"check-pr-title: FAIL — {title!r} owes no entry, and the branch edits "
            + "CHANGELOG.md.\nRelabel the change, or leave CHANGELOG.md alone.\n"
        )
        return ExitStatus(1)
    if where is None:
        emit(f"check-pr-title: ok ({title!r} reads in the vocabulary and owes no entry)")
        return ExitStatus(0)
    if CHANGELOG not in branch.changed:
        _ = sys.stderr.write(
            f"check-pr-title: FAIL — {title!r} owes {where}, and the branch leaves "
            + "CHANGELOG.md alone.\n"
        )
        return ExitStatus(1)
    emit(f"check-pr-title: ok ({title!r} owes {where}; the branch edits CHANGELOG.md)")
    return ExitStatus(0)


def main() -> ExitStatus:
    """Fail on a title the vocabulary refuses, mislabels the branch, or owes an absent entry."""
    ap = argparse.ArgumentParser(description=DESCRIPTION)
    _ = ap.add_argument("title", help="the pull request's title")
    _ = ap.add_argument("base", nargs="?", default="main", help="comparison ref (default: main)")
    arguments = ap.parse_args()
    title = Prose(str(arguments.title))
    base = Revision(str(arguments.base))

    read = parse(title)
    if isinstance(read, Refusal):
        _ = sys.stderr.write(f"check-pr-title: FAIL — {title!r}: {read.reason}.\n")
        return ExitStatus(1)
    kernel = _kernel()
    if kernel is None:
        return COULD_NOT_CHECK
    branch = read_branch(TOOL, base)
    if branch is None:
        return COULD_NOT_CHECK
    return verdict(title, read, branch, kernel)


if __name__ == "__main__":
    sys.exit(main())

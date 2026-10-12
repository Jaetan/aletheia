# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_changelog.py — Hold a branch's subjects to the vocabulary, and the CHANGELOG to them.

The changelog has one entry per significant change and none for internal work
(AGENTS.md § Universal Rules).  Comparing the branch with the merge-base of a
comparison ref (default ``main``), this gate holds these:

* every commit subject on the branch reads ``type(scope)!: text`` in the closed
  vocabulary of ``tools/commit_subjects.py``, merge commits aside;
* a branch that changes what users get carries a subject naming a shipped
  scope, or none, not internal ones alone (that module's ``mislabelled``, which
  reads the kernel's shipped modules from ``haskell-shim/runtime-closure.snapshot``);
* a branch whose subjects owe an entry by that module's table, or that changes
  a record of the public surface (``SURFACE_RECORDS``: the feature matrix,
  which the parity tests hold every binding's listed symbols to; the C ABI's
  export snapshot; the wire codes and the log events, names consumers match
  on), edits ``CHANGELOG.md``;
* a branch that owes no entry leaves ``CHANGELOG.md`` alone, the release
  preparation apart (that module's ``cuts_a_release``): the changelog records
  what users get, and an entry under a subject that owes none is where internal
  work leaks into it;
* the ``## [Unreleased]`` section carries each of its ``###`` category headers
  once, and every one is a Keep-a-Changelog category: a second
  ``### Changed`` is where an entry lands out of sight of the first.

The pull request's title, which its squash commit lands with, is held to the
same vocabulary and table by ``tools/check_pr_title.py``.  This gate is the
Shake phony ``check-changelog``, which ``tools/run_ci.py`` runs.

Exit codes:
  0 — the subjects read in the vocabulary, the branch owes no entry or carries
      one, and the section is sound.
  1 — a subject the vocabulary refuses, shipped files under internal labels
      alone, a branch that owes an entry and leaves ``CHANGELOG.md`` alone, one
      that edits it owing none and cutting no release, no ``## [Unreleased]``
      section, a category header repeated under it, or a header there that is
      not a category.
  2 — git cannot answer (no comparison ref, no merge-base, no top level), or
      ``CHANGELOG.md`` or the runtime-closure snapshot cannot be read as UTF-8.
"""

from __future__ import annotations

import argparse
import sys
from enum import StrEnum
from pathlib import Path
from typing import NamedTuple

from tools._common import RelPath, emit
from tools._markdown import headings, sections
from tools.commit_subjects import (
    RUNTIME_CLOSURE,
    SHIPPED_SCOPES,
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
    "Hold a branch's commit subjects to the vocabulary, require the CHANGELOG entry they or a "
    + "public-surface record owe and refuse one nothing owes, and hold [Unreleased] to one "
    + "header per category."
)
TOOL = Prose("check-changelog")

COULD_NOT_CHECK = ExitStatus(2)

# The records of the public surface, each moved by a change a consumer sees.
SURFACE_RECORDS = frozenset(
    {
        RelPath("docs/FEATURE_MATRIX.yaml"),
        RelPath("haskell-shim/ffi-exports.snapshot"),
        RelPath("docs/WIRE_CODES.yaml"),
        RelPath("docs/LOG_EVENTS.yaml"),
    }
)
CHANGELOG = RelPath("CHANGELOG.md")

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


class OwedSubject(NamedTuple):
    """A subject that owes the changelog an entry, and where the entry goes."""

    subject: Prose
    where: Prose


class Owed(NamedTuple):
    """Why a branch owes an entry: the surface records it changed, the subjects that owe one.

    Both empty is a branch that owes nothing.
    """

    records: list[RelPath]
    subjects: list[OwedSubject]


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


def owed(branch: Branch) -> Owed:
    """Say why the branch owes an entry: the surface records it changed, the subjects owing one.

    A subject the vocabulary refuses owes nothing here; ``subjects_refused`` names it.
    """
    subjects: list[OwedSubject] = []
    for subject in branch.subjects:
        read = parse(subject)
        if isinstance(read, Refusal):
            continue
        where = owed_entry(read)
        if where is not None:
            subjects.append(OwedSubject(subject, where))
    return Owed([path for path in branch.changed if path in SURFACE_RECORDS], subjects)


def subjects_refused(branch: Branch) -> bool:
    """Write the refusal for each subject the vocabulary refuses; say if one was."""
    refused = False
    for subject in branch.subjects:
        read = parse(subject)
        if isinstance(read, Refusal):
            _ = sys.stderr.write(f"check-changelog: FAIL — {subject!r}: {read.reason}.\n")
            refused = True
    return refused


def labels_refused(branch: Branch, kernel: frozenset[RelPath]) -> bool:
    """Write the refusal for shipped files under internal labels alone; say if there were."""
    labels = [read for read in map(parse, branch.subjects) if isinstance(read, Subject)]
    shipped = mislabelled(branch.changed, kernel, labels)
    if not shipped:
        return False
    named = ", ".join(sorted(scope.value for scope in SHIPPED_SCOPES))
    lines = [
        "check-changelog: FAIL — the branch changes what users get, and every subject "
        + "names an internal scope:",
        *(f"  {path}" for path in shipped),
        f"Name the shipped scope the change is in: {named}.",
    ]
    _ = sys.stderr.write("\n".join(lines) + "\n")
    return True


def read_text(path: Path) -> Prose | None:
    """Read a file the gate needs as UTF-8, or write why it cannot and give None."""
    try:
        return Prose(str(path.read_bytes(), "utf-8"))
    except (OSError, UnicodeDecodeError) as exc:
        _ = sys.stderr.write(f"check-changelog: FAIL — {path} cannot be read: {exc}\n")
        return None


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


def entry_refused(branch: Branch) -> bool:
    """Write the refusal for a branch that owes an entry and has none; say if one was."""
    reasons = owed(branch)
    if not (reasons.records or reasons.subjects) or CHANGELOG in branch.changed:
        return False
    lines = [
        "check-changelog: FAIL — the branch owes CHANGELOG.md an entry and leaves it alone.",
        *(f"  changes the public-surface record {path}" for path in reasons.records),
        *(f"  {owing.subject}: owes {owing.where}" for owing in reasons.subjects),
        "Add one entry under '## [Unreleased]': a bold lead and one line, two at most,",
        "however intricate the change; the detail belongs to the commit message.",
    ]
    _ = sys.stderr.write("\n".join(lines) + "\n")
    return True


def unowed_edit_refused(branch: Branch) -> bool:
    """Write the refusal for a branch that edits the CHANGELOG owing it nothing; say if one was."""
    if CHANGELOG not in branch.changed:
        return False
    reasons = owed(branch)
    subjects = [read for read in map(parse, branch.subjects) if isinstance(read, Subject)]
    if reasons.records or reasons.subjects or any(map(cuts_a_release, subjects)):
        return False
    lines = [
        "check-changelog: FAIL — the branch edits CHANGELOG.md, and no subject owes it an entry:",
        *(f"  {subject}" for subject in branch.subjects),
        "An entry is owed by a feat, fix or perf on a shipped scope, a breaking mark, or a",
        "changed public-surface record; relabel the change, or leave CHANGELOG.md alone.",
    ]
    _ = sys.stderr.write("\n".join(lines) + "\n")
    return True


def main() -> ExitStatus:
    """Fail on a refused subject or label, an entry owed or unowed, or a refused section."""
    ap = argparse.ArgumentParser(description=DESCRIPTION)
    _ = ap.add_argument("base", nargs="?", default="main", help="comparison ref (default: main)")
    base = Revision(str(ap.parse_args().base))

    top = toplevel(TOOL)
    if top is None:
        return COULD_NOT_CHECK
    text = read_text(Path(top) / CHANGELOG)
    snapshot = read_text(Path(top) / RUNTIME_CLOSURE)
    if text is None or snapshot is None:
        return COULD_NOT_CHECK
    if headers_refused(unreleased_headers(text)):
        return ExitStatus(1)

    branch = read_branch(TOOL, base)
    if branch is None:
        return COULD_NOT_CHECK
    refused = [
        subjects_refused(branch),
        labels_refused(branch, kernel_sources(snapshot)),
        entry_refused(branch),
        unowed_edit_refused(branch),
    ]
    if any(refused):
        return ExitStatus(1)
    emit(
        f"check-changelog: ok (the subjects since {base} read in the vocabulary, "
        + "and CHANGELOG.md is edited exactly when they owe it an entry, the release "
        + "preparation apart)"
    )
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())

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
  on; the C++ layout record, which every program linked against the shared
  library is rebuilt for), edits ``CHANGELOG.md``;
* a branch that owes no entry leaves ``CHANGELOG.md`` alone, the release
  preparation apart (that module's ``cuts_a_release``): the changelog records
  what users get, and an entry under a subject that owes none is where internal
  work leaks into it;
* the ``## [Unreleased]`` section carries each of its ``###`` category headers
  once, and every one is a Keep-a-Changelog category: a second
  ``### Changed`` is where an entry lands out of sight of the first;
* a branch whose commits prepare a release (that module's ``released``) carries
  its cut from the merge-base, as ``docs/development/RELEASE.md`` makes it
  (``cut_problem``): the base's ``## [Unreleased]`` lines, in their order, under
  ``## [X.Y.Z] — YYYY-MM-DD`` for that version and a calendar date, below an empty
  ``## [Unreleased]``, no other line changed, and the version newer than every
  release the base holds; a branch preparing two versions is refused.

The pull request's title, which its squash commit lands with, is held to the
same vocabulary and table by ``tools/check_pr_title.py``.  This gate is the
Shake phony ``check-changelog``, which ``tools/run_ci.py`` runs.

Exit codes:
  0 — the subjects read in the vocabulary, the branch owes no entry or carries
      one, the section is sound, and a release the branch prepares is cut.
  1 — a subject the vocabulary refuses, shipped files under internal labels
      alone, a branch that owes an entry and leaves ``CHANGELOG.md`` alone, one
      that edits it owing none and cutting no release, no ``## [Unreleased]``
      section, a category header repeated under it, a header there that is
      not a category, a release the CHANGELOG does not cut from its base, or two
      releases.
  2 — git cannot answer (no comparison ref, no merge-base, no top level), or
      ``CHANGELOG.md`` or the runtime-closure snapshot cannot be read as UTF-8, or,
      on a branch preparing a release, the merge-base's ``CHANGELOG.md`` cannot.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from datetime import date
from enum import StrEnum
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, NewType

from tools._common import RelPath, emit, find_executable
from tools._markdown import headings, sections
from tools._markdown import lines as commonmark_lines
from tools.commit_subjects import (
    RUNTIME_CLOSURE,
    SHIPPED_SCOPES,
    VERSION_PATTERN,
    Branch,
    Refusal,
    ReleaseVersion,
    Revision,
    Subject,
    cuts_a_release,
    kernel_sources,
    mislabelled,
    owed_entry,
    parse,
    read_branch,
    released,
    toplevel,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from tools._markdown import Section

DESCRIPTION = (
    "Hold a branch's commit subjects to the vocabulary, require the CHANGELOG entry they or a "
    + "public-surface record owe and refuse one nothing owes, hold [Unreleased] to one "
    + "header per category, and hold a release preparation to its cut."
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
        RelPath("docs/CPP_LAYOUT.yaml"),
    }
)
CHANGELOG = RelPath("CHANGELOG.md")

# The level of a category header under a release, ``###``, and of a release's own.
_CATEGORY_LEVEL = 3
_RELEASE_LEVEL = 2
UNRELEASED_HEADER = "## [Unreleased]"
# A release's heading as docs/development/RELEASE.md writes it: the version in
# brackets, an em dash, and the date of the cut.
_RELEASE_HEADING = re.compile(
    rf"\[(?P<version>{VERSION_PATTERN})\] — (?P<date>[0-9]{{4}}-[0-9]{{2}}-[0-9]{{2}})"
)
# What opens any release's heading, however the rest of it reads.
_RELEASE_OPENING = re.compile(rf"\[(?P<version>{VERSION_PATTERN})\]")
# A blank line as CommonMark reads one: spaces and tabs at most.
_BLANK = " \t"
# One of a version's three numbers.
VersionNumber = NewType("VersionNumber", int)


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


class VersionKey(NamedTuple):
    """A version as SemVer orders it: by major, then minor, then patch."""

    major: VersionNumber
    minor: VersionNumber
    patch: VersionNumber


class CutProblem(NamedTuple):
    """How a CHANGELOG falls short of a release's cut, and what fixes it."""

    found: Prose
    fix: Prose


class _Cut(NamedTuple):
    """The fresh ``## [Unreleased]`` section and the release section under it."""

    unreleased: Section
    release: Section


def _cut_fix(version: ReleaseVersion) -> Prose:
    """Say how docs/development/RELEASE.md cuts ``version``."""
    return Prose(
        "Cut it as docs/development/RELEASE.md says: the entries move under "
        + f"'## [{version}] — YYYY-MM-DD', below an empty '{UNRELEASED_HEADER}', and nothing "
        + "else changes."
    )


def _key(version: ReleaseVersion) -> VersionKey:
    """Order versions as SemVer does, number by number."""
    major, minor, patch = (VersionNumber(int(number)) for number in version.split("."))
    return VersionKey(major, minor, patch)


def _releases(text: Prose) -> list[ReleaseVersion]:
    """Return the version every top-level release heading of the text opens with."""
    found: list[ReleaseVersion] = []
    for heading in headings(text):
        matched = _RELEASE_OPENING.match(heading.source)
        if heading.level == _RELEASE_LEVEL and not heading.nested and matched is not None:
            found.append(ReleaseVersion(matched["version"]))
    return found


def _cut_shape(changelog: Prose, version: ReleaseVersion) -> _Cut | Prose:
    """Find the fresh section and the release under it, or say how the shape differs."""
    unreleased = sections(changelog, Prose(UNRELEASED_HEADER))
    if len(unreleased) != 1:
        return Prose(f"has {len(unreleased)} '{UNRELEASED_HEADER}' sections, not one")
    section = unreleased[0]
    if any(
        line.strip(_BLANK)
        for line in commonmark_lines(changelog)[section.first - 1 : section.end - 1]
    ):
        return Prose(f"is not empty under '{UNRELEASED_HEADER}'")
    wanted = f"'## [{version}] — YYYY-MM-DD'"
    following = [
        heading
        for heading in headings(changelog)
        if heading.line == section.end and heading.level == _RELEASE_LEVEL
    ]
    if not following:
        return Prose(f"has no {wanted} heading after '{UNRELEASED_HEADER}'")
    written = following[0].source
    matched = _RELEASE_HEADING.fullmatch(written)
    if matched is None or matched["version"] != version:
        return Prose(f"heads the section after '{UNRELEASED_HEADER}' {written!r}, not {wanted}")
    try:
        _ = date.fromisoformat(matched["date"])
    except ValueError:
        return Prose(f"dates release {version} {matched['date']!r}, which is not a calendar date")
    release = [
        found
        for found in sections(changelog, Prose(f"## {written}"))
        if found.heading.line == section.end
    ]
    return _Cut(section, release[0])


def cut_problem(changelog: Prose, base: Prose, version: ReleaseVersion) -> CutProblem | None:
    """Say how the CHANGELOG falls short of cutting ``version`` from ``base``, or None.

    The cut is docs/development/RELEASE.md's: the base's one ``## [Unreleased]``
    section renamed ``## [X.Y.Z] — YYYY-MM-DD``, for the version and a calendar
    date, under a fresh ``## [Unreleased]`` whose lines hold only spaces and tabs.
    Against the base, the release section holds the lines its ``[Unreleased]``
    held, blank ones included, in their order; the lines above the fresh section and
    below the release's are the base's own; and the version is newer than every
    release heading the base opens with ``[X.Y.Z]``.  Lines are read as CommonMark
    ends them, their terminators aside.  The date is read, never compared with
    today.
    """
    cut = _cut_shape(changelog, version)
    if not isinstance(cut, _Cut):
        return CutProblem(cut, _cut_fix(version))
    before = sections(base, Prose(UNRELEASED_HEADER))
    if len(before) != 1:
        return CutProblem(
            Prose(f"is cut from a base with {len(before)} '{UNRELEASED_HEADER}' sections, not one"),
            Prose(f"Merge the base's '{UNRELEASED_HEADER}' sections into one on main first."),
        )
    newest = max(_releases(base), key=_key, default=None)
    if newest is not None and _key(version) <= _key(newest):
        return CutProblem(
            Prose(f"names release {version}, not newer than the base's newest release, {newest}"),
            Prose(
                f"Prepare a version newer than {newest}, in the commit, the title and the heading."
            ),
        )
    moved = _moved(changelog, base, cut, before[0], version)
    return None if moved is None else CutProblem(moved, _cut_fix(version))


def _moved(
    changelog: Prose, base: Prose, cut: _Cut, held: Section, version: ReleaseVersion
) -> Prose | None:
    """Say how the cut moved other lines than the base's unreleased ones, or None.

    Lines are read as CommonMark ends them, their terminators aside.
    """
    head, before = commonmark_lines(changelog), commonmark_lines(base)
    moved = head[cut.release.first - 1 : cut.release.end - 1]
    if moved != before[held.first - 1 : held.end - 1]:
        return Prose(
            f"holds under release {version} other lines, or the same in another order, than "
            + f"the base's '{UNRELEASED_HEADER}' held"
        )
    above, below = head[: cut.unreleased.heading.line - 1], head[cut.release.end - 1 :]
    if above != before[: held.heading.line - 1] or below != before[held.end - 1 :]:
        return Prose(f"changes text outside '{UNRELEASED_HEADER}' and the new release's section")
    return None


def base_changelog(branch: Branch) -> Prose | None:
    """Read CHANGELOG.md as the branch's merge-base holds it, or write why not and give None."""
    shown = subprocess.run(
        [find_executable("git"), "show", f"{branch.merge_base}:{CHANGELOG}"],
        capture_output=True,
        check=False,
    )
    reason = str(shown.stderr, "utf-8", "replace").strip()
    if shown.returncode == 0:
        try:
            return Prose(str(shown.stdout, "utf-8"))
        except UnicodeDecodeError as exc:
            reason = str(exc)
    _ = sys.stderr.write(
        f"check-changelog: FAIL — {CHANGELOG} cannot be read at the merge-base "
        + f"{branch.merge_base}: {reason}\n"
    )
    return None


def versions_refused(prepared: list[ReleaseVersion]) -> bool:
    """Write the refusal for a branch preparing more than one release; say if it was."""
    if len(prepared) <= 1:
        return False
    _ = sys.stderr.write(
        "check-changelog: FAIL — the branch prepares more than one release: "
        + f"{', '.join(prepared)}.\nKeep one: reword or drop the earlier preparation commit, "
        + "then force-push the re-signed branch (git push --force-with-lease); never pull the "
        + "old one back.\n"
    )
    return True


def cut_refused(version: ReleaseVersion, changelog: Prose, base: Prose) -> bool:
    """Write the refusal for a release the CHANGELOG does not cut from its base; say if one was."""
    problem = cut_problem(changelog, base, version)
    if problem is None:
        return False
    _ = sys.stderr.write(
        f"check-changelog: FAIL — the branch prepares release {version}, and CHANGELOG.md "
        + f"{problem.found}.\n{problem.fix}\n"
    )
    return True


def main() -> ExitStatus:
    """Fail on a refused subject, label, entry or section, or a release not cut from its base."""
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
    branch = read_branch(TOOL, base)
    if branch is None:
        return COULD_NOT_CHECK
    prepared = sorted(released(branch))
    base_text: Prose | None = None
    if len(prepared) == 1:
        base_text = base_changelog(branch)
        if base_text is None:
            return COULD_NOT_CHECK
    refused = [
        headers_refused(unreleased_headers(text)),
        subjects_refused(branch),
        labels_refused(branch, kernel_sources(snapshot)),
        entry_refused(branch),
        unowed_edit_refused(branch),
        versions_refused(prepared),
        base_text is not None and cut_refused(prepared[0], text, base_text),
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

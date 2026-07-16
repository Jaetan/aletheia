# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Citation gate: no agent-memory-store pointers in the living tree.

The agent memory store (``feedback_*.md``, ``project_*.md``, ``[[wikilink]]``
notes) lives under ``~/.claude/``, **outside the repository**. A pointer to it in
a tracked file resolves for nobody who has cloned the repo — it is dead on arrival
for the only audience the file has. This gate fails (exit 1) when such a pointer
appears in any tracked file that is expected to read as a product, so a one-time
strip cannot silently re-accrete (126 citations once did across source, and 6 more
had accreted in product docs, precisely because no gate watched them).

## What is scanned, and what is exempt

Every tracked, non-binary file is scanned EXCEPT:

* the **AI-process-infra docs** whose PURPOSE includes cross-referencing the store
  — ``CLAUDE.md``, ``AGENTS.md`` + ``AGENTS/``, ``docs/development/DEFERRED_ITEMS.md``
  (``MEMORY.md`` and ``.session-state.md`` are the agent store / gitignored, so git
  never tracks them here anyway). Note the user-facing logs are NOT exempt:
  ``CHANGELOG.md`` and ``PROJECT_STATUS.md`` are read by users, so a store pointer
  is as dead for their readers as for anyone's — they are gated, and being
  historical does not license an unresolvable pointer;
* the ``docs/development/E2_*`` proof-strategy backlog docs — kept with their
  internal references while the E.2 proof is live, and deleted once it lands;
* the detectors and their fixtures (this gate, ``check_docs``,
  ``check_no_review_marks``, and their tests) — they carry citation-shaped strings
  by construction. Excluded BY EXACT PATH so the exclusion cannot mask a real
  citation in an ordinary file (unit-tested);
* ``.archive/`` — the review work record.

## Relationship to the other doc gates

* ``tools/check_docs.py`` resolves Markdown links/anchors and flags
  Markdown-link-syntax memory links (``](memory/x.md)``). This gate overlaps there
  only on that one syntactic form; it additionally catches the **bare** shapes
  (``[[slug]]``, a bare ``memory/x.md``, a bare ``slug.md``) that link resolution
  cannot see.
* ``tools/check_no_review_marks.py`` flags review-*process* marks and *masks* store
  pointers (its concern is the round tokens inside a pointer's name). This gate is
  its complement: it flags the pointer itself.

## What it flags — unambiguous STRUCTURED forms only

A text matcher can catch a *structured* citation; it cannot catch **bare prose**
("see the project memory", "per the feedback note"). This gate's guarantee is
therefore "no *structured* store pointer in a gated file", **not** "the tree is
citation-free". The three shapes, each with no legitimate non-citation meaning:

1. a memory ``[[wikilink]]`` — ``[[feedback_x]]``, ``[[project_y]]`` (anchored on
   the store's slug prefixes, so C++ attributes ``[[maybe_unused]]`` /
   ``[[nodiscard]]`` never match);
2. a store path — ``memory/<name>.md``;
3. a memory-note filename — ``feedback_x.md`` / ``project_y.md`` (the ``.md``
   suffix on a slug-prefixed snake-case token is the discriminator; a bare
   ``project_root`` identifier, having no ``.md``, does not match).

Bare slug tokens without one of those anchors, git SHAs, ISO ``§`` clause cites,
and code cross-refs are intentionally NOT gated — they are ambiguous, and a green
tree must stay green without whitelisting innocent content.

Run ``python -m tools.check_no_memory_citations`` from the repo root. Exit 0 =
clean, 1 = citation found, 2 = could-not-check (a tracked file was unreadable —
never reported as clean). Its parsers are unit-tested by
``python/tests/test_check_no_memory_citations.py``.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tools._common import emit, git_ls_files

REPO = Path(__file__).resolve().parent.parent

# The store's slug prefixes. A memory note is always <prefix>_<name>; anchoring on
# these keeps the wikilink/filename shapes clear of innocent look-alikes (a C++
# ``[[maybe_unused]]``, a ``project_root`` identifier).
_PREFIX = r"(?:feedback|project|learnings|proof|review|reference)"

# The three unambiguous structured citation shapes.
_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(rf"\[\[{_PREFIX}_[A-Za-z0-9_]+\]\]"), "memory wikilink"),
    (re.compile(r"\bmemory/[A-Za-z0-9_./-]+\.(?:md|markdown)\b"), "agent-store path"),
    (
        # A <prefix>_<name>.md filename NOT already part of a ``memory/`` path
        # (the lookbehind stops double-reporting ``memory/project_x.md``).
        re.compile(rf"(?<![A-Za-z0-9_/.-]){_PREFIX}_[A-Za-z0-9_]+\.(?:md|markdown)\b"),
        "memory-note filename",
    ),
]

# Binary / non-text tracked files we never scan.
_BINARY_SUFFIXES = {
    ".png",
    ".jpg",
    ".jpeg",
    ".gif",
    ".ico",
    ".pdf",
    ".agdai",
    ".so",
    ".o",
    ".woff",
    ".woff2",
    ".ttf",
    ".zip",
    ".gz",
    ".sig",
    ".key",
    ".pub",
    ".wasm",
}

# Files that carry citation-shaped strings by construction (detectors + fixtures),
# legitimately cite the store (AI-process-infra docs), or are frozen history
# (CHANGELOG) — scanned-around, never flagged.
_EXEMPT_FILES = {
    # detectors + their fixtures
    "tools/check_docs.py",
    "tools/check_no_review_marks.py",
    "tools/check_no_memory_citations.py",
    "python/tests/test_check_docs.py",
    "python/tests/test_check_no_review_marks.py",
    "python/tests/test_check_no_memory_citations.py",
    # AI-process-infra docs whose purpose includes citing the store
    "CLAUDE.md",
    "AGENTS.md",
    "docs/development/DEFERRED_ITEMS.md",
}
_EXEMPT_PREFIXES = (
    ".archive/",  # review work record
    "AGENTS/",  # per-language coding-standard docs (AI-process infra)
    "docs/development/E2_",  # E.2 proof-strategy backlog docs (deleted once the proof lands)
)


def is_exempt(rel: str) -> bool:
    """Return True for detectors/fixtures, AI-infra docs, history, and the archive."""
    return rel in _EXEMPT_FILES or rel.startswith(_EXEMPT_PREFIXES)


def in_scope(rel: str) -> bool:
    """Return True if ``rel`` is a tracked file this gate scans.

    Every tracked, non-binary, non-exempt file — source AND product docs alike.
    Markdown is scanned too (the AI-process-infra docs that may cite the store are
    exempted by name), so a bare ``[[slug]]`` in a product ``.md`` doc is caught.
    """
    return not is_exempt(rel) and Path(rel).suffix not in _BINARY_SUFFIXES


def scan_text(rel: str, text: str) -> list[str]:
    """Return finding suffixes for ``text`` treated as file ``rel`` (empty = clean).

    The pure core of the scan — no filesystem — so the detector is unit-testable
    on synthetic input (``python/tests/test_check_no_memory_citations.py``).
    """
    findings: list[str] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        for pat, why in _PATTERNS:
            findings.extend(f"{rel}:{lineno}: {why} -> {m.group(0)!r}" for m in pat.finditer(line))
    return findings


def scan_file(rel: str) -> tuple[list[str], bool]:
    """Scan one tracked file: return ``(findings, could_not_read)``.

    A tracked file that cannot be read is reported as could-not-check (the caller
    turns it into exit 2) — never silently treated as clean.
    """
    try:
        text = (REPO / rel).read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        _ = sys.stderr.write(f"check_no_memory_citations: cannot read {rel}: {exc}\n")
        return [], True
    return scan_text(rel, text), False


def check_tree() -> tuple[list[str], bool]:
    """Scan every in-scope tracked file: return ``(findings, could_not_check)``."""
    findings: list[str] = []
    could_not_check = False
    for rel in git_ls_files(REPO):
        if not in_scope(rel):
            continue
        file_findings, unread = scan_file(rel)
        findings.extend(file_findings)
        could_not_check = could_not_check or unread
    return findings, could_not_check


def main(argv: list[str] | None = None) -> int:
    """Scan the gated tree; 1 if citations found, 2 if a file was unreadable, else 0."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)  # no options; --help only

    findings, could_not_check = check_tree()
    if findings:
        emit(f"check_no_memory_citations: {len(findings)} agent-store citation(s):")
        for f in findings:
            emit(f"  {f}")
        return 1
    if could_not_check:
        emit("check_no_memory_citations: COULD NOT CHECK — a tracked file was unreadable.")
        return 2
    emit("check_no_memory_citations: no agent-store citations in the gated tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

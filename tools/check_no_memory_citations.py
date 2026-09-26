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
  — ``CLAUDE.md``, ``AGENTS.md`` + ``AGENTS/``
  (``MEMORY.md``, ``TASKS.md`` and ``.session-state.md`` are the agent store / gitignored, so git
  never tracks them here anyway). Note the user-facing logs are NOT exempt:
  ``CHANGELOG.md`` and ``PROJECT_STATUS.md`` are read by users, so a store pointer
  is as dead for their readers as for anyone's — they are gated, and being
  historical does not license an unresolvable pointer;
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

from tools._common import (
    TreeScan,
    is_prose_file,
    pattern_findings,
    report_tree_scan,
    scan_tracked_tree,
)

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
        # A <prefix>_<name>.md filename. The word-char lookbehind prevents matching
        # inside a larger identifier (``subproject_x.md``); the ``memory/`` lookbehind
        # avoids double-reporting a ``memory/<name>.md`` path (already caught by the
        # path shape) while STILL flagging any other path (``docs/project_x.md``).
        re.compile(rf"(?<![A-Za-z0-9_])(?<!memory/){_PREFIX}_[A-Za-z0-9_]+\.(?:md|markdown)\b"),
        "memory-note filename",
    ),
]

# Files that carry citation-shaped strings by construction (detectors + fixtures)
# or legitimately cite the store (AI-process-infra docs) — scanned-around, never
# flagged. The user-facing logs (CHANGELOG, PROJECT_STATUS) are NOT here: they are
# gated (see the module docstring).
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
}
_EXEMPT_PREFIXES = (
    ".archive/",  # review work record
    "AGENTS/",  # per-language coding-standard docs (AI-process infra)
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
    return is_prose_file(rel, is_exempt)


def scan_text(rel: str, text: str) -> list[str]:
    """Return finding suffixes for ``text`` treated as file ``rel`` (empty = clean).

    The pure core of the scan — no filesystem — so the detector is unit-testable
    on synthetic input (``python/tests/test_check_no_memory_citations.py``).
    """
    return pattern_findings(rel, enumerate(text.splitlines(), start=1), _PATTERNS)


def check_tree(repo: Path = REPO) -> TreeScan:
    """Scan every in-scope tracked file of ``repo`` for agent-store citations."""
    return scan_tracked_tree(repo, is_exempt, scan_text)


def main(argv: list[str] | None = None, *, repo: Path = REPO) -> int:
    """Scan the gated tree; 2 if a file was unreadable, 1 if citations found, else 0."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)  # no options; --help only

    scan = check_tree(repo)
    return report_tree_scan(
        "check_no_memory_citations",
        scan,
        found=f"{len(scan.findings)} agent-store citation(s):",
        found_lines=scan.findings,
        clean="no agent-store citations in the gated tree.",
    )


if __name__ == "__main__":
    sys.exit(main())

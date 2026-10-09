# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The living documents carry no transient label and no link into the agent memory store.

A living document is any tracked Markdown file under ``docs/``, the root
``README.md`` and every other ``README.md``: each describes the current state,
so an internal review mark, a finding identifier or a session phrase such as
"pending push" in its prose is a finding, and so is a Markdown link into the
agent memory store, which no checkout holds. The repository-root logs, the
changelog and the status page, record history by purpose and are not read.
Fenced code and inline code spans are not prose, so a mark shown as an
example is not a finding. Each distinct mark is reported once per document,
and a tree with no living document is a finding, the scan holding nothing.
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._common import RelPath, prose_lines

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence
    from pathlib import Path

_PATTERNS = (
    (re.compile(r"\(PR [A-Z]\d*\)"), Prose("internal PR label")),
    (re.compile(r"\bR\d+ cluster\b"), Prose("review-round cluster mark")),
    (re.compile(r"\b(?:AGDA|GO|CPP|PY|RUST|XBINDING|DOCS)-[A-Z]-\d+\.\d+"), Prose("finding id")),
    (re.compile(r"\bPY-S-\d+"), Prose("review finding mark")),
    (re.compile(r"\bpending push\b", re.IGNORECASE), Prose("transient session phrase")),
    (re.compile(r"\bcommitted locally\b", re.IGNORECASE), Prose("transient session phrase")),
)
# A Markdown link into the agent memory store, which lives outside any checkout.
_MEMORY_LINK = re.compile(r"\][(](?:[^)]*/\.claude/[^)]*|memory/[^)]*)[)]")
_README = "README.md"


def is_living(rel: RelPath) -> bool:
    """Whether ``rel`` is a living document: under ``docs/``, or a ``README.md`` anywhere."""
    return rel.startswith("docs/") or rel == _README or rel.endswith(f"/{_README}")


def label_findings(rel: RelPath, text: Prose) -> list[Prose]:
    """Return one finding per memory-store link and per distinct mark in the prose of ``text``."""
    prose = "\n".join(line for _, line in prose_lines(rel, text))
    out = [
        Prose(f"{rel}: link into the ~/.claude memory store -> {m.group(0)}")
        for m in _MEMORY_LINK.finditer(prose)
    ]
    for pattern, why in _PATTERNS:
        out.extend(
            Prose(f"{rel}: {why} -> {mark!r}")
            for mark in sorted({m.group(0) for m in pattern.finditer(prose)})
        )
    return out


def findings(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return one finding per transient label or memory-store link in a living document.

    Args:
        root: The repository root.
        tracked: Every tracked path, as ``git ls-files`` prints it.
        documents: Every tracked Markdown file's text, by its repo-relative path.

    Returns:
        The findings, each naming the document that carries the mark.

    """
    del root, tracked
    living = [rel for rel in documents if is_living(rel)]
    if not living:
        return [Prose(f"{_README}: not tracked, and no other living document is")]
    return [finding for rel in living for finding in label_findings(rel, documents[rel])]

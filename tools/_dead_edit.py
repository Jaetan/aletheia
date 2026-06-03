#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Import-clause text editing for the dead-import tooling.

Produces, for a given imported name, the per-open variants of a file with that
name dropped from exactly ONE open's clause — the candidate removals the
confirm step (tools.warm_dead_imports) and the cleanup tool (tools.warm_apply)
recompile.  Grammar-complete via :func:`tools._agda_opens.find_opens` (every
open, every position), so it edits names that parse_imports cannot see (e.g. a
multi-line ``using`` clause, a non-``import`` ``open M``).
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING

from tools._agda_opens import find_opens
from tools.prune_unused_imports import remove_name_from_raw, remove_rename_from_raw

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools._agda_opens import Name, OpenInfo


def _edit_clause(raw: str, keyword: str, edit: Callable[[str], str | None]) -> str | None:
    """Apply `edit` to `raw` from the `keyword` clause onward, keeping the prefix.

    Slicing from the `using`/`renaming` keyword confines the removal to that
    clause, so a name equal to the opened module's last path component is never
    matched in the module path.  Returns None if the keyword is absent or `edit`
    finds nothing to remove.
    """
    match = re.search(rf"\b{keyword}\b", raw)
    if match is None:
        return None
    edited = edit(raw[match.start() :])
    return raw[: match.start()] + edited if edited is not None else None


def _open_raw_without_name(raw: str, open_info: OpenInfo, name: Name) -> str | None:
    """Return `raw` (one open's directive) with `name` dropped, or None if absent.

    Handles the three entry shapes: a plain `using` name, a `using (module X)`
    entry, and a `renaming` destination — each edited within its own clause.
    """
    if name in open_info.using_names:
        return _edit_clause(raw, "using", lambda c: remove_name_from_raw(c, name))
    if "module " + name in open_info.using_names:
        return _edit_clause(raw, "using", lambda c: remove_name_from_raw(c, "module " + name))
    pair = next(((s, d) for s, d in open_info.renaming if d == name), None)
    if pair is not None:
        return _edit_clause(raw, "renaming", lambda c: remove_rename_from_raw(c, pair[0], pair[1]))
    return None


def texts_without_name(original: str, name: Name) -> list[str]:
    """Each variant of `original` with `name` dropped from ONE open's clause.

    Iterates EVERY open (`find_opens`), not just top-level `open import` blocks,
    so a P1 name — a `using` entry on a non-`import` `open M`, an
    open-module-macro, or a local `where`/`let` open — is removable too.  A name
    imported in several opens (a duplicate) yields one variant per open, so the
    confirm tests EVERY occurrence (the redundant copy need not be the first).
    `public` re-exports are skipped (removing one would change the exported
    surface, which the per-file recompile cannot validate).  Opens that yield no
    change are skipped.
    """
    variants: list[str] = []
    for open_info in find_opens(original):
        if not open_info.is_open or open_info.has_public:
            continue
        start, end = open_info.span
        raw = original[start:end]
        edited = _open_raw_without_name(raw, open_info, name)
        if edited is not None and edited != raw:
            variants.append(original[:start] + edited + original[end:])
    return variants

"""IWYU R&D (ci-speed branch): attribute used names to their providing module.

Drives Agda's `Cmd_why_in_scope_toplevel` over `--interaction-json` to recover,
for each name referenced in a module's body, which `open` brought it into scope.
From that we derive the actually-used surface of each WILDCARD `open import M`
(no `using`/`renaming` list) — the input to an "import what you use" narrowing
suggestion.  Confirmed mechanism (see `memory/project_agda_iwyu.md`): the query
returns a `DisplayInfo`/`WhyInScope` payload whose message names "the opening of
M" for the responsible module.

Reuses the warm-process driver `WarmAgda` from `warm_dead_imports` so the stdlib
and shared interfaces load once.  Invoke as
`python -m tools.warm_iwyu <relpath.agda> [...]`.

LIMITATION (mixfix): names are queried by the body token's source text, so an
operator used infix (token `⊕`) is not matched to its scope name `_⊕_` and is
under-reported.  The suggested `using` list can therefore wrongly omit used
operators — this is informational R&D output, NOT yet safe to apply blindly.
Fix path: attribute by definitionSite identity (a wildcard's exported def-ids,
e.g. via `Cmd_show_module_contents`, matched against the body's def-ids —
mixfix-safe); tracked in `memory/project_agda_iwyu.md`.
"""

from __future__ import annotations

import json
import re
import sys
from typing import TYPE_CHECKING, TypedDict, cast

from tools._agda_imports import parse_imports
from tools._common import emit
from tools.warm_dead_imports import SRC, WarmAgda, line_offsets

if TYPE_CHECKING:
    from tools.warm_dead_imports import Token

# A WhyInScope message lists each responsible open as "- the opening of M at ...".
_OPENING_RE = re.compile(r"the opening of (\S+)")

# Safety cap on lines read while awaiting a query's DisplayInfo terminal.
_MAX_RESPONSE_LINES = 200


class _WhyInScopeInfo(TypedDict, total=False):
    """The `info` field of a WhyInScope DisplayInfo response."""

    kind: str
    message: str
    thing: str


class _DisplayResponse(TypedDict, total=False):
    """One `agda --interaction-json` response carrying display info."""

    kind: str
    info: _WhyInScopeInfo


def _parse_openings(message: str) -> list[str]:
    """Return the module paths named in a WhyInScope message, de-duplicated."""
    matches: list[str] = _OPENING_RE.findall(message)
    return list(dict.fromkeys(matches))


def why_in_scope(agda: WarmAgda, abspath: str, name: str) -> list[str]:
    """Return the modules whose opening brings `name` into scope in `abspath`.

    Sends `Cmd_why_in_scope_toplevel` and reads to the `DisplayInfo` terminal
    (the response is a `Status` then a `WhyInScope` display).  The module must
    already be loaded in `agda`.  An out-of-scope name yields an empty list
    rather than hanging.
    """
    proc = agda.proc
    if proc.stdin is None or proc.stdout is None:
        msg = "agda --interaction-json process has no stdin/stdout pipe"
        raise RuntimeError(msg)
    query = f'IOTCM "{abspath}" None Direct (Cmd_why_in_scope_toplevel "{name}")\n'
    _ = proc.stdin.write(query)
    proc.stdin.flush()
    for _attempt in range(_MAX_RESPONSE_LINES):
        line = proc.stdout.readline()
        if not line:
            msg = "agda --interaction-json exited during why_in_scope"
            raise RuntimeError(msg)
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            resp = cast("_DisplayResponse", json.loads(stripped))
        except json.JSONDecodeError:
            continue
        if resp.get("kind") != "DisplayInfo":
            continue
        info = resp.get("info")
        message = info.get("message", "") if info is not None else ""
        return _parse_openings(message)
    return []


def _wildcard_modules(text: str) -> set[str]:
    """Return the modules brought into scope UNQUALIFIED by a wildcard open.

    A wildcard is `open import M` with no `using`/`renaming` list and not
    `public`.  `import M` / `import M as N` (qualified-only — they add no
    unqualified names, so there is no using-list to narrow them to) are
    excluded by the leading-`open` check.
    """
    return {
        block.module_path
        for block in parse_imports(text)
        if block.raw.lstrip().startswith("open")
        and not block.using_names
        and not block.renaming_pairs
        and not block.has_public
    }


def _import_char_ranges(text: str) -> list[tuple[int, int]]:
    """Return the (start, end) char offsets of every import block in `text`."""
    offsets = line_offsets(text)
    ranges: list[tuple[int, int]] = []
    for block in parse_imports(text):
        start = offsets[block.line_start]
        end = offsets[block.line_end + 1] if block.line_end + 1 < len(offsets) else offsets[-1]
        ranges.append((start, end))
    return ranges


def _body_names(text: str, tokens: list[Token], ranges: list[tuple[int, int]]) -> list[str]:
    """Return the distinct names referenced in the body (outside import clauses).

    Only tokens that carry a `definitionSite` are kept — those resolve to a
    definition and are worth attributing to a providing module.
    """
    seen: dict[str, None] = {}
    for tok in tokens:
        rng = tok.get("range")
        if not rng:
            continue
        off0 = rng[0] - 1
        if any(start <= off0 < end for start, end in ranges):
            continue
        if tok.get("definitionSite") is None:
            continue
        seen.setdefault(text[off0 : rng[1] - 1], None)
    return list(seen)


def attribute_wildcards(
    agda: WarmAgda, abspath: str, text: str, tokens: list[Token]
) -> dict[str, list[str]]:
    """Map each wildcard-opened module to the body names attributed to it.

    The result for module M is M's actually-used surface in this file — the
    `using (...)` list that would replace its wildcard `open import M`.
    """
    wildcards = _wildcard_modules(text)
    ranges = _import_char_ranges(text)
    used_by: dict[str, set[str]] = {module: set() for module in wildcards}
    for name in _body_names(text, tokens, ranges):
        for module in why_in_scope(agda, abspath, name):
            if module in wildcards:
                used_by[module].add(name)
    return {module: sorted(names) for module, names in used_by.items()}


def _report(rel: str, used: dict[str, list[str]]) -> None:
    """Print the wildcard-narrowing suggestion for one file."""
    emit(f"=== {rel}: {len(used)} wildcard open(s) ===")
    for module, names in sorted(used.items()):
        if names:
            emit(f"  open import {module}  -->  using ({'; '.join(names)})  [{len(names)} used]")
        else:
            emit(f"  open import {module}  -->  (no names used here; wildcard import is DEAD)")


def main() -> int:
    """Attribute wildcard-opened names for each file given on the command line."""
    rels = [arg for arg in sys.argv[1:] if not arg.startswith("--")]
    if not rels:
        emit("usage: python -m tools.warm_iwyu <relpath.agda> [...]")
        return 2
    with WarmAgda() as agda:
        for rel in rels:
            abspath = str(SRC / rel)
            text = (SRC / rel).read_text(encoding="utf-8")
            tokens, ok = agda.load(abspath)
            if not ok:
                emit(f"{rel}: LOAD FAILED (agda could not check it)")
                continue
            _report(rel, attribute_wildcards(agda, abspath, text, tokens))
    return 0


if __name__ == "__main__":
    sys.exit(main())

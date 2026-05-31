"""IWYU R&D (ci-speed branch): attribute used names to their providing module.

Derives, for each WILDCARD `open import M` (no `using`/`renaming` list), the
subset of M's exports actually referenced in the body — the `using (...)` list
an "import what you use" narrowing would replace the wildcard with.

Attribution is by **definitionSite identity** (mixfix-safe).  Two facts make it
work (see `memory/project_agda_iwyu.md`):

  * Every body highlighting token carries a `definitionSite = {filepath, pos}`,
    and reading `filepath` at `pos` spells the FULL name — so an operator used
    infix (token `⊕`) resolves to its definition name `_⊕_`.
  * `Cmd_show_module_contents_toplevel` returns M's full export names (again
    `_⊕_`, not the part `⊕`).

A name is used-from-M iff it is in `show_module_contents(M)` AND its full name
appears among the body's definition-site names.  Re-exports fall out for free
(the def-site spells the name; smc lists it under M).

Reuses the warm-process driver `WarmAgda` from `warm_dead_imports`.  Invoke as
`python -m tools.warm_iwyu <relpath.agda> [...]`.

Documented edges (not yet solved): a name *renamed* on re-export (smc shows the
renamed name, the def-site the original → missed); a name exported by two
wildcard modules (lands in both using-lists — conservative, harmless).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING, TypedDict, cast

from tools._agda_imports import parse_imports
from tools._common import emit
from tools.warm_dead_imports import SRC, WarmAgda, line_offsets

if TYPE_CHECKING:
    from tools.warm_dead_imports import Token

# A definition name is the run of characters at its def-site up to whitespace
# or a bracket/semicolon (Agda names may contain `_`, operators, sub/superscripts).
_NAME_RE = re.compile(r"[^\s(){};]+")

# Safety cap on lines read while awaiting a query's DisplayInfo terminal.
_MAX_RESPONSE_LINES = 200


class _ModuleEntry(TypedDict, total=False):
    """One entry in a ModuleContents listing."""

    name: str
    term: str


class _ModuleContentsInfo(TypedDict, total=False):
    """The `info` field of a ModuleContents DisplayInfo response."""

    kind: str
    contents: list[_ModuleEntry]


class _ModuleContentsResponse(TypedDict, total=False):
    """One `agda --interaction-json` response carrying module contents."""

    kind: str
    info: _ModuleContentsInfo


def show_module_contents(agda: WarmAgda, abspath: str, module: str) -> list[str]:
    """Return the full export names of `module` via Cmd_show_module_contents.

    `module` must be in scope (imported) in the loaded `abspath`.  Reads to the
    `DisplayInfo` terminal; a non-ModuleContents display (e.g. an error) yields
    an empty list rather than hanging.
    """
    proc = agda.proc
    if proc.stdin is None or proc.stdout is None:
        msg = "agda --interaction-json process has no stdin/stdout pipe"
        raise RuntimeError(msg)
    query = f'IOTCM "{abspath}" None Direct (Cmd_show_module_contents_toplevel AsIs "{module}")\n'
    _ = proc.stdin.write(query)
    proc.stdin.flush()
    for _attempt in range(_MAX_RESPONSE_LINES):
        line = proc.stdout.readline()
        if not line:
            msg = "agda --interaction-json exited during show_module_contents"
            raise RuntimeError(msg)
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            resp = cast("_ModuleContentsResponse", json.loads(stripped))
        except json.JSONDecodeError:
            continue
        if resp.get("kind") != "DisplayInfo":
            continue
        info = resp.get("info")
        if info is None or info.get("kind") != "ModuleContents":
            return []
        return [name for entry in info.get("contents", []) if (name := entry.get("name"))]
    return []


def _read_text(filepath: str) -> str:
    """Return the file's text, or empty string if it cannot be read."""
    try:
        return Path(filepath).read_text(encoding="utf-8")
    except OSError:
        return ""


def _full_name_at(text: str, position: int) -> str:
    """Extract the (mixfix-complete) name defined at 1-based codepoint `position`."""
    match = _NAME_RE.match(text, position - 1)
    return match.group(0) if match else ""


def _wildcard_modules(text: str) -> set[str]:
    """Return the modules brought into scope UNQUALIFIED by a wildcard open.

    A wildcard is `open import M` with NO `using`/`renaming` clause and not
    `public`.  Excluded: `import M` / `import M as N` (qualified-only, via the
    leading-`open` check) and `open import M using ()` (an explicit
    import-nothing for qualified `M.x` access, via the `"using"` check — it is
    already maximally narrow, so there is nothing to suggest).  parse_imports
    reports an empty `using ()` as no names, so the raw `"using"` check is what
    tells the two apart.
    """
    return {
        block.module_path
        for block in parse_imports(text)
        if block.raw.lstrip().startswith("open")
        and "using" not in block.raw
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


def used_full_names(tokens: list[Token], ranges: list[tuple[int, int]]) -> set[str]:
    """Return the full names of every definition referenced in the body.

    For each body token (outside import clauses) carrying a `definitionSite`,
    the name is read from the DEFINITION file at the recorded position — so a
    mixfix operator used infix (`⊕`) resolves to its full name (`_⊕_`).
    """
    cache: dict[str, str] = {}
    names: set[str] = set()
    for tok in tokens:
        rng = tok.get("range")
        if not rng:
            continue
        off0 = rng[0] - 1
        if any(start <= off0 < end for start, end in ranges):
            continue
        site = tok.get("definitionSite")
        if site is None:
            continue
        filepath = site["filepath"]
        if filepath not in cache:
            cache[filepath] = _read_text(filepath)
        full = _full_name_at(cache[filepath], site["position"])
        if full:
            names.add(full)
    return names


def attribute_wildcards(
    agda: WarmAgda, abspath: str, text: str, tokens: list[Token]
) -> dict[str, list[str]]:
    """Map each wildcard-opened module to its actually-used export surface.

    The list for module M is the `using (...)` that an "import what you use"
    narrowing would replace M's wildcard `open import M` with.
    """
    wildcards = _wildcard_modules(text)
    ranges = _import_char_ranges(text)
    used = used_full_names(tokens, ranges)
    return {
        module: sorted(set(show_module_contents(agda, abspath, module)) & used)
        for module in sorted(wildcards)
    }


def _report(rel: str, used: dict[str, list[str]]) -> None:
    """Print the wildcard-narrowing suggestion for one file."""
    emit(f"=== {rel}: {len(used)} wildcard open(s) ===")
    for module, names in used.items():
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

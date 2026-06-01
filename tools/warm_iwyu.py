"""IWYU R&D (ci-speed branch): narrow wildcard `open import M` to `using (...)`.

Derives, for each WILDCARD `open import M` (no `using`/`renaming` clause), the
subset of M's exports actually referenced in the body — the `using (...)` list
an "import what you use" narrowing replaces the wildcard with — and can apply
and verify that narrowing.

Attribution is by **definitionSite identity** (mixfix-safe).  Two facts make it
work (see `memory/project_agda_iwyu.md`):

  * Every body highlighting token carries a `definitionSite = {filepath, pos}`,
    and reading `filepath` at `pos` spells the FULL name — so an operator used
    infix (token `⊕`) resolves to its definition name `_⊕_`.
  * `Cmd_show_module_contents_toplevel` returns M's full export names (again
    `_⊕_`, not the part `⊕`), including re-exports.

A name is used-from-M iff it is in `show_module_contents(M)` AND its full name
appears among the body's definition-site names.  Re-exports fall out for free.

`--apply` rewrites each verified narrowing into the source; the narrowing is
recompiled first, so one that would not type-check is reported and skipped
rather than applied.  Crash-safe: a rewritten file is restored on interrupt.

Error-driven completion (`complete_narrowing`) recovers the names static
attribution cannot see — one *renamed* on re-export (`ℕ`, re-exported for the
builtin `Nat`: the def-site spells `Nat`, `show_module_contents` spells `ℕ`, so
the intersection drops it) and one used only in an inferred position (no body
token at all).  When a narrowing fails to type-check, agda's `[NotInScope]`
error names each dropped-but-needed name as a `did you mean 'M.x'` suggestion
(always present, since `using` keeps `M.*` qualified-accessible); those names
are added back and the narrowing re-verified to a fixpoint.

Reuses the warm-process driver `WarmAgda` from `warm_dead_imports`.  Invoke as
`python -m tools.warm_iwyu [--apply] <relpath.agda> [...]`.

Remaining edge: a name exported by two wildcard modules lands in both
using-lists (conservative — both `did you mean` candidates are added).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, TypedDict, cast

from tools._agda_imports import parse_imports, replace_block_in_lines
from tools._common import emit, install_restore_handlers, track_inflight, untrack_inflight
from tools.warm_dead_imports import SRC, LoadResult, WarmAgda, line_offsets, ranged_tokens

if TYPE_CHECKING:
    from tools._agda_imports import ImportBlock
    from tools.warm_dead_imports import Token

# An Agda identifier as it appears in a `using (...)` list (mixfix-complete,
# e.g. "ℕ", "_∷_").
type Name = str
# A module path brought into scope by an `open import`, e.g. "Aletheia.Prelude".
type ModulePath = str
# A file's wildcard narrowing: each wildcard-opened module → the using-list of
# the names actually referenced from it.
type UsingByModule = dict[ModulePath, list[Name]]

# A definition name is the run of characters at its def-site up to whitespace
# or a bracket/semicolon (Agda names may contain `_`, operators, sub/superscripts).
_NAME_RE = re.compile(r"[^\s(){};]+")

# Safety cap on lines read while awaiting a query's DisplayInfo terminal.
_MAX_RESPONSE_LINES = 200

# Agda's NotInScope error quotes the qualified form of each dropped-but-needed
# name, e.g. "(did you mean 'Aletheia.Prelude.ℕ'?)" — the completion signal.
_SUGGESTION_RE = re.compile(r"'([^']+)'")

# Backstop on error-driven completion rounds (one reload recovers one name).
_MAX_COMPLETION_ROUNDS = 40


class Narrowing(NamedTuple):
    """A file's completed wildcard-import narrowing.

    `used` maps each wildcard-opened module to the using-list it should narrow
    to.  `verified` is True iff that narrowing type-checks — and ONLY then is it
    safe to apply; when False, `used` is the best effort reached before a stall
    and is left unapplied (the wildcard stays).  `rounds` is the number of
    error-driven completion reloads taken (1 ⇒ static attribution was already
    complete).
    """

    used: UsingByModule
    verified: bool
    rounds: int


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


def show_module_contents(agda: WarmAgda, abspath: str, module: ModulePath) -> list[Name]:
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


def _is_wildcard(block: ImportBlock) -> bool:
    """Return True iff `block` is a wildcard `open import M` (unqualified names).

    Excludes `import M` / `import M as N` (no leading `open`) and any `using`
    clause — including `using ()` and a multi-line `using` clause (keyword and
    paren on separate lines), both of which parse_imports leaves with empty
    `using_names`; the raw `"using"` check is what tells them apart.
    """
    return (
        block.raw.lstrip().startswith("open")
        and "using" not in block.raw
        and not block.renaming_pairs
        and not block.has_public
    )


def _wildcard_modules(text: str) -> set[ModulePath]:
    """Return the modules brought into scope UNQUALIFIED by a wildcard open."""
    return {block.module_path for block in parse_imports(text) if _is_wildcard(block)}


def _import_char_ranges(text: str) -> list[tuple[int, int]]:
    """Return the (start, end) char offsets of every import block in `text`."""
    offsets = line_offsets(text)
    ranges: list[tuple[int, int]] = []
    for block in parse_imports(text):
        start = offsets[block.line_start]
        end = offsets[block.line_end + 1] if block.line_end + 1 < len(offsets) else offsets[-1]
        ranges.append((start, end))
    return ranges


def used_full_names(tokens: list[Token], ranges: list[tuple[int, int]]) -> set[Name]:
    """Return the full names of every definition referenced in the body.

    For each body token (outside import clauses) carrying a `definitionSite`,
    the name is read from the DEFINITION file at the recorded position — so a
    mixfix operator used infix (`⊕`) resolves to its full name (`_⊕_`).
    """
    cache: dict[str, str] = {}
    names: set[Name] = set()
    for tok, rng in ranged_tokens(tokens):
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
) -> UsingByModule:
    """Map each wildcard-opened module to its actually-used export surface."""
    wildcards = _wildcard_modules(text)
    ranges = _import_char_ranges(text)
    used = used_full_names(tokens, ranges)
    return {
        module: sorted(set(show_module_contents(agda, abspath, module)) & used)
        for module in sorted(wildcards)
    }


def _narrowed_block_raw(block: ImportBlock, names: list[Name]) -> str:
    """Rewrite a wildcard block as `open import M using (n1; n2; ...)`."""
    indent = block.raw[: len(block.raw) - len(block.raw.lstrip())]
    return f"{indent}open import {block.module_path} using ({'; '.join(names)})\n"


def narrow_text(text: str, used: UsingByModule) -> str:
    """Rewrite each used wildcard `open import M` to `using (...)` in `text`."""
    lines = text.splitlines(keepends=True)
    blocks = [b for b in parse_imports(text) if _is_wildcard(b) and used.get(b.module_path)]
    for block in sorted(blocks, key=lambda b: b.line_start, reverse=True):
        lines = replace_block_in_lines(
            lines, block, _narrowed_block_raw(block, used[block.module_path])
        )
    return "".join(lines)


def verify_narrowing(agda: WarmAgda, abspath: str, text: str, used: UsingByModule) -> LoadResult:
    """Rewrite the wildcards to using-lists, reload, and return the LoadResult.

    Always restores the original text (crash-safe); the caller re-applies the
    (already-verified) narrowing only when `--apply` is set.  The reload's `ok`
    and `error` drive completion; its `tokens` (of the narrowed file) are unused.
    """
    if not any(used.values()):
        return LoadResult([], ok=True, error="")
    install_restore_handlers()
    path = Path(abspath)
    try:
        track_inflight(abspath, text)
        _ = path.write_text(narrow_text(text, used), encoding="utf-8")
        return agda.load(abspath)
    finally:
        _ = path.write_text(text, encoding="utf-8")
        untrack_inflight(abspath)


def _module_for(qualified: str, modules: list[ModulePath]) -> ModulePath | None:
    """Return the longest wildcard module M for which `qualified` == 'M.<name>'."""
    best: ModulePath | None = None
    for module in modules:
        if qualified.startswith(module + ".") and (best is None or len(module) > len(best)):
            best = module
    return best


def _add_missing(used: UsingByModule, error: str) -> bool:
    """Append each `did you mean 'M.name'` suggestion to module M's using-list.

    Returns True iff a new name was added.  A name already present, or one whose
    qualifier is not a narrowed wildcard module, is skipped — so a stalled
    completion (agda still failing with nothing new to add) returns False.

    When the suggestion is a record-field access (`M.Record.field`, e.g.
    `…Cache.CachedSignal.value`), stripping the module leaves `Record.field` —
    which is not a valid using-list entry.  The entry that brings it into scope
    is the FIRST component (`Record`); since Agda names never contain `.`, the
    first dotted component is always the right top-level name (a record, a
    submodule, …) to add.
    """
    modules = list(used)
    suggestions: list[str] = _SUGGESTION_RE.findall(error)
    added = False
    for qualified in suggestions:
        module = _module_for(qualified, modules)
        if module is None:
            continue
        name = qualified[len(module) + 1 :].split(".", 1)[0]
        if name and name not in used[module]:
            used[module].append(name)
            added = True
    return added


def complete_narrowing(agda: WarmAgda, abspath: str, text: str, used: UsingByModule) -> Narrowing:
    """Grow each wildcard's using-list by the names agda reports out-of-scope.

    Body-token attribution misses a name whose def-site spells something other
    than M re-exports (e.g. `ℕ`, re-exported for the builtin `Nat`) and any name
    used only in an inferred position (no body token at all).  After a narrowing
    fails to type-check, every `did you mean 'M.name'` in the error names a
    still-qualified-accessible export to add back (`open import M using (X)` keeps
    `M.*` qualified, so the suggestion always appears); re-verify and repeat to a
    fixpoint.  Only verify-confirmed names are kept, and a stall ends the loop
    leaving the wildcard untouched (see `Narrowing`).

    A dropped operator used *infix* yields a `[NoParseForLHS]` parse error with
    no `did you mean` suggestion, so completion cannot recover it and stalls
    (safe — the wildcard stays).  This is rare: static attribution already
    catches body-used operators mixfix-safely, so an operator reaches completion
    only when renamed on re-export or used purely in an inferred position.
    """
    used = {module: list(names) for module, names in used.items()}
    rounds = 0
    for rounds in range(1, _MAX_COMPLETION_ROUNDS + 1):
        outcome = verify_narrowing(agda, abspath, text, used)
        if outcome.ok:
            for names in used.values():
                names.sort()
            return Narrowing(used, verified=True, rounds=rounds)
        if not _add_missing(used, outcome.error):
            return Narrowing(used, verified=False, rounds=rounds)
    return Narrowing(used, verified=False, rounds=rounds)


def _report(rel: str, used: UsingByModule) -> None:
    """Print the wildcard-narrowing suggestion for one file."""
    emit(f"=== {rel}: {len(used)} wildcard open(s) ===")
    for module, names in used.items():
        if names:
            emit(f"  open import {module}  -->  using ({'; '.join(names)})  [{len(names)} used]")
        else:
            emit(
                f"  open import {module}  -->  (no names attributed; not a narrowing "
                + "target — check whole-import removability via the dead-import/prune oracle)"
            )


def _process(agda: WarmAgda, rel: str, *, apply: bool) -> None:
    """Report (and optionally apply) the wildcard narrowing for one file."""
    abspath = str(SRC / rel)
    text = (SRC / rel).read_text(encoding="utf-8")
    loaded = agda.load(abspath)
    if not loaded.ok:
        emit(f"{rel}: LOAD FAILED (agda could not check it)")
        return
    used = attribute_wildcards(agda, abspath, text, loaded.tokens)
    if not any(used.values()):
        _report(rel, used)
        return
    narrowing = complete_narrowing(agda, abspath, text, used)
    _report(rel, narrowing.used)
    emit(f"  narrowing type-checks: {narrowing.verified}  (completion rounds: {narrowing.rounds})")
    if apply and narrowing.verified:
        _ = (SRC / rel).write_text(narrow_text(text, narrowing.used), encoding="utf-8")
        emit(f"  APPLIED narrowing to {rel}")


def main() -> int:
    """Report (or, with --apply, apply) wildcard narrowing for the given files."""
    args = sys.argv[1:]
    apply = "--apply" in args
    rels = [arg for arg in args if not arg.startswith("--")]
    if not rels:
        emit("usage: python -m tools.warm_iwyu [--apply] <relpath.agda> [...]")
        return 2
    with WarmAgda() as agda:
        for rel in rels:
            _process(agda, rel, apply=apply)
    return 0


if __name__ == "__main__":
    sys.exit(main())

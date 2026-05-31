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
recompiled first, so an incomplete used-set (it would not type-check) is
reported and skipped rather than applied.  Crash-safe: a rewritten file is
restored on interrupt.

Reuses the warm-process driver `WarmAgda` from `warm_dead_imports`.  Invoke as
`python -m tools.warm_iwyu [--apply] <relpath.agda> [...]`.

Documented edges (not solved): a name *renamed* on re-export (smc shows the
renamed name, the def-site the original → missed — but `--apply` would catch
the resulting type error and skip); a name exported by two wildcard modules
(lands in both using-lists — conservative).
"""

from __future__ import annotations

import atexit
import contextlib
import json
import re
import signal
import sys
from pathlib import Path
from typing import TYPE_CHECKING, TypedDict, cast

from tools._agda_imports import parse_imports, replace_block_in_lines
from tools._common import emit
from tools.warm_dead_imports import SRC, WarmAgda, line_offsets

if TYPE_CHECKING:
    from tools._agda_imports import ImportBlock
    from tools.warm_dead_imports import Token

# A definition name is the run of characters at its def-site up to whitespace
# or a bracket/semicolon (Agda names may contain `_`, operators, sub/superscripts).
_NAME_RE = re.compile(r"[^\s(){};]+")

# Safety cap on lines read while awaiting a query's DisplayInfo terminal.
_MAX_RESPONSE_LINES = 200

# Source files rewritten in-flight, restored on interrupt (path -> original).
_inflight: dict[str, str] = {}
_handlers_installed: list[bool] = []


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


def _restore_inflight() -> None:
    """Restore any source file left rewritten by an interrupted narrowing."""
    for path_str, original in list(_inflight.items()):
        with contextlib.suppress(OSError):
            _ = Path(path_str).write_text(original, encoding="utf-8")
    _inflight.clear()


def _signal_restore(signum: int, _frame: object) -> None:
    """SIGINT/SIGTERM handler: restore rewritten files, then exit."""
    _restore_inflight()
    sys.exit(128 + signum)


def _install_restore_handlers() -> None:
    """Install atexit + SIGINT/SIGTERM restore handlers once (idempotent)."""
    if _handlers_installed:
        return
    _ = atexit.register(_restore_inflight)
    for sig in (signal.SIGINT, signal.SIGTERM):
        _ = signal.signal(sig, _signal_restore)
    _handlers_installed.append(True)


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


def _wildcard_modules(text: str) -> set[str]:
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
    """Map each wildcard-opened module to its actually-used export surface."""
    wildcards = _wildcard_modules(text)
    ranges = _import_char_ranges(text)
    used = used_full_names(tokens, ranges)
    return {
        module: sorted(set(show_module_contents(agda, abspath, module)) & used)
        for module in sorted(wildcards)
    }


def _narrowed_block_raw(block: ImportBlock, names: list[str]) -> str:
    """Rewrite a wildcard block as `open import M using (n1; n2; ...)`."""
    indent = block.raw[: len(block.raw) - len(block.raw.lstrip())]
    return f"{indent}open import {block.module_path} using ({'; '.join(names)})\n"


def narrow_text(text: str, used: dict[str, list[str]]) -> str:
    """Rewrite each used wildcard `open import M` to `using (...)` in `text`."""
    lines = text.splitlines(keepends=True)
    blocks = [b for b in parse_imports(text) if _is_wildcard(b) and used.get(b.module_path)]
    for block in sorted(blocks, key=lambda b: b.line_start, reverse=True):
        lines = replace_block_in_lines(
            lines, block, _narrowed_block_raw(block, used[block.module_path])
        )
    return "".join(lines)


def verify_narrowing(agda: WarmAgda, abspath: str, text: str, used: dict[str, list[str]]) -> bool:
    """Rewrite the wildcards to using-lists, reload, and report if it type-checks.

    Always restores the original text (crash-safe); the caller re-applies the
    (already-verified) narrowing only when `--apply` is set.
    """
    if not any(used.values()):
        return True
    _install_restore_handlers()
    path = Path(abspath)
    try:
        _inflight[abspath] = text
        _ = path.write_text(narrow_text(text, used), encoding="utf-8")
        _tokens, ok = agda.load(abspath)
        return ok
    finally:
        _ = path.write_text(text, encoding="utf-8")
        _ = _inflight.pop(abspath, None)


def _report(rel: str, used: dict[str, list[str]]) -> None:
    """Print the wildcard-narrowing suggestion for one file."""
    emit(f"=== {rel}: {len(used)} wildcard open(s) ===")
    for module, names in used.items():
        if names:
            emit(f"  open import {module}  -->  using ({'; '.join(names)})  [{len(names)} used]")
        else:
            emit(f"  open import {module}  -->  (no names used here; wildcard import is DEAD)")


def _process(agda: WarmAgda, rel: str, *, apply: bool) -> None:
    """Report (and optionally apply) the wildcard narrowing for one file."""
    abspath = str(SRC / rel)
    text = (SRC / rel).read_text(encoding="utf-8")
    tokens, ok = agda.load(abspath)
    if not ok:
        emit(f"{rel}: LOAD FAILED (agda could not check it)")
        return
    used = attribute_wildcards(agda, abspath, text, tokens)
    _report(rel, used)
    if not any(used.values()):
        return
    verified = verify_narrowing(agda, abspath, text, used)
    emit(f"  narrowing type-checks: {verified}")
    if apply and verified:
        _ = (SRC / rel).write_text(narrow_text(text, used), encoding="utf-8")
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

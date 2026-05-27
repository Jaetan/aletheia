#!/usr/bin/env python3
"""Agda import parsing, surgical editing, dependency graphs, and type-checking.

The substrate shared by the dead-import tooling (``prune_unused_imports`` and
``warm_dead_imports``).  It owns three concerns, all expressed as pure functions
plus small value types:

  * **parsing** -- read ``open import M ... using (...) [renaming (...)]`` blocks
    out of Agda source into :class:`ImportBlock` values;
  * **editing** -- remove a single ``using`` name or ``renaming`` pair from a
    block's raw text and splice it back into the file's line list;
  * **driving agda** -- run ``agda --type-check`` on a module (via
    :class:`TypecheckCtx`) and report whether it still type-checks without
    introducing new silent-semantic-change warnings, plus the module-dependency
    graphs used to order parallel work.

Imported as ``from tools._agda_imports import ...``.  ``prune_unused_imports``
re-exports the names its callers (notably ``warm_dead_imports``) reach for.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

from tools._common import match_paren_content, split_top_level_semicolons


def _find_repo_root() -> Path:
    """Locate the Aletheia repo root.

    Search order:
      1. $ALETHEIA_REPO env var, if set.
      2. Walk up from CWD looking for `aletheia.agda-lib`.
      3. Walk up from the script's directory (works when installed in-repo).

    This lets the script live anywhere (e.g. `~/.local/bin/`) and still find
    the repo when invoked from inside it.
    """
    env = os.environ.get("ALETHEIA_REPO")
    if env:
        p = Path(env).resolve()
        if (p / "aletheia.agda-lib").exists():
            return p
    for base in (Path.cwd().resolve(), Path(__file__).resolve()):
        for p in [base, *base.parents]:
            if (p / "aletheia.agda-lib").exists():
                return p
    message = "could not locate Aletheia repo root; set ALETHEIA_REPO or run from inside the repo"
    raise RuntimeError(message)


REPO_ROOT = _find_repo_root()
SRC_DIR = REPO_ROOT / "src"

AGDA_BIN = Path(os.environ.get("AGDA_BIN", "/home/nicolas/.cabal/bin/agda"))

# Character class for Agda identifier continuation: letters, digits, _, ', -.
# Used in word-boundary lookarounds.
IDENT_CHARS = r"A-Za-z0-9_'\-"


@dataclass
class ImportBlock:
    """One import block, possibly spanning multiple lines.

    Shape: ``open import M ... [using (...)] [renaming (...)] [public]``.
    """

    line_start: int  # 0-indexed, inclusive
    line_end: int  # 0-indexed, inclusive (last line of the block)
    raw: str  # original block text (including trailing newline of last line)
    module_path: str
    has_public: bool
    using_names: list[str] = field(default_factory=list)
    # renaming_pairs[i] = (source, destination); the destination is the
    # in-scope name in the body.
    renaming_pairs: list[tuple[str, str]] = field(default_factory=list)


# ----------------------------------------------------------------------------
# Parser
# ----------------------------------------------------------------------------


def parse_imports(content: str) -> list[ImportBlock]:
    """Parse all import blocks in the file content."""
    lines = content.splitlines(keepends=True)
    blocks: list[ImportBlock] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if stripped.startswith(("open import ", "import ")):
            block, consumed = _parse_one_block(lines, i)
            if block:
                blocks.append(block)
                i += consumed
                continue
        i += 1
    return blocks


def _parse_one_block(lines: list[str], start: int) -> tuple[ImportBlock | None, int]:
    """Collect lines belonging to one import block.

    A block extends until paren depth returns to 0 AND the next line is not
    a continuation (`using (...)`, `renaming (...)`, or `public`).
    """
    paren_depth = 0
    end = start
    while end < len(lines):
        clean = _strip_comments(lines[end])
        paren_depth += clean.count("(") - clean.count(")")
        end += 1
        if paren_depth == 0:
            # Check if next line continues this import block.
            if end < len(lines):
                nxt = lines[end].lstrip()
                if (
                    re.match(r"^using\s*\(?", nxt)
                    or re.match(r"^renaming\s*\(?", nxt)
                    or nxt.startswith("public")
                ):
                    continue
            break
        if paren_depth < 0:
            # Malformed input; give up on this block.
            return None, end - start
    raw = "".join(lines[start:end])
    return _parse_block_content(start, end - 1, raw), end - start


def _strip_comments(line: str) -> str:
    """Remove `{- ... -}` and `-- ...` comments from a single line.

    Multi-line block comments are not handled (uncommon in imports).
    """
    line = re.sub(r"\{-.*?-\}", "", line)
    idx = line.find("--")
    if idx >= 0:
        return line[:idx]
    return line


def _strip_comments_all(text: str) -> str:
    """Strip comments throughout a multi-line block."""
    without_block = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", without_block)


def _parse_block_content(line_start: int, line_end: int, raw: str) -> ImportBlock:
    """Parse one import block's raw text into an ImportBlock."""
    text = _strip_comments_all(raw)

    has_public = bool(re.search(r"\bpublic\b", text))

    mod_m = re.search(r"(?:open\s+)?import\s+([\w.]+)", text)
    module_path = mod_m.group(1) if mod_m else "?"

    using_names: list[str] = []
    renaming_pairs: list[tuple[str, str]] = []

    using_clause = _extract_paren_after(text, "using")
    if using_clause is not None:
        using_names = _split_top_level(using_clause)

    renaming_clause = _extract_paren_after(text, "renaming")
    if renaming_clause is not None:
        for pair_str in _split_top_level(renaming_clause):
            pm = re.match(r"^(.+?)\s+to\s+(.+)$", pair_str)
            if pm:
                renaming_pairs.append((pm.group(1).strip(), pm.group(2).strip()))

    return ImportBlock(
        line_start=line_start,
        line_end=line_end,
        raw=raw,
        module_path=module_path,
        has_public=has_public,
        using_names=using_names,
        renaming_pairs=renaming_pairs,
    )


def _extract_paren_after(text: str, keyword: str) -> str | None:
    """Find ``keyword (...)`` and return the parenthesized content.

    Returns None if not found.  Handles nested parens (rare in imports).
    """
    pat = re.compile(rf"\b{re.escape(keyword)}\s*\(")
    m = pat.search(text)
    if not m:
        return None
    return match_paren_content(text, m.end())


def _split_top_level(content: str) -> list[str]:
    """Split a using/renaming clause on ``;`` at paren depth 0."""
    return split_top_level_semicolons(content)


# ----------------------------------------------------------------------------
# Editor — surgical removals
# ----------------------------------------------------------------------------


def remove_name_from_raw(raw: str, name: str) -> str | None:
    """Remove `name` from a `using (...)` clause in `raw`.

    Returns new raw text, or None if the name wasn't found.

    Handles the four positional cases (sole entry / first / middle / last)
    by removing the name plus its adjacent semicolon, preserving surrounding
    whitespace/newlines as much as possible.
    """
    escaped = re.escape(name)
    nb = rf"(?<![{IDENT_CHARS}])"
    nf = rf"(?![{IDENT_CHARS}])"

    # Pattern 1 — name followed by `;` (anywhere except last in clause):
    #   `(X; Y; Z)` or `(... ; X; ...)` — consume `X` and its trailing `;`
    #    + surrounding whitespace.
    pat1 = rf"{nb}{escaped}{nf}\s*;\s*"
    # Pattern 2 — name preceded by `;` (last in clause):
    #   `(... ; X)` — consume the leading `;` and the name.
    pat2 = rf";\s*{nb}{escaped}{nf}\s*"
    # Pattern 3 — sole entry:
    #   `(X)` — consume the name (resulting in `()`).
    pat3 = rf"{nb}{escaped}{nf}\s*"

    # Try pat1 first (most common).  If only one match in clause, pat1 might
    # consume a separator that should remain; pat2 then handles the LAST-entry
    # case correctly.  Try pat3 as fallback for the sole-entry case.
    for pat in (pat1, pat2, pat3):
        new = re.sub(pat, "", raw, count=1)
        if new != raw:
            return new
    return None


def remove_rename_from_raw(raw: str, src: str, dst: str) -> str | None:
    """Remove `src to dst` pair from a `renaming (...)` clause."""
    src_esc = re.escape(src)
    dst_esc = re.escape(dst)
    pair = rf"{src_esc}\s+to\s+{dst_esc}"
    nb = rf"(?<![{IDENT_CHARS}])"

    pat1 = rf"{nb}{pair}\s*;\s*"
    pat2 = rf";\s*{nb}{pair}\s*"
    pat3 = rf"{nb}{pair}\s*"

    for pat in (pat1, pat2, pat3):
        new = re.sub(pat, "", raw, count=1)
        if new != raw:
            return new
    return None


def replace_block_in_lines(lines: list[str], block: ImportBlock, new_raw: str) -> list[str]:
    """Splice `new_raw` in place of the original block lines."""
    new_block_lines = new_raw.splitlines(keepends=True)
    # Ensure block ends with newline (matches original convention).
    if new_block_lines and not new_block_lines[-1].endswith("\n"):
        new_block_lines[-1] += "\n"
    return lines[: block.line_start] + new_block_lines + lines[block.line_end + 1 :]


# ----------------------------------------------------------------------------
# Type-checker invocation
# ----------------------------------------------------------------------------


@dataclass(frozen=True)
class TypecheckCtx:
    """The agda invocation parameters shared by every type-check in a run.

    These four values are fixed for the whole pruning pass (they come from CLI
    flags), so bundling them keeps the dozen type-check call sites from each
    threading four positional arguments.  ``src_dir`` is the cwd agda runs in
    (paths are passed relative to it); ``rts_cores`` / ``rts_heap_gb`` set the
    GHC RTS ``-N`` / ``-M`` flags; ``timeout`` caps each agda call in seconds.
    """

    src_dir: Path
    rts_cores: int
    rts_heap_gb: int
    timeout: int


# Warning categories that signal SILENT SEMANTIC CHANGES — must not appear
# as a NEW warning after a removal:
#   PatternShadowsConstructor: a pattern like `... | True = X` reinterpreted as
#     a pattern-variable binding when `True` is no longer in scope as a
#     constructor.  The file type-checks but its semantics silently change.
#     Discovered by R22 sweep against Coalgebra/stepL's TruthVal pattern matches.
#   UnreachableClauses: typically the downstream consequence of
#     PatternShadowsConstructor (the catch-all swallows later clauses).
_SEMANTIC_WARNING_TAGS = ("PatternShadowsConstructor", "UnreachableClauses")


def path_to_module(file_path: Path, src_dir: Path) -> str:
    """Convert `src/Aletheia/Foo/Bar.agda` → `Aletheia.Foo.Bar`."""
    rel = file_path.relative_to(src_dir)
    return str(rel.with_suffix("")).replace("/", ".")


def _forward_deps(files: list[Path], src_dir: Path) -> dict[Path, set[Path]]:
    """Map each file to the set of files in ``files`` it imports.

    Dependencies on files OUTSIDE ``files`` (stdlib, excluded files) are
    ignored — their interfaces are stable for the whole run.
    """
    module_to_file: dict[str, Path] = {}
    for f in files:
        try:
            module_to_file[path_to_module(f, src_dir)] = f
        except ValueError:
            continue

    deps: dict[Path, set[Path]] = {f: set() for f in files}
    pat = re.compile(r"^(?:open\s+)?import\s+([\w.]+)", flags=re.MULTILINE)
    for f in files:
        try:
            content = f.read_text(encoding="utf-8")
        except OSError:
            continue
        for m in pat.finditer(content):
            dep_file = module_to_file.get(m.group(1))
            if dep_file is not None and dep_file != f:
                deps[f].add(dep_file)
    return deps


def topological_levels(files: list[Path], src_dir: Path) -> list[list[Path]]:
    """Group ``files`` into topological levels.

    Level 0 = files with no Aletheia.* dependencies on other files IN
    ``files`` (true leaves wrt the queue).
    Level N = files whose every Aletheia.* dependency on a file in ``files``
    is at level < N.

    Within a single level, files have no inter-dependencies, so parallel
    workers can safely process them concurrently without ``.agdai`` race
    conditions (see ``feedback_agda_import_pruning_safety.md`` for the race
    pattern observed in sweeps #2 and #3).  Across levels, level K's files
    are processed strictly AFTER all of level <K, so by the time a level-K
    file is touched its dependencies' interfaces are stable.

    Returns ``list[list[Path]]`` ordered from level 0 (leaves) upward.
    Within a level, files are sorted alphabetically for determinism.
    """
    deps = _forward_deps(files, src_dir)
    # Kahn's algorithm: in-degree = number of unprocessed dependencies.
    in_degree: dict[Path, int] = {f: len(deps[f]) for f in files}
    # Reverse graph: f → set of files that depend on f (its dependents).
    dependents: dict[Path, list[Path]] = {f: [] for f in files}
    for f in files:
        for d in deps[f]:
            dependents[d].append(f)

    levels: list[list[Path]] = []
    remaining = set(files)
    while remaining:
        level = [f for f in remaining if in_degree[f] == 0]
        if not level:
            # Cycle (shouldn't happen in Agda).  Dump remaining as a final
            # bucket so we don't hang.
            levels.append(sorted(remaining))
            break
        levels.append(sorted(level))
        for f in level:
            remaining.discard(f)
            for dep in dependents[f]:
                in_degree[dep] -= 1
    return levels


def build_reverse_dep_graph(all_agda_files: list[Path]) -> dict[str, list[Path]]:
    """Scan every .agda file's imports; return module-name → list-of-importers.

    Used to compute the direct-consumer set when a removal touches a
    `public` re-export line: the consumer files need to be re-checked to
    confirm the removal didn't break their resolution of the re-exported
    name.

    A file appears in its own consumers list iff it imports itself (which
    is illegal in Agda — so never), so duplicate-skip isn't strictly
    required, but we deduplicate anyway for cleanliness.
    """
    consumers: dict[str, list[Path]] = {}
    pat = re.compile(r"^(?:open\s+)?import\s+([\w.]+)", flags=re.MULTILINE)
    for f in all_agda_files:
        try:
            content = f.read_text(encoding="utf-8")
        except OSError:
            continue
        seen_modules: set[str] = set()
        for m in pat.finditer(content):
            module = m.group(1)
            if module in seen_modules:
                continue
            seen_modules.add(module)
            consumers.setdefault(module, []).append(f)
    # Deduplicate (a file might import the same module twice via aliases).
    return {k: list(dict.fromkeys(v)) for k, v in consumers.items()}


def _count_semantic_warnings(stdout: bytes, stderr: bytes) -> int:
    """Count occurrences of semantic-change warnings.

    Agda emits warnings to stdout (not stderr), so the stdout stream is the
    primary source; stderr is checked as a fallback in case future Agda
    versions change the routing.
    """
    s_out = stdout.decode("utf-8", errors="replace")
    s_err = stderr.decode("utf-8", errors="replace")
    combined = s_out + "\n" + s_err
    return sum(combined.count(tag) for tag in _SEMANTIC_WARNING_TAGS)


def _agda_cmd(rel_path: str, ctx: TypecheckCtx) -> list[str]:
    """Build the ``agda +RTS -N.. -M..G -RTS <rel_path>`` argument list."""
    return [
        str(AGDA_BIN),
        "+RTS",
        f"-N{ctx.rts_cores}",
        f"-M{ctx.rts_heap_gb}G",
        "-RTS",
        rel_path,
    ]


def typecheck(
    rel_path: str,
    ctx: TypecheckCtx,
    *,
    baseline_warning_count: int = 0,
) -> bool:
    """Run ``agda --type-check`` on ``rel_path`` (relative to ``ctx.src_dir``).

    Returns True iff:
      - agda exits 0, AND
      - the number of ``PatternShadowsConstructor`` / ``UnreachableClauses``
        warnings is <= ``baseline_warning_count``.

    The second condition catches the silent-semantic-change bug where a
    removal turns constructor patterns into pattern-variable bindings.
    Caller should compute the baseline via ``warning_count_for`` before the
    first removal attempt.
    """
    try:
        result = subprocess.run(
            _agda_cmd(rel_path, ctx),
            check=False,
            cwd=str(ctx.src_dir),
            capture_output=True,
            timeout=ctx.timeout,
        )
        if result.returncode != 0:
            return False
        return _count_semantic_warnings(result.stdout, result.stderr) <= baseline_warning_count
    except subprocess.TimeoutExpired:
        return False


def warning_count_for(
    rel_path: str,
    ctx: TypecheckCtx,
    *,
    retries: int = 4,
    retry_sleep_s: int = 45,
) -> int:
    """Run agda once and report the count of semantic-change warnings.

    Used as the per-file baseline.  Returns -1 if the file fails to
    type-check (caller should treat as a pre-check failure).

    **Race-condition mitigation:** when multiple workers process files in
    parallel and a worker happens to test removals on file F while another
    worker is computing the baseline for F's dependent G, G's elaboration
    can fail because F's ``.agdai`` is mid-flight.  This typically resolves
    itself once the first worker's agda invocation completes and writes a
    consistent ``.agdai``.  Retry up to ``retries`` times with ``retry_sleep_s``
    backoff between attempts.  R22 full-sweep #2 (2026-05-21) showed this
    on the ``CAN/Encoding/*`` cluster: 7 of 16 files failed baseline without
    retries; retry+sleep would have let those settle.
    """
    cmd = _agda_cmd(rel_path, ctx)
    for attempt in range(retries):
        try:
            result = subprocess.run(
                cmd,
                check=False,
                cwd=str(ctx.src_dir),
                capture_output=True,
                timeout=ctx.timeout,
            )
        except subprocess.TimeoutExpired:
            pass
        else:
            if result.returncode == 0:
                return _count_semantic_warnings(result.stdout, result.stderr)
        if attempt < retries - 1:
            time.sleep(retry_sleep_s)
    return -1


def typecheck_with_consumers(
    file_path: Path,
    consumers: list[Path],
    consumer_baselines: dict[Path, int],
    ctx: TypecheckCtx,
    *,
    file_baseline_warnings: int,
) -> bool:
    """Type-check ``file_path`` AND each direct consumer.

    Used when testing removals on a ``public`` re-export line: removing a name
    from a public block changes the file's exported surface, so we must
    verify that every direct consumer still type-checks.

    ``consumer_baselines`` is a mutable cache of {consumer_path: warning_count}
    populated lazily on first check.  The first time a consumer is checked,
    its current (pre-modification) warning count is recorded; subsequent
    checks compare against that baseline.

    NOTE: The baseline is captured the FIRST time we check the consumer
    AFTER the file under test has been modified — which means the baseline
    is "the consumer's warning count given some modification to file_path".
    To get a TRUE pre-modification baseline, the caller should precompute
    via ``prefill_consumer_baselines`` before any modifications.

    Returns True iff:
      1. ``file_path`` itself type-checks with no new semantic-change warnings.
      2. Every consumer type-checks with no new semantic-change warnings.
    """
    rel_file = str(file_path.relative_to(ctx.src_dir))
    if not typecheck(rel_file, ctx, baseline_warning_count=file_baseline_warnings):
        return False
    for c in consumers:
        try:
            rel_c = str(c.relative_to(ctx.src_dir))
        except ValueError:
            continue
        # Lazy fallback to 0 if no prefill happened (prefill_consumer_baselines
        # is the recommended path for a true pre-modification baseline).
        baseline = consumer_baselines.get(c, 0)
        if not typecheck(rel_c, ctx, baseline_warning_count=baseline):
            return False
    return True


def prefill_consumer_baselines(
    consumers: list[Path],
    consumer_baselines: dict[Path, int],
    ctx: TypecheckCtx,
) -> None:
    """Compute the pre-modification semantic-warning count for each consumer.

    Called BEFORE any removal attempt that might affect these consumers,
    so the post-modification check has a true baseline to compare against.
    Skips consumers already cached.
    """
    for c in consumers:
        if c in consumer_baselines:
            continue
        try:
            rel_c = str(c.relative_to(ctx.src_dir))
        except ValueError:
            consumer_baselines[c] = 0
            continue
        count = warning_count_for(rel_c, ctx)
        consumer_baselines[c] = max(count, 0)


# Per-worker (process-local) consumer-check context.  Set by prune_file at the
# start of each block; read by the type-check call sites in the bisect helpers.
# We use process-local module state here rather than threading additional
# parameters through the half-dozen helper signatures (which would have made
# every call site noisier).  Each `ProcessPoolExecutor` worker has its own copy
# of this module, so the state is isolated.  The containers are mutated in place
# (never rebound) so no `global` declaration is needed.
_block_consumers: list[Path] = []
_block_consumer_baselines: dict[Path, int] = {}


def set_block_check_context(consumers: list[Path], consumer_baselines: dict[Path, int]) -> None:
    """Update process-local consumer-check state.

    Called by ``prune_file`` before processing each block.  Pass an empty
    ``consumers`` list to disable consumer checks for the current block.
    """
    _block_consumers.clear()
    _block_consumers.extend(consumers)
    _block_consumer_baselines.clear()
    _block_consumer_baselines.update(consumer_baselines)


def check_modified(file_path: Path, ctx: TypecheckCtx, *, file_baseline_warnings: int) -> bool:
    """Run the universal post-modification check: file itself + block consumers.

    Drop-in replacement for the prior ``typecheck(...)`` calls in bisect
    helpers.  When ``_block_consumers`` is empty (non-public blocks or when
    ``--include-public`` is off), behaves identically to ``typecheck``.
    """
    return typecheck_with_consumers(
        file_path,
        _block_consumers,
        _block_consumer_baselines,
        ctx,
        file_baseline_warnings=file_baseline_warnings,
    )


def gather_agda_files(paths: list[Path]) -> list[Path]:
    """Recursively collect *.agda files from the given paths."""
    files: list[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p.resolve())
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            _ = sys.stderr.write(f"warning: {p} is not a file or directory; skipping\n")
    return [f.resolve() for f in files]



def find_live_block(
    current_lines: list[str], module_path: str, original_idx: int
) -> ImportBlock | None:
    """After mutations, re-parse and find the block matching `module_path`.

    Use original_idx to disambiguate if multiple blocks share a module_path
    (rare).  Pick the original_idx-th matching block.
    """
    fresh_blocks = parse_imports("".join(current_lines))
    matching = [b for b in fresh_blocks if b.module_path == module_path]
    if not matching:
        return None
    # If multiple, prefer the same positional index.
    if original_idx < len(matching):
        return matching[original_idx]
    return matching[-1]

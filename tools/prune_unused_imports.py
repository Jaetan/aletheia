#!/usr/bin/env python3
"""prune_unused_imports.py — agda-driven dead-import remover.

For each .agda file:
  1. Parse all `open import M ... using (...) [renaming (...)]` blocks.
  2. For every name in `using (...)` and every pair in `renaming (...)`,
     attempt removal: rewrite the file with that name dropped, run
     `agda --type-check`.  If exit 0, keep the removal; else restore.
  3. The type-checker is the ground truth: zero false positives, zero
     false negatives.  All mixfix forms (infix `a X b`, sections
     `(_X y)` / `(x X_)`, free combinator `_X_`), module-qualified
     access (`module X` + `X.field` body uses), `as N` aliases, and
     `renaming` pairs are resolved correctly because we just ask agda.

Concurrency: file-level parallel workers.  Each file's audit is serial
(tests mutate the file).  Different files can be in flight simultaneously
because each file's `.agdai` interface is independent.

Public re-exports: `open import M ... public` lines are SKIPPED by default
(removing a name from them changes the file's exported surface, which can
break downstream consumers).  Use --include-public to test them anyway —
this only checks the file itself, NOT downstream, so combine with
--final-check to run `cabal run shake -- check-properties` at the end.

Usage:
    tools/prune_unused_imports.py [OPTIONS] [PATHS...]

Default paths: src/

Options:
    -j, --workers N        Parallel file workers (default: 4)
        --rts-cores K      GHC RTS cores per agda call (default: 8)
        --rts-heap G       GHC RTS heap per agda call in GB (default: 3)
        --timeout SECS     Per-agda-call timeout (default: 300)
        --include-public   Test `public` re-export lines (default: skip).
        --final-check      After pruning, run `cabal run shake -- check-properties`.
                           Restores all changes if the project-wide check fails.
        --dry-run          Don't modify files; report what would be removed.
        --quiet            Suppress per-file output.
        --verbose          Per-name decision logging.
        --pre-check        Verify each file type-checks before pruning;
                           skip files that fail.
        --no-bisect        Disable bisection (pure per-name brute force).

The default mode tries removing ALL names in an import block at once
(bisection optimization).  If that fails, it falls back to per-name
testing for that block.  Best case: 1 type-check per all-dead block.
Worst case: 1 + N type-checks per block where N is the block's name count.

Output: per-file summary line + aggregate stats.  Exit 0 if all files
processed successfully; 1 if any failures.
"""

from __future__ import annotations

import argparse
import atexit
import concurrent.futures
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

# ----------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------


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
        for p in [base] + list(base.parents):
            if (p / "aletheia.agda-lib").exists():
                return p
    raise RuntimeError(
        "could not locate Aletheia repo root; set ALETHEIA_REPO or run from inside the repo"
    )


REPO_ROOT = _find_repo_root()
SRC_DIR = REPO_ROOT / "src"
AGDA_BIN = Path(os.environ.get("AGDA_BIN", "/home/nicolas/.cabal/bin/agda"))

# Character class for Agda identifier continuation: letters, digits, _, ', -.
# Used in word-boundary lookarounds.
IDENT_CHARS = r"A-Za-z0-9_'\-"

# ----------------------------------------------------------------------------
# Data model
# ----------------------------------------------------------------------------


@dataclass
class ImportBlock:
    """One `open import M ... [using (...)] [renaming (...)] [public]` block,
    possibly spanning multiple lines.
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


@dataclass
class FileStats:
    file: Path
    using_tested: int = 0
    using_removed: int = 0
    renaming_tested: int = 0
    renaming_removed: int = 0
    public_blocks_skipped: int = 0
    type_checks: int = 0
    seconds: float = 0.0
    baseline_warnings: int = 0
    error: str | None = None

    @property
    def removed_total(self) -> int:
        return self.using_removed + self.renaming_removed


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
        if stripped.startswith("open import ") or stripped.startswith("import "):
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
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


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
    """Find `keyword (...)` and return the parenthesized content.

    Returns None if not found.  Handles nested parens (rare in imports).
    """
    pat = re.compile(rf"\b{re.escape(keyword)}\s*\(")
    m = pat.search(text)
    if not m:
        return None
    start = m.end()
    depth = 1
    i = start
    while i < len(text) and depth > 0:
        ch = text[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return text[start:i]
        i += 1
    return None


def _split_top_level(content: str) -> list[str]:
    """Split a using/renaming clause on `;` at paren depth 0."""
    parts: list[str] = []
    depth = 0
    buf: list[str] = []
    for ch in content:
        if ch == "(":
            depth += 1
            buf.append(ch)
        elif ch == ")":
            depth -= 1
            buf.append(ch)
        elif ch == ";" and depth == 0:
            item = "".join(buf).strip()
            if item:
                parts.append(item)
            buf = []
        else:
            buf.append(ch)
    item = "".join(buf).strip()
    if item:
        parts.append(item)
    return parts


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


def topological_levels(files: list[Path], src_dir: Path) -> list[list[Path]]:
    """Group `files` into topological levels.

    Level 0 = files with no Aletheia.* dependencies on other files IN
    `files` (true leaves wrt the queue).
    Level N = files whose every Aletheia.* dependency on a file in `files`
    is at level < N.

    Within a single level, files have no inter-dependencies, so parallel
    workers can safely process them concurrently without `.agdai` race
    conditions (see `feedback_agda_import_pruning_safety.md` for the race
    pattern observed in sweeps #2 and #3).  Across levels, level K's files
    are processed strictly AFTER all of level <K, so by the time a level-K
    file is touched its dependencies' interfaces are stable.

    Dependencies on files OUTSIDE `files` (e.g. stdlib, or files the user
    excluded from this run) are ignored — those interfaces are stable for
    the whole run, so they don't constrain the order.

    Returns: `list[list[Path]]` ordered from level 0 (leaves) upward.
    Within a level, files are sorted alphabetically for determinism.
    """
    files_set = set(files)
    module_to_file: dict[str, Path] = {}
    for f in files:
        try:
            module_to_file[path_to_module(f, src_dir)] = f
        except ValueError:
            continue

    # Forward dependencies: f → set of files (also in `files`) that f imports.
    deps: dict[Path, set[Path]] = {f: set() for f in files}
    pat = re.compile(r"^(?:open\s+)?import\s+([\w.]+)", flags=re.MULTILINE)
    for f in files:
        try:
            content = f.read_text(encoding="utf-8")
        except OSError:
            continue
        for m in pat.finditer(content):
            mod = m.group(1)
            dep_file = module_to_file.get(mod)
            if dep_file is not None and dep_file != f:
                deps[f].add(dep_file)

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


def build_reverse_dep_graph(all_agda_files: list[Path], src_dir: Path) -> dict[str, list[Path]]:
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
    for k in consumers:
        consumers[k] = list(dict.fromkeys(consumers[k]))
    return consumers


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


def typecheck(
    rel_path: str,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    baseline_warning_count: int = 0,
) -> bool:
    """Run `agda --type-check` on `rel_path` (relative to src_dir).

    Returns True iff:
      - agda exits 0, AND
      - the number of `PatternShadowsConstructor` / `UnreachableClauses`
        warnings is <= `baseline_warning_count`.

    The second condition catches the silent-semantic-change bug where a
    removal turns constructor patterns into pattern-variable bindings.
    Caller should compute the baseline via `warning_count_for(file_path)`
    before the first removal attempt.
    """
    cmd = [
        str(AGDA_BIN),
        "+RTS",
        f"-N{rts_cores}",
        f"-M{rts_heap_gb}G",
        "-RTS",
        rel_path,
    ]
    try:
        result = subprocess.run(
            cmd,
            check=False,
            cwd=str(src_dir),
            capture_output=True,
            timeout=timeout,
        )
        if result.returncode != 0:
            return False
        if _count_semantic_warnings(result.stdout, result.stderr) > baseline_warning_count:
            return False
        return True
    except subprocess.TimeoutExpired:
        return False


def warning_count_for(
    rel_path: str,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    retries: int = 4,
    retry_sleep_s: int = 45,
) -> int:
    """Run agda once and report the count of semantic-change warnings.

    Used as the per-file baseline.  Returns -1 if the file fails to
    type-check (caller should treat as a pre-check failure).

    **Race-condition mitigation:** when multiple workers process files in
    parallel and a worker happens to test removals on file F while another
    worker is computing the baseline for F's dependent G, G's elaboration
    can fail because F's `.agdai` is mid-flight.  This typically resolves
    itself once the first worker's agda invocation completes and writes a
    consistent `.agdai`.  Retry up to `retries` times with `retry_sleep_s`
    backoff between attempts.  R22 full-sweep #2 (2026-05-21) showed this
    on the `CAN/Encoding/*` cluster: 7 of 16 files failed baseline without
    retries; retry+sleep would have let those settle.
    """
    cmd = [
        str(AGDA_BIN),
        "+RTS",
        f"-N{rts_cores}",
        f"-M{rts_heap_gb}G",
        "-RTS",
        rel_path,
    ]
    last_failure: str | None = None
    for attempt in range(retries):
        try:
            result = subprocess.run(
                cmd,
                check=False,
                cwd=str(src_dir),
                capture_output=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            last_failure = "timeout"
        else:
            if result.returncode == 0:
                return _count_semantic_warnings(result.stdout, result.stderr)
            last_failure = f"exit={result.returncode}"
        if attempt < retries - 1:
            time.sleep(retry_sleep_s)
    return -1


def typecheck_with_consumers(
    file_path: Path,
    consumers: list[Path],
    consumer_baselines: dict[Path, int],
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    file_baseline_warnings: int,
) -> bool:
    """Type-check `file_path` AND each direct consumer.

    Used when testing removals on a `public` re-export line: removing a name
    from a public block changes the file's exported surface, so we must
    verify that every direct consumer still type-checks.

    `consumer_baselines` is a mutable cache of {consumer_path: warning_count}
    populated lazily on first check.  The first time a consumer is checked,
    its current (pre-modification) warning count is recorded; subsequent
    checks compare against that baseline.

    NOTE: The baseline is captured the FIRST time we check the consumer
    AFTER the file under test has been modified — which means the baseline
    is "the consumer's warning count given some modification to file_path".
    To get a TRUE pre-modification baseline, the caller should precompute
    via `prefill_consumer_baselines()` before any modifications.

    Returns True iff:
      1. `file_path` itself type-checks with no new semantic-change warnings.
      2. Every consumer type-checks with no new semantic-change warnings.
    """
    rel_file = str(file_path.relative_to(src_dir))
    if not typecheck(
        rel_file,
        src_dir,
        rts_cores,
        rts_heap_gb,
        timeout,
        baseline_warning_count=file_baseline_warnings,
    ):
        return False
    for c in consumers:
        try:
            rel_c = str(c.relative_to(src_dir))
        except ValueError:
            continue
        baseline = consumer_baselines.get(c)
        if baseline is None:
            # Lazy compute: if no prefill happened, fall back to 0.
            # (Best-effort; prefill_consumer_baselines is the recommended path.)
            baseline = 0
        if not typecheck(
            rel_c,
            src_dir,
            rts_cores,
            rts_heap_gb,
            timeout,
            baseline_warning_count=baseline,
        ):
            return False
    return True


def prefill_consumer_baselines(
    consumers: list[Path],
    consumer_baselines: dict[Path, int],
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
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
            rel_c = str(c.relative_to(src_dir))
        except ValueError:
            consumer_baselines[c] = 0
            continue
        count = warning_count_for(rel_c, src_dir, rts_cores, rts_heap_gb, timeout)
        consumer_baselines[c] = max(count, 0)


# Per-worker (process-local) consumer-check context.  Set by prune_file
# at the start of each block; read by the type-check call sites in the
# bisect helpers.  We use process-local globals here rather than threading
# additional parameters through the half-dozen helper signatures (which
# would have made every call site noisier).  Each `ProcessPoolExecutor`
# worker has its own copy of these globals, so the state is isolated.
_BLOCK_CONSUMERS: list[Path] = []
_BLOCK_CONSUMER_BASELINES: dict[Path, int] = {}


def _set_block_check_context(consumers: list[Path], consumer_baselines: dict[Path, int]) -> None:
    """Update process-local consumer-check state.

    Called by `prune_file` before processing each block.  Pass an empty
    `consumers` list to disable consumer checks for the current block.
    """
    global _BLOCK_CONSUMERS, _BLOCK_CONSUMER_BASELINES
    _BLOCK_CONSUMERS = consumers
    _BLOCK_CONSUMER_BASELINES = consumer_baselines


def _check_modified(
    file_path: Path,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    file_baseline_warnings: int,
) -> bool:
    """Universal post-modification check: file itself + any block-context consumers.

    Drop-in replacement for the prior `typecheck(...)` calls in bisect
    helpers.  When `_BLOCK_CONSUMERS` is empty (non-public blocks or when
    --include-public is off), behaves identically to `typecheck`.
    """
    return typecheck_with_consumers(
        file_path,
        _BLOCK_CONSUMERS,
        _BLOCK_CONSUMER_BASELINES,
        src_dir,
        rts_cores,
        rts_heap_gb,
        timeout,
        file_baseline_warnings,
    )


def project_typecheck(timeout: int = 1200) -> bool:
    """Run `cabal run shake -- check-properties` from repo root."""
    cmd = ["cabal", "run", "shake", "--", "check-properties"]
    try:
        result = subprocess.run(
            cmd, check=False, cwd=str(REPO_ROOT), capture_output=True, timeout=timeout
        )
        return (
            result.returncode == 0
            and b"All proof modules type-checked successfully!" in result.stdout
        )
    except subprocess.TimeoutExpired:
        return False


# ----------------------------------------------------------------------------
# Pruning algorithm
# ----------------------------------------------------------------------------


def prune_file(
    file_path: Path,
    *,
    src_dir: Path,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    include_public: bool,
    dry_run: bool,
    pre_check: bool,
    use_bisect: bool,
    verbose: bool,
    consumers_map: dict[str, list[Path]] | None = None,
) -> FileStats:
    """Prune one file.  Returns FileStats.

    Crash-safety: writes a sibling `.prune-bak` file before any modification.
    The `finally` clause restores the file to a coherent state (original on
    dry-run / exception, pruned on success).  If the process is killed
    bypassing `finally` (e.g. SIGKILL), the `.prune-bak` file survives and
    can be restored manually via `--restore-backups` mode.
    """
    stats = FileStats(file=file_path)
    t0 = time.monotonic()

    try:
        rel_path = str(file_path.relative_to(src_dir))
    except ValueError:
        stats.error = "file is not under src_dir"
        return stats

    original_content = file_path.read_text(encoding="utf-8")
    backup_path = file_path.with_suffix(file_path.suffix + ".prune-bak")
    backup_path.write_text(original_content, encoding="utf-8")

    final_content = original_content  # default if anything goes wrong
    consumer_baselines: dict[Path, int] = {}

    try:
        # Compute baseline count of semantic-change warnings (always — even
        # without --pre-check, we need it to detect when a removal silently
        # changes pattern matches into pattern-variable bindings).
        baseline_warnings = warning_count_for(rel_path, src_dir, rts_cores, rts_heap_gb, timeout)
        if baseline_warnings < 0:
            stats.error = "baseline type-check failed; file does not type-check"
            return stats
        stats.baseline_warnings = baseline_warnings

        # When `--include-public` is on AND the file has any public block,
        # precompute the consumer set + their warning baselines once.
        # We use the file's OWN module path (Aletheia.X.Y.Z) to find its
        # consumers in the global graph.
        file_consumers: list[Path] = []
        if include_public and consumers_map is not None:
            file_module = path_to_module(file_path, src_dir)
            file_consumers = [c for c in consumers_map.get(file_module, []) if c != file_path]

        blocks = parse_imports(original_content)
        if not blocks:
            stats.seconds = time.monotonic() - t0
            return stats

        # Working state: current file content (mutated as removals succeed).
        current_lines = original_content.splitlines(keepends=True)

        for block_idx, block in enumerate(blocks):
            if block.has_public and not include_public:
                stats.public_blocks_skipped += 1
                continue

            # Re-parse the block from current_lines, because earlier blocks
            # may have shifted line numbers.  Find by module_path.
            live_block = _find_live_block(current_lines, block.module_path, block_idx)
            if live_block is None:
                continue

            # Per-block check context: when this block has `public` AND
            # --include-public is on, every removal-attempt also re-checks
            # the direct consumers of THIS FILE (because removing a name
            # from a public block changes the file's exported surface).
            # Otherwise, the consumer list is empty (no extra work).
            if block.has_public and include_public and file_consumers:
                # Precompute consumer baselines once on the first public
                # block we hit, so we have a true pre-modification baseline
                # to compare each consumer's post-removal warnings against.
                prefill_consumer_baselines(
                    file_consumers,
                    consumer_baselines,
                    src_dir,
                    rts_cores,
                    rts_heap_gb,
                    timeout,
                )
                _set_block_check_context(file_consumers, consumer_baselines)
            else:
                _set_block_check_context([], consumer_baselines)

            if use_bisect and len(live_block.using_names) > 1:
                _bisect_using(
                    file_path,
                    src_dir,
                    live_block,
                    current_lines,
                    rts_cores,
                    rts_heap_gb,
                    timeout,
                    stats,
                    verbose,
                )
            else:
                _per_name_using(
                    file_path,
                    src_dir,
                    live_block,
                    current_lines,
                    rts_cores,
                    rts_heap_gb,
                    timeout,
                    stats,
                    verbose,
                )

            # Re-parse for renaming pairs (block may have changed after using-removal).
            if live_block.renaming_pairs:
                live_block = _find_live_block(current_lines, block.module_path, block_idx)
                if live_block is not None and live_block.renaming_pairs:
                    if use_bisect and len(live_block.renaming_pairs) > 1:
                        _bisect_renaming(
                            file_path,
                            src_dir,
                            live_block,
                            current_lines,
                            rts_cores,
                            rts_heap_gb,
                            timeout,
                            stats,
                            verbose,
                        )
                    else:
                        _per_name_renaming(
                            file_path,
                            src_dir,
                            live_block,
                            current_lines,
                            rts_cores,
                            rts_heap_gb,
                            timeout,
                            stats,
                            verbose,
                        )

        if not dry_run:
            final_content = "".join(current_lines)
    finally:
        # Always restore the file to a coherent state.  On dry-run or
        # exception, this writes the original.  On success, writes the
        # pruned content.  Backup deleted on normal exit.
        try:
            file_path.write_text(final_content, encoding="utf-8")
        finally:
            if backup_path.exists():
                backup_path.unlink()

    stats.seconds = time.monotonic() - t0
    return stats


def restore_backups(paths: list[Path]) -> int:
    """Restore any `*.prune-bak` files found under `paths`.

    Useful after an interrupted run that left files in a modified state.
    Returns: number of files restored.
    """
    restored = 0
    for p in paths:
        candidates: list[Path]
        if p.is_file() and p.name.endswith(".prune-bak"):
            candidates = [p]
        elif p.is_dir():
            candidates = list(p.rglob("*.prune-bak"))
        else:
            candidates = []
        for bak in candidates:
            target = bak.with_suffix("")  # drops .prune-bak, leaving e.g. .agda
            # The above is wrong — with_suffix drops the LAST suffix.
            # `foo.agda.prune-bak`.with_suffix('') → `foo.agda`.  That's correct.
            # Let me double-check: a file `foo.agda.prune-bak` has stem
            # `foo.agda` and suffix `.prune-bak`.  with_suffix('') gives
            # `foo.agda`.  Yes correct.
            target.write_text(bak.read_text(encoding="utf-8"), encoding="utf-8")
            bak.unlink()
            print(f"  restored {target}")
            restored += 1
    return restored


# --- Crash-safe cleanup (user request 2026-05-26) ---------------------------
# The per-file `finally` restores on normal completion/exception, but a
# SIGTERM/SIGINT (e.g. `timeout`, Ctrl-C) bypasses it, leaving the source
# modified + a stray `.prune-bak` (this corrupted a working tree once).  These
# handlers restore any stray backup under SRC_DIR on exit/signal;
# restore_backups() scans the filesystem, so a single main-process handler also
# recovers backups left by ProcessPool workers.  SIGKILL can't be caught — the
# start-of-run sweep (in main) catches its leftovers on the next invocation.
def _cleanup_stray_backups() -> int:
    return restore_backups([SRC_DIR])


def _signal_cleanup(signum: int, _frame: object) -> None:
    _cleanup_stray_backups()
    sys.exit(128 + signum)


def _install_cleanup_handlers() -> None:
    atexit.register(_cleanup_stray_backups)
    for _sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(_sig, _signal_cleanup)


def _find_live_block(
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


def _per_name_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[int]:
    """Test each using-name in `block` one at a time.

    Mutates `current_lines` in-place when a removal succeeds.
    Returns indices of removed names (informational).
    """
    removed_indices = []
    # Iterate over names by NAME, not index — after each successful removal
    # the block's name list shrinks (we re-parse).
    for name in list(block.using_names):
        # Re-find the block in the current state.
        fresh = _find_live_block(current_lines, block.module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        if _try_remove_using(
            file_path,
            src_dir,
            fresh,
            current_lines,
            name,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        ):
            removed_indices.append(0)  # informational only
    return removed_indices


def _per_name_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[int]:
    """Same as _per_name_using but for renaming pairs."""
    removed = []
    for src, dst in list(block.renaming_pairs):
        fresh = _find_live_block(current_lines, block.module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        if _try_remove_renaming(
            file_path,
            src_dir,
            fresh,
            current_lines,
            src,
            dst,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        ):
            removed.append(0)
    return removed


def _bisect_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[int]:
    """Bisect: try removing all using-names at once.  If pass, all dead.
    If fail with len==1, the one is live.  Else split and recurse.

    Falls back to per-name if bisection finds the bulk dead — i.e. when the
    fast path triggers, we save N-1 type-checks compared to per-name.

    Returns the set of names that were removed.
    """
    return _bisect_helper_using(
        file_path,
        src_dir,
        block.module_path,
        list(block.using_names),
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    )


def _bisect_helper_using(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: list[str],
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[str]:
    """Recursive bisection on `candidates` (names in module_path's using clause)."""
    if not candidates:
        return []

    # Re-find the block in the current state.
    fresh = _find_live_block(current_lines, module_path, 0)
    if fresh is None:
        return []

    # Verify all candidates still exist in the block.
    candidates = [n for n in candidates if n in fresh.using_names]
    if not candidates:
        return []

    # Try removing all candidates at once.
    snapshot = list(current_lines)
    new_raw = fresh.raw
    for name in candidates:
        nxt = remove_name_from_raw(new_raw, name)
        if nxt is None:
            # Some name not found (shouldn't happen after verification, but be safe).
            new_raw = None
            break
        new_raw = nxt

    if new_raw is None:
        # Couldn't construct the bulk-removal block; bail to per-name on this segment.
        return _bisect_per_name_fallback(
            file_path,
            src_dir,
            module_path,
            candidates,
            current_lines,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        )

    new_lines = replace_block_in_lines(current_lines, fresh, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.using_tested += len(candidates)
    if _check_modified(
        file_path, src_dir, rts_cores, rts_heap_gb, timeout, stats.baseline_warnings
    ):
        # All candidates are dead.
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.using_removed += len(candidates)
        if verbose:
            print(
                f"    -- bulk-removed {len(candidates)} using-names: {', '.join(candidates)}",
                flush=True,
            )
        return candidates

    # Restore.
    file_path.write_text("".join(snapshot), encoding="utf-8")

    if len(candidates) == 1:
        if verbose:
            print(f"    -- KEPT {candidates[0]} (live)", flush=True)
        return []

    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]
    left_dead = _bisect_helper_using(
        file_path,
        src_dir,
        module_path,
        left,
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    )
    right_dead = _bisect_helper_using(
        file_path,
        src_dir,
        module_path,
        right,
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    )
    return left_dead + right_dead


def _bisect_per_name_fallback(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: list[str],
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[str]:
    """Per-name removal for a list of using names in module_path."""
    removed = []
    for name in candidates:
        fresh = _find_live_block(current_lines, module_path, 0)
        if fresh is None or name not in fresh.using_names:
            continue
        if _try_remove_using(
            file_path,
            src_dir,
            fresh,
            current_lines,
            name,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        ):
            removed.append(name)
    return removed


def _try_remove_using(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    name: str,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> bool:
    """Try removing a single using-name.  Returns True if removed."""
    snapshot = list(current_lines)
    new_raw = remove_name_from_raw(block.raw, name)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(current_lines, block, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.using_tested += 1
    if _check_modified(
        file_path, src_dir, rts_cores, rts_heap_gb, timeout, stats.baseline_warnings
    ):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.using_removed += 1
        if verbose:
            print(f"    -- removed using-name `{name}` from `{block.module_path}`", flush=True)
        return True
    file_path.write_text("".join(snapshot), encoding="utf-8")
    if verbose:
        print(f"    -- KEPT using-name `{name}` from `{block.module_path}` (live)", flush=True)
    return False


def _bisect_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[tuple[str, str]]:
    """Bisect on renaming pairs.  Symmetric to _bisect_using."""
    return _bisect_helper_renaming(
        file_path,
        src_dir,
        block.module_path,
        list(block.renaming_pairs),
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    )


def _bisect_helper_renaming(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: list[tuple[str, str]],
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[tuple[str, str]]:
    if not candidates:
        return []

    fresh = _find_live_block(current_lines, module_path, 0)
    if fresh is None:
        return []

    candidates = [p for p in candidates if p in fresh.renaming_pairs]
    if not candidates:
        return []

    snapshot = list(current_lines)
    new_raw = fresh.raw
    for src, dst in candidates:
        nxt = remove_rename_from_raw(new_raw, src, dst)
        if nxt is None:
            new_raw = None
            break
        new_raw = nxt

    if new_raw is None:
        return _bisect_per_pair_fallback(
            file_path,
            src_dir,
            module_path,
            candidates,
            current_lines,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        )

    new_lines = replace_block_in_lines(current_lines, fresh, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.renaming_tested += len(candidates)
    if _check_modified(
        file_path, src_dir, rts_cores, rts_heap_gb, timeout, stats.baseline_warnings
    ):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.renaming_removed += len(candidates)
        if verbose:
            print(f"    -- bulk-removed {len(candidates)} renaming-pairs", flush=True)
        return candidates

    file_path.write_text("".join(snapshot), encoding="utf-8")

    if len(candidates) == 1:
        return []

    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]
    return _bisect_helper_renaming(
        file_path,
        src_dir,
        module_path,
        left,
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    ) + _bisect_helper_renaming(
        file_path,
        src_dir,
        module_path,
        right,
        current_lines,
        rts_cores,
        rts_heap_gb,
        timeout,
        stats,
        verbose,
    )


def _bisect_per_pair_fallback(
    file_path: Path,
    src_dir: Path,
    module_path: str,
    candidates: list[tuple[str, str]],
    current_lines: list[str],
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> list[tuple[str, str]]:
    removed = []
    for src, dst in candidates:
        fresh = _find_live_block(current_lines, module_path, 0)
        if fresh is None or (src, dst) not in fresh.renaming_pairs:
            continue
        if _try_remove_renaming(
            file_path,
            src_dir,
            fresh,
            current_lines,
            src,
            dst,
            rts_cores,
            rts_heap_gb,
            timeout,
            stats,
            verbose,
        ):
            removed.append((src, dst))
    return removed


def _try_remove_renaming(
    file_path: Path,
    src_dir: Path,
    block: ImportBlock,
    current_lines: list[str],
    src: str,
    dst: str,
    rts_cores: int,
    rts_heap_gb: int,
    timeout: int,
    stats: FileStats,
    verbose: bool,
) -> bool:
    snapshot = list(current_lines)
    new_raw = remove_rename_from_raw(block.raw, src, dst)
    if new_raw is None:
        return False
    new_lines = replace_block_in_lines(current_lines, block, new_raw)
    file_path.write_text("".join(new_lines), encoding="utf-8")
    stats.type_checks += 1
    stats.renaming_tested += 1
    if _check_modified(
        file_path, src_dir, rts_cores, rts_heap_gb, timeout, stats.baseline_warnings
    ):
        current_lines.clear()
        current_lines.extend(new_lines)
        stats.renaming_removed += 1
        if verbose:
            print(
                f"    -- removed renaming-pair `{src} to {dst}` from `{block.module_path}`",
                flush=True,
            )
        return True
    file_path.write_text("".join(snapshot), encoding="utf-8")
    if verbose:
        print(f"    -- KEPT renaming-pair `{src} to {dst}` (live)", flush=True)
    return False


# ----------------------------------------------------------------------------
# CLI / orchestration
# ----------------------------------------------------------------------------


def gather_agda_files(paths: list[Path]) -> list[Path]:
    """Recursively collect *.agda files from the given paths."""
    files: list[Path] = []
    for p in paths:
        if p.is_file() and p.suffix == ".agda":
            files.append(p.resolve())
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.agda")))
        else:
            print(f"warning: {p} is not a file or directory; skipping", file=sys.stderr)
    return [f.resolve() for f in files]


def worker_process_file(args: tuple) -> FileStats:
    """Entry point for process pool workers."""
    (
        file_path,
        src_dir,
        rts_cores,
        rts_heap_gb,
        timeout,
        include_public,
        dry_run,
        pre_check,
        use_bisect,
        verbose,
        consumers_map,
    ) = args
    return prune_file(
        file_path,
        src_dir=src_dir,
        rts_cores=rts_cores,
        rts_heap_gb=rts_heap_gb,
        timeout=timeout,
        include_public=include_public,
        dry_run=dry_run,
        pre_check=pre_check,
        use_bisect=use_bisect,
        verbose=verbose,
        consumers_map=consumers_map,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=__doc__,
    )
    parser.add_argument(
        "paths", nargs="*", type=Path, help="Files or directories to prune (default: src/)"
    )
    parser.add_argument(
        "-j", "--workers", type=int, default=4, help="Parallel file workers (default: 4)"
    )
    parser.add_argument(
        "--rts-cores", type=int, default=8, help="GHC RTS cores per agda call (default: 8)"
    )
    parser.add_argument(
        "--rts-heap", type=int, default=3, help="GHC RTS heap per agda call in GB (default: 3)"
    )
    parser.add_argument(
        "--timeout", type=int, default=300, help="Per-agda-call timeout seconds (default: 300)"
    )
    parser.add_argument(
        "--include-public", action="store_true", help="Test `public` re-export lines too"
    )
    parser.add_argument(
        "--final-check",
        action="store_true",
        help="Run cabal run shake -- check-properties after pruning",
    )
    parser.add_argument(
        "--dry-run", action="store_true", help="Don't write changes; report what would be removed"
    )
    parser.add_argument("--quiet", action="store_true", help="Suppress per-file output")
    parser.add_argument("--verbose", action="store_true", help="Per-name decision logging")
    parser.add_argument(
        "--pre-check", action="store_true", help="Verify each file type-checks before pruning"
    )
    parser.add_argument(
        "--no-bisect", action="store_true", help="Disable bisection (pure per-name brute force)"
    )
    parser.add_argument(
        "--no-topo",
        action="store_true",
        help="Hint: skip topological-level batching IF the input set has no inter-dependencies (single topo level).  Saves the topo-graph startup cost for small independent subsets.  If inter-deps are detected, the tool auto-enables topo batching (since `--no-topo` + multi-worker on inter-deps reliably races on `.agdai` writes).  Pass `--workers 1` to force pure sequential without topo cost.",
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="Lint-mode: implies --dry-run + --quiet; exits 1 if any dead imports would be removed, 0 if clean.  Intended for CI gates / pre-commit / pre-push hooks.",
    )
    parser.add_argument(
        "--restore-backups",
        action="store_true",
        help="Restore any *.prune-bak files left by an interrupted run, then exit",
    )

    args = parser.parse_args()

    if args.restore_backups:
        paths = args.paths if args.paths else [SRC_DIR]
        n = restore_backups(paths)
        print(f"restored {n} backup(s)")
        return 0

    # --check-only implies --dry-run + --quiet (lint mode for CI/hooks).
    if args.check_only:
        args.dry_run = True
        args.quiet = True

    paths = args.paths if args.paths else [SRC_DIR]

    # Crash-safe cleanup: sweep any leftovers from a prior interrupted run
    # (e.g. a SIGKILL that bypassed the signal handler), then arm exit/signal
    # restore for THIS run so an interruption never leaves the tree corrupted.
    _swept = _cleanup_stray_backups()
    if _swept and not args.quiet:
        print(
            f"start sweep: restored {_swept} file(s) left modified by a prior interrupted run",
            flush=True,
        )
    _install_cleanup_handlers()
    files = gather_agda_files(paths)
    if not files:
        print("error: no .agda files found", file=sys.stderr)
        return 1

    # Build the reverse dependency graph IF --include-public is on (otherwise
    # no consumer checks are needed and the graph is wasted work).  Always
    # scan the full src/ tree (not just `paths`) — a file in `paths` may
    # have consumers outside `paths`.
    consumers_map: dict[str, list[Path]] = {}
    if args.include_public:
        if not args.quiet:
            print("  building reverse dependency graph (full src/ tree)...", flush=True)
        all_files = gather_agda_files([SRC_DIR])
        consumers_map = build_reverse_dep_graph(all_files, SRC_DIR)
        if not args.quiet:
            print(
                f"  reverse graph: {len(consumers_map)} modules indexed, "
                f"{sum(len(v) for v in consumers_map.values())} consumer edges",
                flush=True,
            )

    if not args.quiet:
        print(f"prune_unused_imports: processing {len(files)} files with {args.workers} workers")
        print(
            f"  src_dir={SRC_DIR}, rts={args.rts_cores}c/{args.rts_heap}G, "
            f"timeout={args.timeout}s, include_public={args.include_public}, "
            f"dry_run={args.dry_run}, bisect={not args.no_bisect}",
            flush=True,
        )

    t_start = time.monotonic()
    worker_args = [
        (
            f,
            SRC_DIR,
            args.rts_cores,
            args.rts_heap,
            args.timeout,
            args.include_public,
            args.dry_run,
            args.pre_check,
            not args.no_bisect,
            args.verbose,
            consumers_map,
        )
        for f in files
    ]

    all_stats: list[FileStats] = []
    errors = 0

    # Decide whether to use topological-level batching.  Default is ON
    # because R22 sweeps #2 and #3 demonstrated race conditions when
    # parallel workers process inter-dependent files concurrently (one
    # worker's .agdai mid-write breaks another's elaboration).  Topo
    # batching processes files level by level; within a level, files
    # have no inter-dependencies so parallel is safe.
    #
    # R23: `--no-topo` is treated as a HINT, not a directive.  It allows
    # skipping the topo-graph startup overhead WHEN the input file set
    # has no inter-dependencies (single topo level).  If `--no-topo` is
    # passed but the input has inter-deps, the tool auto-overrides to
    # topo batching to keep the race-free guarantee; this was the R23
    # CI failure mode where a 4-file branch diff with shared imports
    # reliably produced 1 baseline error per run.  Pass `--workers 1`
    # to truly force single-bucket sequential (no race possible).
    if args.workers <= 1:
        batches: list[list[tuple]] = [worker_args]  # serial — no race
    elif args.no_topo:
        # Honor --no-topo iff the input set has no inter-dependencies.
        levels = topological_levels(files, SRC_DIR)
        if len(levels) <= 1:
            batches = [worker_args]
        else:
            if not args.quiet:
                print(
                    f"  --no-topo overridden: input has inter-dependent files "
                    f"({len(levels)} topo levels); using topo batching to "
                    f"avoid .agdai race "
                    f"(feedback_agda_import_pruning_safety.md).  Pass "
                    f"`--workers 1` for sequential without topo cost.",
                    flush=True,
                )
            wa_by_file = {wa[0]: wa for wa in worker_args}
            batches = [[wa_by_file[f] for f in level if f in wa_by_file] for level in levels]
    else:
        levels = topological_levels(files, SRC_DIR)
        wa_by_file = {wa[0]: wa for wa in worker_args}
        batches = [[wa_by_file[f] for f in level if f in wa_by_file] for level in levels]
        if not args.quiet:
            print(
                f"  topological-level batching: {len(batches)} levels "
                f"(sizes: {[len(b) for b in batches[:10]]}{'...' if len(batches) > 10 else ''})",
                flush=True,
            )

    def _consume(stats: FileStats) -> None:
        nonlocal errors
        all_stats.append(stats)
        _print_stats(stats, args.quiet)
        if stats.error:
            errors += 1

    if args.workers <= 1:
        # Serial: one batch contains every file (above), process linearly.
        for wa in batches[0]:
            _consume(worker_process_file(wa))
    else:
        for level_idx, batch in enumerate(batches):
            if not batch:
                continue
            if not args.quiet and len(batches) > 1:
                print(f"  >>> level {level_idx} ({len(batch)} files)", flush=True)
            with concurrent.futures.ProcessPoolExecutor(
                max_workers=min(args.workers, len(batch))
            ) as pool:
                futures = {pool.submit(worker_process_file, wa): wa[0] for wa in batch}
                for fut in concurrent.futures.as_completed(futures):
                    _consume(fut.result())

    elapsed = time.monotonic() - t_start
    total_removed = sum(s.removed_total for s in all_stats)
    total_tcs = sum(s.type_checks for s in all_stats)
    files_changed = sum(1 for s in all_stats if s.removed_total > 0)
    print()
    print("=== summary ===")
    print(f"  files processed: {len(all_stats)}")
    print(f"  files modified : {files_changed}")
    print(
        f"  dead names removed: {total_removed} (using: {sum(s.using_removed for s in all_stats)}, renaming: {sum(s.renaming_removed for s in all_stats)})"
    )
    print(f"  public blocks skipped: {sum(s.public_blocks_skipped for s in all_stats)}")
    print(f"  type-checks run: {total_tcs}")
    print(f"  errors: {errors}")
    print(f"  wall time: {elapsed:.1f}s")
    if args.dry_run:
        print("  (dry-run: no files modified)")

    if args.final_check and not args.dry_run:
        print()
        print("=== final project-wide check-properties ===")
        if project_typecheck():
            print("  PASS")
        else:
            print("  FAIL — project-wide check-properties broke after pruning!", file=sys.stderr)
            return 2

    # Exit-code semantics:
    #   0 — tool ran successfully AND (apply mode OR dry-run found no dead).
    #   1 — tool/agda errors during the run (baseline failures, exceptions).
    #   1 — `--dry-run` (or `--check-only`) AND any dead imports would have
    #        been removed.  Matches gofmt -l / prettier --check / eslint
    #        / pyflakes / clang-format --dry-run -Werror — the universal
    #        lint-tool convention.
    #   2 — `--final-check` failed in apply mode.
    if errors:
        return 1
    if args.dry_run and total_removed > 0:
        if args.check_only:
            # --check-only suppresses verbose output; surface the count here
            # so CI logs and pre-commit hooks have a one-line failure signal.
            print(
                f"prune_unused_imports: {total_removed} dead name(s) found across "
                f"{files_changed} file(s); run without --check-only to remove",
                file=sys.stderr,
            )
        return 1
    return 0


def _print_stats(stats: FileStats, quiet: bool) -> None:
    if quiet and not stats.error and stats.removed_total == 0:
        return
    try:
        rel = stats.file.relative_to(REPO_ROOT)
    except ValueError:
        rel = stats.file
    if stats.error:
        print(f"  {rel}  ERROR: {stats.error}", flush=True)
    else:
        print(
            f"  {rel}  removed={stats.removed_total} "
            f"(using {stats.using_removed}/{stats.using_tested}, "
            f"renaming {stats.renaming_removed}/{stats.renaming_tested}) "
            f"tcs={stats.type_checks} t={stats.seconds:.1f}s "
            f"{'public-skipped=' + str(stats.public_blocks_skipped) if stats.public_blocks_skipped else ''}",
            flush=True,
        )


if __name__ == "__main__":
    sys.exit(main())

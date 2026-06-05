#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Warm-process dead-import detection via `agda --interaction-json` (ci-speed).

Supersedes a per-file `agda --html` pass:
  * ONE warm agda process loads many files (`Cmd_load` each) -> per-file agda
    startup + stdlib/interface reload is amortized across the whole batch.
  * structured JSON: every token carries `definitionSite = {filepath, position}`
    (the exact def identity) -> no HTML parse, no closure written to disk.

The prunable names come from `tools._agda_opens` (grammar-complete: every
`open` in every position — top-level, `where`/`let`, non-`import` `open M`,
open-module-macro — and every directive form).  A candidate is one UNUSED
import: its definition never reappears among the file's BODY tokens.  A type
used only in an INFERRED position (e.g. `String` behind a string literal, an
instance argument, `BitVec` in `Maybe (BitVec _)`) references no body token, so
the sieve over-flags it; the confirm pass filters it back out.

The gate flags ONLY genuinely-unused imports.  It deliberately does NOT flag
"redundant" imports — a name that IS used but also supplied by a duplicate
import or a wildcard `open` — because that is a scope/provider question the
def-id sieve cannot answer soundly, and "drop the explicit import, lean on the
wildcard" is anti-IWYU.  Provider-redundancy belongs to the future
`.agdai`-interface reader (`iInsideScope` carries the scope precisely); see
`memory/project_agda_iwyu.md`.

The confirm pass (`drive_dead` / `process_names` — remove-one + recompile
against agda ground truth) is the verdict; the sieve only narrows what is
confirmed, so confirm cost is proportional to actual deadness, not file size.

Invoke as `python -m tools.warm_dead_imports [--confirm] <relpath.agda> ...`.
"""

from __future__ import annotations

import json
import os
import queue
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NamedTuple, Self, TypedDict, cast

from tools._agda_opens import (
    OpenInfo,
    find_opens,
    open_check_names,
    public_open_names,
)
from tools._common import (
    agda_tree_lock,
    emit,
    find_executable,
    git_toplevel,
    install_restore_handlers,
    run_capture,
    track_inflight,
    untrack_inflight,
)
from tools._dead_edit import texts_without_name
from tools.prune_unused_imports import AGDA_BIN, SRC_DIR

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from pathlib import Path

AGDA = str(AGDA_BIN)
SRC = SRC_DIR

# An imported identifier — a `using (...)` entry or renaming dest, e.g. "_∷_".
type Name = str
# A src-relative Agda module path, e.g. "Aletheia/LTL/Coalgebra.agda".
type RelPath = str
# Dead-import candidates per file: each module → the names flagged removable.
type Candidates = dict[RelPath, list[Name]]
# A half-open [start, end) char-offset span (0-based) of an import block.
type CharRange = tuple[int, int]

# A definition identity: (definitionSite.filepath, definitionSite.position).
DefId = tuple[str, int]

# Max seconds of agda SILENCE (no output line) before a Cmd_load read gives up,
# so no command can hang on a silent agda.  A Cmd_load terminal arrives within
# one module's check time even cold; the cap only fires on a genuinely wedged
# process.
_LOAD_SILENCE_S = 300.0


class SweepResult(NamedTuple):
    """The warm sweep's output: per-file candidates plus per-file load times."""

    candidates: Candidates
    times: list[float]


class DefSite(TypedDict):
    """`definitionSite` of a highlighted token."""

    filepath: str
    position: int


class Token(TypedDict, total=False):
    """One highlighted token from a HighlightingInfo payload."""

    range: list[int]
    definitionSite: DefSite | None


class _ErrorPayload(TypedDict, total=False):
    """The `error` object carried by an Error DisplayInfo."""

    message: str


class _WarningEntry(TypedDict, total=False):
    """One entry in an AllGoalsWarnings `warnings` list."""

    message: str


class _Info(TypedDict, total=False):
    """A response's `info` field — HighlightingInfo tokens, an Error, or warnings.

    `payload` carries the highlighting tokens; `kind`/`error` carry a DisplayInfo
    error (the `[NotInScope]` message); `warnings` carries an AllGoalsWarnings
    list.  total=False because each response kind sets only its own keys, so
    reads go through `.get`.
    """

    payload: list[Token]
    kind: str
    error: _ErrorPayload
    warnings: list[_WarningEntry]


class _StatusInfo(TypedDict, total=False):
    """`status` field of a Status response."""

    checked: bool


class _Response(TypedDict, total=False):
    """One `agda --interaction-json` response object."""

    kind: str
    info: _Info
    status: _StatusInfo


class LoadResult(NamedTuple):
    """The outcome of one warm `Cmd_load`.

    `ok` is True iff agda reported `Status{checked:true}`.  `error` is agda's
    failure message ('' when ok) — for a narrowing that dropped a needed name,
    the `[NotInScope]` text whose `did you mean 'M.x'` hint drives completion.
    `warnings` is the AllGoalsWarnings messages — `count_semantic_warnings`
    extracts the silent-semantic-change ones (prune's dead-import guard).
    """

    tokens: list[Token]
    ok: bool
    error: str
    warnings: list[str]


# The one capability the remove-recompile core needs of a warm agda: load a file
# by path and report the result.  Passed as a bare callable (`WarmAgda.load`) so
# the core is a pure function of "can this text type-check?", unit-testable with a
# plain stub and free of any process/Protocol coupling.
type LoadFn = Callable[[str], LoadResult]


class DetectResult(TypedDict):
    """Result of `detect_dead` for one file."""

    dead: list[Name]  # the unused-sieve verdict — also the candidate set
    candidates: list[Name]  # the authoritative set to confirm (== dead)
    public_skipped: list[Name]  # `public` re-exports, never flagged
    unresolved: list[Name]  # check-names with no resolvable def-id (a blind spot)


def line_offsets(text: str) -> list[int]:
    """Cumulative 0-based char offset of the start of each line."""
    offs = [0]
    for line in text.splitlines(keepends=True):
        offs.append(offs[-1] + len(line))
    return offs


def ranged_tokens(tokens: list[Token]) -> Iterator[tuple[Token, list[int]]]:
    """Yield (token, range) for each highlighting token carrying a `range`.

    Tokens without a `range` (whitespace, layout) are skipped — the shared entry
    point both the dead-import indexer and the IWYU attributor iterate over.
    """
    for tok in tokens:
        rng = tok.get("range")
        if rng:
            yield tok, rng


def _spawn_agda() -> subprocess.Popen[str]:
    """Spawn a warm `agda --interaction-json` process; ownership returns to caller."""
    return subprocess.Popen(
        [AGDA, "--interaction-json"],
        cwd=str(SRC),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        bufsize=1,
        env={**os.environ, "GHCRTS": "-M16G -N8"},
    )


@dataclass
class _LoadState:
    """Mutable accumulator for one `Cmd_load` response stream.

    Tracks the tokens seen so far, whether `Status{checked:true}` arrived, and
    whether a `JumpToError` was observed (so the failure terminal can be told
    apart from an ordinary `Status{checked:false}`).
    """

    tokens: list[Token] = field(default_factory=list)
    ok: bool = False
    saw_error: bool = False
    error: str = ""
    warnings: list[str] = field(default_factory=list)


# Warnings that signal a SILENT semantic change — a pattern reinterpreted as a
# variable binding when a constructor leaves scope (the file still type-checks
# but its meaning changes).  Mirrors prune's `_SEMANTIC_WARNING_TAGS`.
SEMANTIC_WARNING_TAGS = ("PatternShadowsConstructor", "UnreachableClauses")


def count_semantic_warnings(warnings: list[str]) -> int:
    """Count warning messages tagged as a silent semantic change."""
    return sum(1 for w in warnings if any(tag in w for tag in SEMANTIC_WARNING_TAGS))


def _error_display_message(payload: _Response) -> str:
    """Return an Error DisplayInfo's message text, or '' if it is not one.

    A failed `Cmd_load` emits a `DisplayInfo` whose `info.kind == "Error"`
    carries the human-readable error (the `[NotInScope]` text that names the
    missing identifier) BEFORE the `JumpToError`/`Status{checked:false}` terminal.
    """
    info = payload.get("info")
    if info is None or info.get("kind") != "Error":
        return ""
    err = info.get("error")
    return err.get("message", "") if err is not None else ""


def _display_warnings(payload: _Response) -> list[str]:
    """Return an AllGoalsWarnings DisplayInfo's warning messages, or [] otherwise.

    A successful `Cmd_load` emits this after `Status{checked:true}`; the messages
    carry the warning tags (`-W[no]UnreachableClauses`, …) that
    `count_semantic_warnings` scans for the silent-semantic-change ones.
    """
    info = payload.get("info")
    if info is None or info.get("kind") != "AllGoalsWarnings":
        return []
    return [msg for w in info.get("warnings", []) if (msg := w.get("message"))]


def _parse_response(line: str) -> _Response | None:
    """Parse one agda output line into a response, or None if it is not JSON.

    Non-`{`-prefixed lines and malformed JSON both yield None so the read loop
    can simply skip them.
    """
    line = line.strip()
    if not line.startswith("{"):
        return None
    try:
        return cast("_Response", json.loads(line))
    except json.JSONDecodeError:
        return None


def _apply_load_response(payload: _Response, state: _LoadState) -> bool:
    """Fold one parsed Cmd_load response into `state`; return True at a terminal.

    Accumulates `HighlightingInfo` tokens, records `JumpToError`, and reads
    `Status`.  Returns True on either terminal — the success `InteractionPoints`,
    or the `Status{checked:false}` that follows an error — and False otherwise.
    """
    kind = payload.get("kind")
    if kind == "HighlightingInfo":
        info = payload.get("info")
        if info is not None and (tokens := info.get("payload")) is not None:
            state.tokens += tokens
    elif kind == "DisplayInfo":
        message = _error_display_message(payload)
        if message:
            state.error = message
        state.warnings += _display_warnings(payload)
    elif kind == "JumpToError":
        state.saw_error = True
    elif kind == "Status":
        status = payload.get("status")
        if status is not None and status.get("checked"):
            state.ok = True
        elif state.saw_error:
            return True  # failure terminal: Status{checked:false} after the error
    elif kind == "InteractionPoints":
        return True  # success terminal
    return False


def read_load(read_line: Callable[[], str | None]) -> _LoadState:
    """Fold Cmd_load response lines (from `read_line`) into a _LoadState.

    `read_line` returns the next line, None at EOF, and raises `queue.Empty` on
    silence (a wedged process) — silence returns the partial state (`ok` False)
    rather than hanging; EOF mid-load raises.  Pure (no process), so the
    load-terminal logic is unit-testable with a synthetic line source.
    """
    state = _LoadState()
    while True:
        try:
            line = read_line()
        except queue.Empty:
            return state  # silent past the load budget -> give up (ok False)
        if line is None:
            message = "agda --interaction-json exited unexpectedly"
            raise RuntimeError(message)
        payload = _parse_response(line)
        if payload is not None and _apply_load_response(payload, state):
            return state


class WarmAgda:
    """One long-lived `agda --interaction-json` process driven over pipes.

    Use as a context manager (`with WarmAgda() as agda: agda.load(...)`).  A
    daemon thread drains agda's stdout into a queue, so every read is
    time-bounded (`_next_line`): a command can never hang on a silent agda.
    Pipe discipline still holds: flush after every command and drain its
    responses to the terminal marker before the next.
    """

    def __init__(self) -> None:
        """Spawn the warm agda process and start its stdout reader thread."""
        self.proc: subprocess.Popen[str] = _spawn_agda()
        self._lines: queue.Queue[str | None] = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop, daemon=True)
        self._reader.start()

    def _read_loop(self) -> None:
        """Drain agda's stdout into the line queue; enqueue None as the EOF sentinel.

        Uses `iter(readline, "")` (not `for line in stream`, which read-ahead
        buffers and would stall interactive line delivery) so each response line
        is queued as it arrives.  Runs in a daemon thread for the process's life.
        """
        out = self.proc.stdout
        if out is not None:
            for line in iter(out.readline, ""):
                self._lines.put(line)
        self._lines.put(None)

    def _next_line(self, timeout: float) -> str | None:
        """Return the next agda line, or None at EOF; raise `queue.Empty` on silence.

        `queue.Empty` after `timeout` seconds of no output is how a command
        detects that agda has gone silent without sending its terminal -- the
        bound that prevents a hang.
        """
        return self._lines.get(timeout=timeout)

    def __enter__(self) -> Self:
        """Enter the context manager, returning this live process wrapper."""
        return self

    def __exit__(self, *_exc: object) -> None:
        """Exit the context manager, closing the underlying process."""
        self.close()

    def _run_load(self, abspath: str) -> _LoadState:
        """Send Cmd_load and fold responses into a _LoadState until a terminal.

        A FAILED load emits `JumpToError` + `Status{checked:false}` (no
        `InteractionPoints`); both terminals (and a wedged-process silence past
        `_LOAD_SILENCE_S`) are handled by `read_load`, so a broken or stuck file
        is reported, never hung on.
        """
        if self.proc.stdin is None:
            message = "agda --interaction-json process has no stdin pipe"
            raise RuntimeError(message)
        cmd = f'IOTCM "{abspath}" NonInteractive Direct (Cmd_load "{abspath}" [])\n'
        _ = self.proc.stdin.write(cmd)
        self.proc.stdin.flush()
        return read_load(lambda: self._next_line(_LOAD_SILENCE_S))

    def load(self, abspath: str) -> LoadResult:
        """Send Cmd_load; return the load's tokens, ok flag, and error message.

        Agda re-sends highlighting in chunks on a cold check (no warm `.agdai`),
        so the SAME token range can arrive in several `HighlightingInfo`
        messages and accumulate.  Dedup by range (keeping the last, i.e. most
        complete, token per range) so every consumer sees each token once —
        body-def-id counting must not be fooled by re-sent tokens.
        """
        state = self._run_load(abspath)
        by_range: dict[tuple[int, ...], Token] = {}
        for tok in state.tokens:
            key = tuple(tok.get("range", ()))
            if key:
                by_range[key] = tok
        return LoadResult(list(by_range.values()), state.ok, state.error, state.warnings)

    def close(self) -> None:
        """Close stdin and wait for the process to exit (kill on timeout)."""
        if self.proc.stdin is None:
            self.proc.kill()
            return
        try:
            self.proc.stdin.close()
            _ = self.proc.wait(timeout=10)
        except OSError, subprocess.TimeoutExpired:
            self.proc.kill()


class _ImportStructure(NamedTuple):
    """The import-clause structure of a file that `detect_dead` works over."""

    import_ranges: list[CharRange]  # char span of each import block
    check_names: set[Name]  # non-public names — the confirm candidates
    public_skipped: list[Name]  # `public` re-exports (never flagged — see below)


class _BodyIndex(NamedTuple):
    """The lookups `detect_dead` consumes (see its docstring)."""

    import_defid: dict[Name, DefId]  # import name → its definition identity
    body_defids: set[DefId]  # def-ids referenced anywhere in the body
    body_names_external: set[Name]  # body names whose def lives in another file
    qualified_use_files: dict[Name, set[str]]  # qualifier → files of its `q.field` uses


def _import_structure(opens: list[OpenInfo]) -> _ImportStructure:
    """Derive the clause ranges, prunable names, and public skips from the opens.

    Built from the grammar-complete open list (`tools._agda_opens.find_opens`),
    NOT just top-level `open import` blocks:
      * `import_ranges` is every directive's char span, so a token inside ANY
        open (incl. non-`import` `open M`, an open-module-macro, a local
        `where`/`let` open) is classified as an import-clause token, not a body
        use — closing the body-exclusion FN those forms had.
      * `check_names` is the prunable set (`open_check_names`): every `using`
        entry and `renaming` destination of a non-`public` open (P1-complete).
      * a `public` re-export's names are recorded as `public_skipped`, but never
        as candidates — removing one changes the file's exported surface.
    """
    return _ImportStructure(
        import_ranges=[o.span for o in opens],
        check_names=open_check_names(opens),
        public_skipped=sorted(public_open_names(opens)),
    )


def _body_index(
    text: str, tokens: list[Token], abspath: str, structure: _ImportStructure
) -> _BodyIndex:
    """Index tokens into the lookups `detect_dead` consumes.

    `import_defid` maps each non-public check-name to its definition identity;
    the external / qualified-file distinctions are the no-false-positive guards
    described in `detect_dead`.
    """
    import_defid: dict[Name, DefId] = {}
    body_defids: set[DefId] = set()
    body_names_external: set[Name] = set()
    qualified_use_files: dict[Name, set[str]] = {}
    for tok, rng in ranged_tokens(tokens):
        name = text[rng[0] - 1 : rng[1] - 1]  # Agda ranges are 1-based
        site = tok.get("definitionSite")
        defid: DefId | None = (site["filepath"], site["position"]) if site else None
        if any(s <= rng[0] - 1 < e for s, e in structure.import_ranges):  # token in import clause
            # def==None for a renaming dest / local binding: body refs point at THIS
            # token's position in THIS file -> synthesize (abspath, offset).
            if name in structure.check_names:
                import_defid.setdefault(name, defid or (abspath, rng[0]))
        elif defid is not None:  # def-less body tokens can't be import-uses
            body_defids.add(defid)
            if defid[0] != abspath:
                body_names_external.add(name)
            if "." in name:  # qualified use `q.field`
                qualified_use_files.setdefault(name.split(".", 1)[0], set()).add(defid[0])
    return _BodyIndex(import_defid, body_defids, body_names_external, qualified_use_files)


def detect_dead(text: str, tokens: list[Token], abspath: str) -> DetectResult:
    """Return one file's unused-import analysis (the dead-only sieve).

    `candidates` == `dead`: the names whose imported definition never reappears
    among the file's body tokens.  Redundant-but-used imports (duplicate /
    wildcard-supplied) are deliberately NOT flagged — see the module docstring.

    Identity model (from Agda's highlighting): a body reference's def-id is
    `(definitionSite.filepath, position)`; an imported name is ALIVE when its
    import-clause token's def-id reappears among body tokens' def-ids.  Cases:
      * mixfix (`using (_∷_)` / body `∷`): both share one def-id.
      * renaming dest (`renaming (_≟_ to _≟ₛ_)`): the DEST token has def==None,
        but body uses point at `(this-file, dest-offset)` — synthesized.
      * qualified use `n.field` (module/record/type as a qualifier): import
        def-id is n's, body `n.field` carries the FIELD's def-id — detect via
        the `n.` prefix, requiring the field's file to be the import's own.
      * re-export aliases (`[]`): decl/use def-ids differ -> exact-name fallback,
        restricted to body tokens defined OUTSIDE this file (a local shadow of
        the same name must not keep the import alive).
    No-FP bias: dead only if NONE of these say alive — the confirm pass is the
    final ground-truth arbiter.
    """
    structure = _import_structure(find_opens(text))
    index = _body_index(text, tokens, abspath, structure)
    import_defid = index.import_defid

    def alive(name: Name, defid: DefId) -> bool:
        if defid in index.body_defids:  # precise: the import's OWN def is used
            return True
        if name in index.body_names_external:  # re-export alias (def-ids differ across files)
            return True
        # qualified use `name.field` whose field is defined in the import's module
        return defid[0] in index.qualified_use_files.get(name, set())

    dead = sorted(n for n, d in import_defid.items() if not alive(n, d))
    return {
        "dead": dead,
        "candidates": dead,
        "public_skipped": structure.public_skipped,
        "unresolved": sorted(structure.check_names - set(import_defid)),
    }


def import_defids(text: str, tokens: list[Token], abspath: str) -> dict[Name, DefId]:
    """Map each prunable import name to the definition identity its clause token carries.

    The (file, position) def-id is the SAME coordinate the IWYU `.agdai` reader
    reports for used names, so a name is dead iff its def-id is absent from the
    reader's elaboration-complete used-set.  Shared with :mod:`tools.iwyu_reader`
    (the reader-vs-recompile-confirm equivalence check).
    """
    structure = _import_structure(find_opens(text))
    return _body_index(text, tokens, abspath, structure).import_defid


# ---- confirmation: authoritatively classify candidates by removing JUST each
# ---- one and asking agda (ground truth) — NOT the O(all-imports) brute-force.


def _first_removable(load: LoadFn, path: Path, name: Name, baseline: int, *, commit: bool) -> bool:
    """Try each occurrence-variant of `name`; act on the FIRST that type-checks.

    Reads `path`'s CURRENT text (so the apply fixpoint always sees prior
    commits), then `texts_without_name` yields one variant per open `name`
    appears in.  On the first variant that loads `ok` within `baseline`
    silent-semantic warnings (prune's guard), either COMMIT it (leave the edit on
    disk, ``commit=True``) or RESTORE it (probe only, ``commit=False``) and
    return True.  Any non-committed write — a failed variant or an exception — is
    restored, so it is crash-safe (registered via ``track_inflight``).  Returns
    False when no variant is removable.
    """
    original = path.read_text(encoding="utf-8")
    for modified in texts_without_name(original, name):
        kept = False
        try:
            track_inflight(str(path), original)
            _ = path.write_text(modified, encoding="utf-8")
            result = load(str(path))
            if result.ok and count_semantic_warnings(result.warnings) <= baseline:
                kept = commit
                return True
        finally:
            if not kept:
                _ = path.write_text(original, encoding="utf-8")  # restore
            untrack_inflight(str(path))
    return False


def remove_and_reload(load: LoadFn, rel: RelPath, name: Name, baseline: int, *, keep: bool) -> bool:
    """Decide (and, with ``keep``, perform) the removal of dead `name` from `rel`.

    The shared remove-recompile primitive of the confirm gate and the cleanup
    tool.  ``keep=False`` (the confirm gate) PROBES — is some occurrence-variant
    still type-checking within `baseline` warnings? — and always restores; True
    means "dead".  ``keep=True`` (the cleanup, :mod:`tools.warm_apply`) REMOVES
    EVERY dead occurrence: each commit is recompile-validated, then the file is
    re-read and the next occurrence tried, to a fixpoint.  Clearing all copies
    (not just the first) is what makes a cleaned file pass the gate — a name dead
    in several opens (e.g. a where-block local repeated per clause) must lose
    them all, or the gate would flag its own output.  Sound for the mixed case
    too: a copy that is actually USED fails to type-check, so its variant is
    restored and only the genuinely-dead copies go.  Terminating: each commit
    strictly drops one occurrence.  Returns True iff `name` was dead (probed
    removable, or ≥1 occurrence removed).
    """
    path = SRC / rel
    if not keep:
        return _first_removable(load, path, name, baseline, commit=False)
    removed = False
    while _first_removable(load, path, name, baseline, commit=True):
        removed = True
    return removed


def process_names(
    agda: WarmAgda, rel: RelPath, names: list[Name], *, keep: bool
) -> tuple[list[Name], list[Name]]:
    """Run `remove_and_reload` over each name; partition into (dead, alive).

    The shared per-file driver of confirm (`keep=False`, restores) and apply
    (`keep=True`, removes for good).  ``baseline`` is the file's own
    semantic-warning count, so a pre-existing warning is never counted as new.
    Crash-safe: atexit/SIGINT/SIGTERM handlers plus each removal's own restore.
    """
    install_restore_handlers()
    baseline = count_semantic_warnings(agda.load(str(SRC / rel)).warnings)
    dead: list[Name] = []
    alive: list[Name] = []
    for name in names:
        is_dead = remove_and_reload(agda.load, rel, name, baseline, keep=keep)
        (dead if is_dead else alive).append(name)
    return dead, alive


def drive_dead(
    agda: WarmAgda,
    candidates: Candidates,
    *,
    keep: bool,
    verb: str,
    fmt: Callable[[list[Name], list[Name]], str],
) -> int:
    """Per-file driver: process each file's candidates and report; return the total.

    The shared loop of the confirm gate (``keep=False``, restores) and the
    cleanup tool (``keep=True``, :mod:`tools.warm_apply`).  ``fmt(dead, alive)``
    renders each per-file line, so the two tools keep their own wording
    (TRULY-DEAD vs REMOVED) over one shared remove-recompile pass
    (:func:`process_names`).
    """
    ncand = sum(len(v) for v in candidates.values())
    emit(f"=== {verb}: {ncand} candidate(s) via remove + warm recompile ===")
    start = time.time()
    total = 0
    for rel, cands in candidates.items():
        dead, alive = process_names(agda, rel, cands, keep=keep)
        total += len(dead)
        emit(f"  {rel}: {fmt(dead, alive)}")
    emit(f"=== {verb}: {total} of {ncand} in {time.time() - start:.1f}s ===")
    return total


def _result_extra(result: DetectResult) -> str:
    """Build the per-file diagnostic suffix (public-skipped / unresolved)."""
    parts: list[str] = []
    if result["public_skipped"]:
        parts.append(f"public-skipped={len(result['public_skipped'])}")
    if result["unresolved"]:
        parts.append(f"unresolved={result['unresolved']}")
    return ("  " + "  ".join(parts)) if parts else ""


def sweep(agda: WarmAgda, files: list[RelPath]) -> SweepResult:
    """Warm-load each file, print its per-file result, return the SweepResult."""
    candidates: Candidates = {}
    times: list[float] = []
    for i, rel in enumerate(files, 1):
        abspath = str(SRC / rel)
        text = (SRC / rel).read_text(encoding="utf-8")
        start = time.time()
        loaded = agda.load(abspath)
        dt = time.time() - start
        times.append(dt)
        if not loaded.ok:
            emit(
                f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  ⚠️ LOAD FAILED "
                + "(no Status checked:true — agda could not check it)"
            )
            continue
        result = detect_dead(text, loaded.tokens, abspath)
        cands = result["candidates"]
        if cands:
            candidates[rel] = cands
        emit(
            f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  tokens={len(loaded.tokens)} "
            + f"CANDIDATES={cands or '—'}{_result_extra(result)}"
        )
    return SweepResult(candidates, times)


def _print_summary(
    files: list[RelPath], times: list[float], candidates: Candidates, total: float
) -> None:
    """Print the warm-sweep timing + candidate count."""
    ncand = sum(len(v) for v in candidates.values())
    if len(times) > 1:
        warm = sum(times[1:]) / len(times[1:])
        emit(
            f"--- warm sweep: {len(files)} files {total:.1f}s "
            + f"(file1={times[0]:.1f}s cold, mean 2..N={warm:.1f}s) — "
            + f"{ncand} candidate(s) in {len(candidates)} file(s) ---"
        )
    else:
        emit(f"--- 1 file: {total:.1f}s — {ncand} candidate(s) ---")


def _confirm_all(agda: WarmAgda, candidates: Candidates) -> int:
    """Confirm every candidate (remove-one + warm-recompile, restoring); dead count."""
    return drive_dead(
        agda,
        candidates,
        keep=False,
        verb="confirm",
        fmt=lambda dead, alive: f"TRULY-DEAD={dead or '—'}  fp/used={alive or '—'}",
    )


def all_agda_files() -> list[RelPath]:
    """Return every ``.agda`` under ``src/``, src-relative (whole-tree mode)."""
    return sorted(str(p.relative_to(SRC)) for p in SRC.rglob("*.agda"))


def changed_agda_files() -> list[RelPath]:
    """Return ``.agda`` files changed vs the merge-base with ``main``, src-relative.

    The per-push scope (``git diff --name-only main...HEAD -- src/``).  Sound for
    a name whose last use was removed in a CHANGED file; a name made dead by an
    edit in an UNCHANGED file (cross-file deadness) is caught only by the periodic
    whole-tree (``--all``) sweep — so the per-push gate is complete *modulo* that
    sweep, not on its own.  A git failure (e.g. no ``main`` ref) is surfaced and
    yields an empty scope rather than a silent pass.
    """
    root = git_toplevel()
    result = run_capture(
        [
            find_executable("git"),
            "-C",
            str(root),
            "diff",
            "--name-only",
            "main...HEAD",
            "--",
            "src/",
        ],
    )
    if result.returncode != 0:
        emit("dead-import gate: could not diff vs main (rely on the periodic --all sweep)")
        return []
    rels: list[RelPath] = []
    for line in result.stdout.splitlines():
        if not line.endswith(".agda"):
            continue
        try:
            rels.append(str((root / line).relative_to(SRC)))
        except ValueError:
            continue
    return sorted(rels)


def select_files(args: list[str]) -> list[RelPath] | None:
    """Resolve the scoped file set from the mode flags; None signals a usage error.

    ``--all`` = whole tree (onboarding / periodic).  ``--diff`` = files changed
    vs ``main`` (per-push).  Otherwise the explicit ``<relpath.agda> …`` args.
    Unlike the legacy prune gate — which silently ``exit 0``s past a 30-file
    threshold (a false negative) — there is NO file-count skip here: the warm
    sieve is fast enough (~0.6 s/file) to run on every scoped file.
    """
    if "--all" in args:
        files = all_agda_files()
        emit(f"dead-import gate: whole tree — {len(files)} file(s)")
        return files
    if "--diff" in args:
        files = changed_agda_files()
        emit(f"dead-import gate: {len(files)} .agda file(s) changed vs main")
        return files
    explicit = [a for a in args if not a.startswith("--")]
    if not explicit:
        emit("usage: warm_dead_imports [--confirm|--apply] (--all | --diff | FILE.agda ...)")
        return None
    return explicit


def run_warm_tool(args: list[str], action: Callable[[WarmAgda, SweepResult], int]) -> int:
    """Resolve --all/--diff/explicit scope, warm-sweep, then run ``action``.

    The shared CLI shell of the gate (:mod:`tools.warm_dead_imports`) and the
    cleanup (:mod:`tools.warm_apply`): it handles scope selection (usage error →
    exit 2; empty scope → exit 0 no-op), the agda-tree lock + warm process, and
    the per-sweep summary, then delegates the per-tool work to
    ``action(agda, swept)`` whose return value becomes the exit code.
    """
    files = select_files(args)
    if files is None:
        return 2
    if not files:
        return 0  # nothing in scope (e.g. --diff with no .agda change): a true no-op
    start = time.time()
    with agda_tree_lock(), WarmAgda() as agda:
        swept = sweep(agda, files)
        _print_summary(files, swept.times, swept.candidates, time.time() - start)
        return action(agda, swept)


def main() -> int:
    """Warm-sweep modules for dead-import candidates; --confirm verifies (gate mode).

    Sieve candidates = UNUSED-by-def-id names only (no duplicate / wildcard
    speculation — see the module docstring).  With --confirm, each is remove-one
    + warm-recompiled (ground truth, filtering inferred-use false positives);
    exits 1 iff any are confirmed dead — so --confirm is the blocking gate, the
    bare sieve is a fast report.  (To REMOVE confirmed-dead imports in place, use
    the sibling cleanup tool ``python -m tools.warm_apply``.)

    File scope (no silent skip): ``--all`` (whole tree) / ``--diff`` (changed vs
    main) / explicit paths.  ``--diff`` with no .agda change is a genuine no-op
    (exit 0): nothing in scope, not a skipped check.
    """
    do_confirm = "--confirm" in sys.argv[1:]

    def action(agda: WarmAgda, swept: SweepResult) -> int:
        if do_confirm and swept.candidates:
            return 1 if _confirm_all(agda, swept.candidates) else 0
        return 0

    return run_warm_tool(sys.argv[1:], action)


if __name__ == "__main__":
    sys.exit(main())

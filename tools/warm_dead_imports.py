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
open-module-macro — and every directive form), so the candidate set is
FN-complete by construction.  A candidate is generated three ways:
  * UNUSED — its definition never reappears among the file's BODY tokens.  A
    type used only in an INFERRED position (e.g. `BitVec` in `Maybe (BitVec _)`)
    references no body token, so this over-flags; `confirm_candidates` filters it.
  * DUPLICATE — its def-id is imported >=2 times (one copy is redundant).
  * WILDCARD-REDUNDANT — a wildcard open (`open M` / `open import M` with no
    `using`) already supplies it (`show_module_contents` membership).

`confirm_candidates` (remove-one + recompile against agda ground truth) is the
verdict; the sieve only narrows what is confirmed, so confirm cost is
proportional to actual deadness, not file size.

Invoke as `python -m tools.warm_dead_imports [--confirm] <relpath.agda> ...`.
"""

from __future__ import annotations

import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NamedTuple, Self, TypedDict, cast

from tools._agda_opens import (
    ModuleContents,
    ModulePath,
    OpenInfo,
    find_opens,
    open_check_names,
    public_open_names,
    redundant_names,
)
from tools._common import (
    agda_tree_lock,
    emit,
    install_restore_handlers,
    track_inflight,
    untrack_inflight,
)
from tools.prune_unused_imports import (
    AGDA_BIN,
    SRC_DIR,
    remove_name_from_raw,
    remove_rename_from_raw,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator

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

# A def-id imported this many times (or more) is a redundant duplicate: removing
# one copy leaves the others in scope, so the extra import is dead.
_MIN_DUP_OCCURRENCES = 2

# Max seconds of agda SILENCE (no output line) before a read gives up, so no
# command can hang on a silent agda.  A Cmd_load terminal arrives within one
# module's check time even cold; the cap only fires on a genuinely wedged
# process.  Cmd_show_module_contents answers an UNRESOLVABLE module with total
# silence (verified) -- the short cap turns that into a None verdict, fast.
_LOAD_SILENCE_S = 300.0
_SMC_SILENCE_S = 20.0


class ConfirmResult(NamedTuple):
    """How a file's candidates split once authoritatively confirmed.

    `truly_dead` removed cleanly (the file still type-checks with no new
    silent-semantic-change warning); `false_positives` turned out to be needed
    (e.g. used only in an inferred position the sieve could not see).
    """

    truly_dead: list[Name]
    false_positives: list[Name]


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


class _ModuleEntry(TypedDict, total=False):
    """One entry in a `Cmd_show_module_contents` ModuleContents listing."""

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


class DetectResult(TypedDict):
    """Result of `detect_dead` for one file."""

    dead: list[Name]
    dead_defid_only: list[Name]
    duplicates: list[Name]
    wildcard_redundant: list[Name]  # a wildcard open in scope also supplies these
    candidates: list[Name]  # the authoritative set to confirm (FN-complete)
    public_skipped: list[Name]
    unresolved: list[Name]


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


def read_module_contents(read_line: Callable[[], str | None]) -> list[Name] | None:
    """Fold Cmd_show_module_contents response lines into names, or None.

    `read_line` returns the next line, None at EOF, and raises `queue.Empty` on
    the SILENCE an unresolvable module produces; both map to None (unresolvable),
    as does an Error / wrong-terminal display.  A ModuleContents display yields
    its full export names ([] for a genuinely empty module).  Pure, so the
    terminal/None logic is unit-testable without a process.
    """
    while True:
        try:
            line = read_line()
        except queue.Empty:
            return None  # unresolvable module -> agda answers with silence
        if line is None:
            return None  # process exited
        payload = _parse_response(line)
        if payload is None:
            continue
        kind = payload.get("kind")
        if kind in ("JumpToError", "InteractionPoints"):
            return None  # errored / wrong terminal — module not enumerable
        if kind != "DisplayInfo":
            continue
        info = cast("_ModuleContentsResponse", payload).get("info")
        if info is None or info.get("kind") != "ModuleContents":
            return None
        return [name for entry in info.get("contents", []) if (name := entry.get("name"))]


class WarmAgda:
    """One long-lived `agda --interaction-json` process driven over pipes.

    Use as a context manager (`with WarmAgda() as agda: agda.load(...)`).  A
    daemon thread drains agda's stdout into a queue, so every read is
    time-bounded (`_next_line`): a command can never hang on a silent agda --
    notably `Cmd_show_module_contents_toplevel`, which answers an unresolvable
    module with TOTAL silence.  Pipe discipline still holds: flush after every
    command and drain its responses to the terminal marker before the next.
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
        detects that agda has gone silent without sending its terminal (e.g. an
        unresolvable `show_module_contents`) -- the bound that prevents a hang.
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
        occurrence-counting (duplicate-import detection) must not be fooled by
        re-sent tokens.
        """
        state = self._run_load(abspath)
        by_range: dict[tuple[int, ...], Token] = {}
        for tok in state.tokens:
            key = tuple(tok.get("range", ()))
            if key:
                by_range[key] = tok
        return LoadResult(list(by_range.values()), state.ok, state.error, state.warnings)

    def show_module_contents(self, abspath: str, module: str) -> list[Name] | None:
        """Return `module`'s full export names, or None if it cannot be enumerated.

        Sends `Cmd_show_module_contents_toplevel`; `module` must be in scope in
        the loaded `abspath`.  The result's full mixfix names (`_⊕_`, including
        re-exports) are the wildcard provided-set the redundancy check needs.

        Distinguishes UNRESOLVABLE (returns None) from a genuinely EMPTY module
        (returns []), so the caller maps None to the conservative confirm-all
        fallback rather than to "supplies nothing".  Unresolvable is detected two
        ways: an Error / wrong-terminal display, OR -- the common case, verified
        empirically -- agda answering with TOTAL SILENCE, caught by the
        `_SMC_SILENCE_S` read bound.  Either way the query cannot hang.
        """
        if self.proc.stdin is None:
            message = "agda --interaction-json process has no stdin pipe"
            raise RuntimeError(message)
        cmd = f'IOTCM "{abspath}" None Direct (Cmd_show_module_contents_toplevel AsIs "{module}")\n'
        _ = self.proc.stdin.write(cmd)
        self.proc.stdin.flush()
        return read_module_contents(lambda: self._next_line(_SMC_SILENCE_S))

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
    all_names: set[Name]  # public + non-public — for unique-provider counting
    public_skipped: list[Name]  # `public` re-exports (never flagged — see below)


class _BodyIndex(NamedTuple):
    """The lookups `detect_dead` consumes (see its docstring)."""

    import_defid: dict[Name, DefId]  # import name → its definition identity
    import_occurrences: list[tuple[Name, DefId]]  # EVERY import-clause token (name, def-id)
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
      * a `public` re-export's names are recorded as PROVIDERS (in `all_names`,
        for duplicate counting) and as `public_skipped`, but never as candidates
        — removing one changes the file's exported surface.
    """
    check_names = open_check_names(opens)
    public = public_open_names(opens)
    return _ImportStructure(
        import_ranges=[o.span for o in opens],
        check_names=check_names,
        all_names=check_names | public,
        public_skipped=sorted(public),
    )


def _body_index(
    text: str, tokens: list[Token], abspath: str, structure: _ImportStructure
) -> _BodyIndex:
    """Index tokens into the lookups `detect_dead` consumes.

    Occurrences are recorded for ALL import names (public + non-public) so the
    unique-provider count sees a public re-export too; `import_defid` (the
    confirm candidates) is non-public only.  The external / qualified-file
    distinctions are the no-false-positive guards described in `detect_dead`.
    """
    import_defid: dict[Name, DefId] = {}
    import_occurrences: list[tuple[Name, DefId]] = []
    body_defids: set[DefId] = set()
    body_names_external: set[Name] = set()
    qualified_use_files: dict[Name, set[str]] = {}
    for tok, rng in ranged_tokens(tokens):
        name = text[rng[0] - 1 : rng[1] - 1]  # Agda ranges are 1-based
        site = tok.get("definitionSite")
        defid: DefId | None = (site["filepath"], site["position"]) if site else None
        if any(s <= rng[0] - 1 < e for s, e in structure.import_ranges):  # token in import clause
            # def==None for a renaming dest / local binding: body refs point at THIS
            # token's position in THIS file -> synthesize (abspath, offset), which is
            # per-occurrence-unique so a rename never groups as a duplicate.
            if name in structure.all_names:
                occ = defid or (abspath, rng[0])
                import_occurrences.append((name, occ))  # public + non-public: uniqueness count
                if name in structure.check_names:
                    import_defid.setdefault(name, occ)  # non-public: a confirm candidate
        elif defid is not None:  # def-less body tokens can't be import-uses
            body_defids.add(defid)
            if defid[0] != abspath:
                body_names_external.add(name)
            if "." in name:  # qualified use `q.field`
                qualified_use_files.setdefault(name.split(".", 1)[0], set()).add(defid[0])
    return _BodyIndex(
        import_defid, import_occurrences, body_defids, body_names_external, qualified_use_files
    )


def _duplicate_names(occurrences: list[tuple[Name, DefId]], check_names: set[Name]) -> list[Name]:
    """Non-public names whose def-id is imported >=2 times (a redundant duplicate).

    Grouping by DEF-ID (not name), so overloaded `[]`/`_∷_` (distinct def-ids)
    are not falsely paired while a same-entity alias still is.  Occurrences
    include public re-exports (another provider), so a non-public import made
    redundant by a public one is caught; only non-public names are returned (the
    confirm candidates) — exactly the L178 `length` case the per-name
    `import_defid` dict collapses away.
    """
    occ_count: dict[DefId, int] = {}
    for _name, defid in occurrences:
        occ_count[defid] = occ_count.get(defid, 0) + 1
    return sorted(
        {n for n, d in occurrences if occ_count[d] >= _MIN_DUP_OCCURRENCES and n in check_names}
    )


def detect_dead(
    text: str,
    tokens: list[Token],
    abspath: str,
    module_contents: ModuleContents,
) -> DetectResult:
    """Return one file's dead / duplicate / wildcard-redundant / candidate analysis.

    `candidates` is the authoritative set to confirm.  It is FN-complete by
    construction: a dead import is removable iff its name is either UNUSED, a
    same-entity DUPLICATE, or already supplied by a WILDCARD open — the three
    components, each reported for insight:
      * `dead` — the unused-sieve (def-id never reappears in the body).
      * `duplicates` — a def-id imported >=2 times (`_duplicate_names`).
      * `wildcard_redundant` — supplied by a non-`using` open's
        `show_module_contents` (`tools._agda_opens.redundant_names`, fed
        `module_contents`); an unresolvable wildcard makes every check-name a
        candidate (the sound confirm-all fallback that replaced disqualification).

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
    No-FP bias: dead only if NONE of these say alive.  `dead_defid_only` drops
    the name/prefix fallbacks (reported, to show what they catch).
    """
    opens = find_opens(text)
    structure = _import_structure(opens)
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
    dead_defid_only = sorted(n for n, d in import_defid.items() if d not in index.body_defids)
    duplicates = _duplicate_names(index.import_occurrences, structure.check_names)
    wildcard_redundant = sorted(redundant_names(opens, module_contents))
    unresolved = sorted(structure.check_names - set(import_defid))
    candidates = sorted(set(dead) | set(duplicates) | set(wildcard_redundant))
    return {
        "dead": dead,
        "dead_defid_only": dead_defid_only,
        "duplicates": duplicates,
        "wildcard_redundant": wildcard_redundant,
        "candidates": candidates,
        "public_skipped": structure.public_skipped,
        "unresolved": unresolved,
    }


# ---- confirmation: authoritatively classify candidates by removing JUST each
# ---- one and asking agda (ground truth) — NOT the O(all-imports) brute-force.


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


def _confirm_one(agda: WarmAgda, rel: RelPath, name: Name, original: str, baseline: int) -> bool:
    """Remove `name` from each block holding it, warm-reload; dead iff ANY succeeds.

    Dead ⇔ for SOME occurrence, the file still type-checks (`ok`) with no new
    silent-semantic-change warning beyond `baseline` (prune's guard — a removed
    constructor reinterpreting a pattern as a variable binding).  Trying every
    occurrence is what catches a redundant duplicate that is not the first copy.
    ALWAYS restores the original content after each attempt, even on failure.
    """
    path = SRC / rel
    for modified in texts_without_name(original, name):
        try:
            track_inflight(str(path), original)
            _ = path.write_text(modified, encoding="utf-8")
            result = agda.load(str(path))
            if result.ok and count_semantic_warnings(result.warnings) <= baseline:
                return True  # this occurrence is removable -> the import is dead
        finally:
            _ = path.write_text(original, encoding="utf-8")  # ALWAYS restore
            untrack_inflight(str(path))
    return False


def confirm_candidates(agda: WarmAgda, rel: RelPath, names: list[Name]) -> ConfirmResult:
    """Classify each candidate by removing JUST it and warm-recompiling.

    The baseline is the file's own semantic-warning count, so a pre-existing
    warning is not counted as new.  Crash-safe: per-candidate finally +
    atexit/SIGINT/SIGTERM handlers restore the file.
    """
    install_restore_handlers()
    original = (SRC / rel).read_text(encoding="utf-8")
    baseline = count_semantic_warnings(agda.load(str(SRC / rel)).warnings)
    truly_dead: list[Name] = []
    false_positives: list[Name] = []
    for name in names:
        if _confirm_one(agda, rel, name, original, baseline):
            truly_dead.append(name)
        else:
            false_positives.append(name)
    return ConfirmResult(truly_dead, false_positives)


def _module_contents_for_file(
    agda: WarmAgda,
    abspath: str,
    opens: list[OpenInfo],
    import_cache: dict[ModulePath, list[Name]],
) -> dict[ModulePath, list[Name]]:
    """Query `show_module_contents` for each wildcard open's module.

    A WILDCARD open (`is_open`, no `using`) needs its module's exports to decide
    wildcard-redundancy.  A globally-pathed `open import M` is cached across
    files (its exports are stable), but a non-`import` `open M` / `open R r` /
    `open module N = …` resolves in the LOADED file's scope, so it is queried per
    file and NEVER cached under its possibly-file-local name (caching it could
    return another file's same-named module — an FN).  An unresolvable module is
    omitted, so `redundant_names` takes its conservative confirm-all fallback.
    """
    contents: dict[ModulePath, list[Name]] = {}
    for open_info in opens:
        if not open_info.is_open or open_info.has_using or not open_info.module:
            continue
        module = open_info.module
        if open_info.is_import:
            if module not in import_cache:
                resolved = agda.show_module_contents(abspath, module)
                if resolved is not None:
                    import_cache[module] = resolved
            if module in import_cache:
                contents[module] = import_cache[module]
        else:
            resolved = agda.show_module_contents(abspath, module)
            if resolved is not None:
                contents[module] = resolved
    return contents


def _result_extra(result: DetectResult) -> str:
    """Build the per-file diagnostic suffix (duplicates / redundant / skipped)."""
    parts: list[str] = []
    if result["duplicates"]:
        parts.append(f"duplicates={result['duplicates']}")
    if result["wildcard_redundant"]:
        parts.append(f"wildcard-redundant={result['wildcard_redundant']}")
    if result["public_skipped"]:
        parts.append(f"public-skipped={len(result['public_skipped'])}")
    if result["unresolved"]:
        parts.append(f"unresolved={result['unresolved']}")
    return ("  " + "  ".join(parts)) if parts else ""


def _sweep(agda: WarmAgda, files: list[RelPath]) -> SweepResult:
    """Warm-load each file, print its per-file result, return the SweepResult."""
    candidates: Candidates = {}
    times: list[float] = []
    import_cache: dict[ModulePath, list[Name]] = {}  # globally-pathed exports, reused across files
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
        module_contents = _module_contents_for_file(agda, abspath, find_opens(text), import_cache)
        result = detect_dead(text, loaded.tokens, abspath, module_contents)
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
    """Confirm every candidate (remove-one + warm-recompile); return the dead count."""
    ncand = sum(len(v) for v in candidates.values())
    emit(f"=== confirming {ncand} candidate(s): remove-one + warm recompile (ground truth) ===")
    start = time.time()
    n_dead = 0
    for rel, cands in candidates.items():
        confirmed = confirm_candidates(agda, rel, cands)
        n_dead += len(confirmed.truly_dead)
        emit(
            f"  {rel}: TRULY-DEAD={confirmed.truly_dead or '—'}  "
            + f"fp/used={confirmed.false_positives or '—'}"
        )
    emit(f"=== confirm: {n_dead} truly-dead of {ncand} in {time.time() - start:.1f}s ===")
    return n_dead


def main() -> int:
    """Warm-sweep modules for dead-import candidates; --confirm verifies (gate mode).

    Sieve candidates = unused-by-def-id names, plus structural duplicates (a
    def-id imported twice or more).  With --confirm, each is remove-one +
    warm-recompiled (ground truth, filtering inferred-use false positives); exits
    1 iff any are confirmed dead — so --confirm is the blocking gate, the bare
    sieve is a fast report.
    """
    args = sys.argv[1:]
    do_confirm = "--confirm" in args
    files = [a for a in args if not a.startswith("--")]
    if not files:
        emit("usage: python -m tools.warm_dead_imports [--confirm] <relpath.agda> [...]")
        return 2
    start = time.time()
    n_dead = 0
    with agda_tree_lock(), WarmAgda() as agda:
        swept = _sweep(agda, files)
        _print_summary(files, swept.times, swept.candidates, time.time() - start)
        if do_confirm and swept.candidates:
            n_dead = _confirm_all(agda, swept.candidates)
    return 1 if (do_confirm and n_dead) else 0


if __name__ == "__main__":
    sys.exit(main())

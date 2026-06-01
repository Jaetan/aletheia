#!/usr/bin/env python3
"""PROTOTYPE (ci-speed branch): warm-process dead-import detection via `agda --interaction-json`.

Supersedes a per-file `agda --html` pass:
  * ONE warm agda process loads many files (`Cmd_load` each) -> per-file agda
    startup + stdlib/interface reload is amortized across the whole batch.
  * structured JSON: every token carries `definitionSite = {filepath, position}`
    (the exact def identity) -> no HTML parse, no closure written to disk.
  * reuses tools.prune_unused_imports.parse_imports (multi-line/public/renaming)
    and its portable repo-root / agda-binary discovery.

DEAD = a checked import name whose DEFINITION never reappears among the file's
BODY tokens.  This is a fast CANDIDATE generator, NOT a standalone pruner: a type
used only in INFERRED positions (e.g. `BitVec` in `Maybe (BitVec _)`) references
no body token, so it is over-flagged.  `confirm_candidates` (remove-one +
recompile) filters those against agda ground truth.

Invoke as `python -m tools.warm_dead_imports [--confirm] <relpath.agda> ...`.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NamedTuple, Self, TypedDict, cast

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
    parse_imports,
    remove_name_from_raw,
    remove_rename_from_raw,
    replace_block_in_lines,
)

if TYPE_CHECKING:
    from collections.abc import Iterator

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
    candidates: list[Name]  # the authoritative set to confirm (FN-complete)
    disqualified: bool  # file has an unmodeled-scope open -> all in-body confirmed
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


class WarmAgda:
    """One long-lived `agda --interaction-json` process driven over pipes.

    Use as a context manager (`with WarmAgda() as agda: agda.load(...)`).  Pipe
    discipline (deadlock-critical): line-buffered text pipes, flush after every
    command, and drain a command's responses fully (to the terminal marker)
    before sending the next.
    """

    def __init__(self) -> None:
        """Spawn the warm `agda --interaction-json` process."""
        self.proc: subprocess.Popen[str] = _spawn_agda()

    def __enter__(self) -> Self:
        """Enter the context manager, returning this live process wrapper."""
        return self

    def __exit__(self, *_exc: object) -> None:
        """Exit the context manager, closing the underlying process."""
        self.close()

    @staticmethod
    def _apply_response(payload: _Response, state: _LoadState) -> bool:
        """Fold one parsed response into `state`; return True at a terminal.

        Accumulates `HighlightingInfo` tokens, records `JumpToError`, and reads
        `Status`.  Returns True on either terminal — the success
        `InteractionPoints`, or the `Status{checked:false}` that follows an
        error — and False otherwise.
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

    def _run_load(self, abspath: str) -> _LoadState:
        """Send Cmd_load and fold responses into a _LoadState until a terminal.

        Collects HighlightingInfo tokens and an Error DisplayInfo's message.  A
        FAILED load emits `JumpToError` and ends on `Status{checked:false}` (no
        `InteractionPoints`), so both terminals are handled — a broken file is
        reported, not hung on.
        """
        if self.proc.stdin is None or self.proc.stdout is None:
            message = "agda --interaction-json process has no stdin/stdout pipe"
            raise RuntimeError(message)
        cmd = f'IOTCM "{abspath}" NonInteractive Direct (Cmd_load "{abspath}" [])\n'
        _ = self.proc.stdin.write(cmd)
        self.proc.stdin.flush()
        state = _LoadState()
        while True:
            line = self.proc.stdout.readline()
            if not line:
                message = "agda --interaction-json exited unexpectedly"
                raise RuntimeError(message)
            payload = _parse_response(line)
            if payload is not None and self._apply_response(payload, state):
                break
        return state

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

    def close(self) -> None:
        """Close stdin and wait for the process to exit (kill on timeout)."""
        if self.proc.stdin is None:
            self.proc.kill()
            return
        try:
            self.proc.stdin.close()
            _ = self.proc.wait(timeout=10)
        except (OSError, subprocess.TimeoutExpired):
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


def _import_structure(text: str) -> _ImportStructure:
    """Parse import blocks into the clause ranges, names-to-check, and public skips.

    `using (module X)` contributes `X` (used qualified); renaming dests are
    in-scope; `public` re-export blocks are skipped (their only uses are
    downstream — flagging them would let a prune break the consumer's build).
    """
    blocks = parse_imports(text)
    offs = line_offsets(text)
    import_ranges: list[CharRange] = []
    check_names: set[Name] = set()
    all_names: set[Name] = set()
    public_skipped: list[Name] = []
    for blk in blocks:
        start = offs[blk.line_start]
        end = offs[blk.line_end + 1] if blk.line_end + 1 < len(offs) else offs[-1]
        import_ranges.append((start, end))
        names = [n[7:].strip() if n.startswith("module ") else n for n in blk.using_names]
        names += [dst for _src, dst in blk.renaming_pairs]
        all_names.update(names)  # both kinds — a public re-export still PROVIDES a name
        if blk.has_public:
            public_skipped += names
        else:
            check_names.update(names)
    return _ImportStructure(import_ranges, check_names, all_names, public_skipped)


def _has_unmodeled_scope(text: str) -> bool:
    """Report whether the file has any `open` the sieve does not fully model.

    `open` is Agda's single gateway for bringing an unqualified name from another
    scope into the body: `open import M using/renaming (...)` is fully enumerated
    (MODELED — its names are listed, so uniqueness is decidable), whereas a bare
    `open M` / record or module open / `let open`, or a wildcard `open import M`
    with no name list (`hiding` likewise), is an UNMODELED provider whose names
    the sieve cannot enumerate.  When any such construct is present the
    "alive iff def-id in body" shortcut is unsound (a seemingly-used import may be
    redundantly supplied by the unmodeled open), so the caller must confirm EVERY
    in-body import rather than skip.

    Whitelisting the one modeled form (and disqualifying every other `open`,
    including forms not yet imagined) keeps the gate correct BY CONSTRUCTION: an
    unrecognised `open` defaults to confirm, never to a silent skip.
    """
    modeled_lines: set[int] = set()
    for blk in parse_imports(text):
        raw = blk.raw
        if raw.lstrip().startswith("open import") and ("using" in raw or "renaming" in raw):
            modeled_lines.update(range(blk.line_start, blk.line_end + 1))
    for i, line in enumerate(text.splitlines()):
        stripped = line.lstrip()
        is_open = stripped == "open" or stripped[:5] in ("open ", "open\t")
        if is_open and i not in modeled_lines:
            return True
    return False


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


def detect_dead(text: str, tokens: list[Token], abspath: str) -> DetectResult:
    """Return one file's dead / duplicate / candidate analysis.

    `candidates` is the authoritative set to confirm; it is FN-complete by
    construction (see `_has_unmodeled_scope`).  `dead` / `duplicates` are its
    components, reported for insight.

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
    structure = _import_structure(text)
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
    unresolved = sorted(structure.check_names - set(import_defid))
    # Correct BY CONSTRUCTION: the "alive iff def-id in body" skip is sound only
    # when the file's every `open` is a fully-enumerated import (unique provider
    # decidable).  With any unmodeled-scope open, we cannot prove ANY in-body
    # import alive -> confirm them all (this file pays oracle cost, but no FN).
    disqualified = _has_unmodeled_scope(text)
    candidates = (
        sorted(structure.check_names) if disqualified else sorted(set(dead) | set(duplicates))
    )
    return {
        "dead": dead,
        "dead_defid_only": dead_defid_only,
        "duplicates": duplicates,
        "candidates": candidates,
        "disqualified": disqualified,
        "public_skipped": structure.public_skipped,
        "unresolved": unresolved,
    }


# ---- confirmation: authoritatively classify candidates by removing JUST each
# ---- one and asking agda (ground truth) — NOT the O(all-imports) brute-force.


def _texts_without_name(original: str, name: Name) -> list[str]:
    """Each variant of `original` with `name` dropped from ONE import block.

    A name imported in several blocks (a duplicate) yields one variant per
    block, so the confirm can test EVERY occurrence — the redundant copy need
    not be the first (e.g. a where-local re-import shadowed by a top-level one).
    Each block's entry may be a plain name, a `module X`, or a renaming dest;
    blocks that yield no change are skipped.
    """
    variants: list[str] = []
    lines = original.splitlines(keepends=True)
    for blk in parse_imports(original):
        if name in blk.using_names:
            cand = remove_name_from_raw(blk.raw, name)
        elif "module " + name in blk.using_names:
            cand = remove_name_from_raw(blk.raw, "module " + name)
        else:
            pair = next(((s, d) for s, d in blk.renaming_pairs if d == name), None)
            cand = remove_rename_from_raw(blk.raw, pair[0], pair[1]) if pair else None
        if cand is not None and cand != blk.raw:
            variants.append("".join(replace_block_in_lines(lines, blk, cand)))
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
    for modified in _texts_without_name(original, name):
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


def _sweep(agda: WarmAgda, files: list[RelPath]) -> SweepResult:
    """Warm-load each file, print its per-file result, return the SweepResult."""
    candidates: Candidates = {}
    times: list[float] = []
    for i, rel in enumerate(files, 1):
        text = (SRC / rel).read_text(encoding="utf-8")
        start = time.time()
        loaded = agda.load(str(SRC / rel))
        dt = time.time() - start
        times.append(dt)
        if not loaded.ok:
            emit(
                f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  ⚠️ LOAD FAILED "
                + "(no Status checked:true — agda could not check it)"
            )
            continue
        result = detect_dead(text, loaded.tokens, str(SRC / rel))
        cands = result["candidates"]
        if cands:
            candidates[rel] = cands
        extra = ""
        if result["disqualified"]:
            extra += "  [unmodeled-scope: confirming all in-body imports]"
        elif result["duplicates"]:
            extra += f"  duplicates={result['duplicates']}"
        if result["public_skipped"]:
            extra += f"  public-skipped={len(result['public_skipped'])}"
        if result["unresolved"]:
            extra += f"  unresolved={result['unresolved']}"
        if not cands:
            shown = "—"
        elif result["disqualified"]:
            shown = f"ALL {len(cands)}"
        else:
            shown = str(cands)
        emit(
            f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  "
            + f"tokens={len(loaded.tokens)} CANDIDATES={shown}{extra}"
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

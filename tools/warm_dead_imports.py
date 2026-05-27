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

import atexit
import contextlib
import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Self, TypedDict, cast

from tools._common import emit
from tools.prune_unused_imports import (
    AGDA_BIN,
    SRC_DIR,
    TypecheckCtx,
    parse_imports,
    remove_name_from_raw,
    remove_rename_from_raw,
    replace_block_in_lines,
    typecheck,
    warning_count_for,
)

AGDA = str(AGDA_BIN)
SRC = SRC_DIR

# Confirmation type-check budget (one serial agda at a time; memory-safe).
_RTS_CORES = 8
_RTS_HEAP_GB = 8
_CONFIRM_TIMEOUT = 300

# Bundled agda invocation context for the confirmation type-checks.
_CONFIRM_CTX = TypecheckCtx(
    src_dir=SRC, rts_cores=_RTS_CORES, rts_heap_gb=_RTS_HEAP_GB, timeout=_CONFIRM_TIMEOUT
)

# A definition identity: (definitionSite.filepath, definitionSite.position).
DefId = tuple[str, int]


class DefSite(TypedDict):
    """`definitionSite` of a highlighted token."""

    filepath: str
    position: int


class Token(TypedDict, total=False):
    """One highlighted token from a HighlightingInfo payload."""

    range: list[int]
    definitionSite: DefSite | None


class _HLInfo(TypedDict):
    """`info` field of a HighlightingInfo response."""

    payload: list[Token]


class _StatusInfo(TypedDict, total=False):
    """`status` field of a Status response."""

    checked: bool


class _Response(TypedDict, total=False):
    """One `agda --interaction-json` response object."""

    kind: str
    info: _HLInfo
    status: _StatusInfo


class DetectResult(TypedDict):
    """Result of `detect_dead` for one file."""

    dead: list[str]
    dead_defid_only: list[str]
    public_skipped: list[str]
    unresolved: list[str]


def line_offsets(text: str) -> list[int]:
    """Cumulative 0-based char offset of the start of each line."""
    offs = [0]
    for line in text.splitlines(keepends=True):
        offs.append(offs[-1] + len(line))
    return offs


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
            if info is not None:
                state.tokens += info["payload"]
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

    def load(self, abspath: str) -> tuple[list[Token], bool]:
        """Send Cmd_load; collect HighlightingInfo tokens until the load ends.

        Returns (tokens, ok) where ok == saw `Status{checked:true}`.  A FAILED
        load emits `JumpToError` and ends on `Status{checked:false}` (no
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
        return state.tokens, state.ok

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


def _import_structure(
    text: str,
) -> tuple[list[tuple[int, int]], set[str], list[str]]:
    """Parse import blocks → (import-clause char ranges, names to check, public-skipped).

    `using (module X)` contributes `X` (used qualified); renaming dests are
    in-scope; `public` re-export blocks are skipped (their only uses are
    downstream — flagging them would let a prune break the consumer's build).
    """
    blocks = parse_imports(text)
    offs = line_offsets(text)
    import_ranges: list[tuple[int, int]] = []
    check_names: set[str] = set()
    public_skipped: list[str] = []
    for blk in blocks:
        start = offs[blk.line_start]
        end = offs[blk.line_end + 1] if blk.line_end + 1 < len(offs) else offs[-1]
        import_ranges.append((start, end))
        names = [n[7:].strip() if n.startswith("module ") else n for n in blk.using_names]
        names += [dst for _src, dst in blk.renaming_pairs]
        if blk.has_public:
            public_skipped += names
        else:
            check_names.update(names)
    return import_ranges, check_names, public_skipped


def _body_index(
    text: str,
    tokens: list[Token],
    abspath: str,
    import_ranges: list[tuple[int, int]],
    check_names: set[str],
) -> tuple[dict[str, DefId], set[DefId], set[str], dict[str, set[str]]]:
    """Index tokens into the four lookups `detect_dead` consumes.

    Returns (import-name→def-id, body def-ids, body names with an EXTERNAL def,
    qualifier→field-def-files).  The external / qualified-file distinctions are
    the no-false-positive guards described in `detect_dead`.
    """
    import_defid: dict[str, DefId] = {}
    body_defids: set[DefId] = set()
    body_names_external: set[str] = set()
    qualified_use_files: dict[str, set[str]] = {}
    for tok in tokens:
        rng = tok.get("range")
        if not rng:
            continue
        off0 = rng[0] - 1  # Agda ranges are 1-based; Python str is 0-based
        name = text[off0 : rng[1] - 1]
        site = tok.get("definitionSite")
        defid: DefId | None = (site["filepath"], site["position"]) if site else None
        if any(s <= off0 < e for s, e in import_ranges):  # token in an import clause
            # def==None for a renaming dest / local binding: body refs point at
            # THIS token's position in THIS file -> synthesize that def-id.
            if name in check_names and name not in import_defid:
                import_defid[name] = defid or (abspath, rng[0])
        elif defid is not None:  # def-less body tokens can't be import-uses
            body_defids.add(defid)
            if defid[0] != abspath:
                body_names_external.add(name)
            if "." in name:  # qualified use `q.field`
                qualified_use_files.setdefault(name.split(".", 1)[0], set()).add(defid[0])
    return import_defid, body_defids, body_names_external, qualified_use_files


def detect_dead(text: str, tokens: list[Token], abspath: str) -> DetectResult:
    """Return {dead, dead_defid_only, public_skipped, unresolved}.

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
    import_ranges, check_names, public_skipped = _import_structure(text)
    import_defid, body_defids, body_names_external, qualified_use_files = _body_index(
        text, tokens, abspath, import_ranges, check_names
    )

    def alive(name: str, defid: DefId) -> bool:
        if defid in body_defids:  # precise: the import's OWN def is used
            return True
        if name in body_names_external:  # re-export alias (def-ids differ across files)
            return True
        # qualified use `name.field` whose field is defined in the import's module
        return defid[0] in qualified_use_files.get(name, set())

    dead = sorted(n for n, d in import_defid.items() if not alive(n, d))
    dead_defid_only = sorted(n for n, d in import_defid.items() if d not in body_defids)
    unresolved = sorted(check_names - set(import_defid))
    return {
        "dead": dead,
        "dead_defid_only": dead_defid_only,
        "public_skipped": public_skipped,
        "unresolved": unresolved,
    }


# ---- confirmation: authoritatively classify candidates by removing JUST each
# ---- one and asking agda (ground truth) — NOT the O(all-imports) brute-force.

_inflight: dict[str, str] = {}  # path -> original content, for crash-safe restore
_handlers_installed: list[bool] = []  # sentinel (mutated, not rebound → no `global`)


def _restore_inflight() -> None:
    """Restore any file left modified by an interrupted confirmation."""
    for path_str, original in list(_inflight.items()):
        with contextlib.suppress(OSError):
            _ = Path(path_str).write_text(original, encoding="utf-8")
    _inflight.clear()


def _signal_restore(signum: int, _frame: object) -> None:
    """SIGINT/SIGTERM handler: restore in-flight files, then exit."""
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


def _confirm_one(rel: str, name: str, original: str, baseline: int) -> bool:
    """Remove just `name` from its import clause, recompile, then restore.

    Returns True iff the file still type-checks without it (⇒ truly dead).
    ALWAYS restores the original content, even on failure.
    """
    path = SRC / rel
    new_raw: str | None = None
    target = None
    for blk in parse_imports(original):
        if name in blk.using_names:
            cand = remove_name_from_raw(blk.raw, name)
        elif "module " + name in blk.using_names:
            cand = remove_name_from_raw(blk.raw, "module " + name)
        else:
            pair = next(((s, d) for s, d in blk.renaming_pairs if d == name), None)
            cand = remove_rename_from_raw(blk.raw, pair[0], pair[1]) if pair else None
        if cand is not None and cand != blk.raw:
            new_raw, target = cand, blk
            break
    if new_raw is None or target is None:
        return False  # can't locate the clause entry -> conservatively NOT dead
    new_lines = replace_block_in_lines(original.splitlines(keepends=True), target, new_raw)
    try:
        _inflight[str(path)] = original
        _ = path.write_text("".join(new_lines), encoding="utf-8")
        return typecheck(rel, _CONFIRM_CTX, baseline_warning_count=baseline)
    finally:
        _ = path.write_text(original, encoding="utf-8")  # ALWAYS restore
        _ = _inflight.pop(str(path), None)


def confirm_candidates(rel: str, names: list[str]) -> tuple[list[str], list[str]]:
    """Classify each warm-flagged candidate by removing JUST it and recompiling.

    Returns (truly_dead, false_positives).  Crash-safe: per-candidate finally +
    atexit/SIGINT/SIGTERM handlers restore the file.  `typecheck`'s baseline
    guards the PatternShadowsConstructor silent-breakage class.
    """
    _install_restore_handlers()
    original = (SRC / rel).read_text(encoding="utf-8")
    baseline = warning_count_for(rel, _CONFIRM_CTX)
    truly_dead: list[str] = []
    fps: list[str] = []
    for name in names:
        (truly_dead if _confirm_one(rel, name, original, baseline) else fps).append(name)
    return truly_dead, fps


def _sweep(agda: WarmAgda, files: list[str]) -> tuple[dict[str, list[str]], list[float]]:
    """Warm-load each file, print its per-file result, return (candidates, times)."""
    candidates: dict[str, list[str]] = {}
    times: list[float] = []
    for i, rel in enumerate(files, 1):
        text = (SRC / rel).read_text(encoding="utf-8")
        start = time.time()
        tokens, ok = agda.load(str(SRC / rel))
        dt = time.time() - start
        times.append(dt)
        if not ok:
            emit(
                f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  ⚠️ LOAD FAILED "
                + "(no Status checked:true — agda could not check it)"
            )
            continue
        result = detect_dead(text, tokens, str(SRC / rel))
        if result["dead"]:
            candidates[rel] = result["dead"]
        extra = ""
        if result["public_skipped"]:
            extra += f"  public-skipped={len(result['public_skipped'])}"
        if result["unresolved"]:
            extra += f"  unresolved={result['unresolved']}"
        shown = result["dead"] if result["dead"] else "—"
        emit(
            f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  "
            + f"tokens={len(tokens)} CANDIDATES={shown}{extra}"
        )
    return candidates, times


def _print_summary(
    files: list[str], times: list[float], candidates: dict[str, list[str]], total: float
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


def _confirm_all(candidates: dict[str, list[str]]) -> None:
    """Confirm every candidate (remove-one + recompile) and print the verdict."""
    ncand = sum(len(v) for v in candidates.values())
    emit(f"=== confirming {ncand} candidate(s): remove-one + recompile (ground truth) ===")
    start = time.time()
    n_dead = 0
    for rel, cands in candidates.items():
        truly_dead, fps = confirm_candidates(rel, cands)
        n_dead += len(truly_dead)
        emit(f"  {rel}: TRULY-DEAD={truly_dead or '—'}  fp/used={fps or '—'}")
    emit(f"=== confirm: {n_dead} truly-dead of {ncand} in {time.time() - start:.1f}s ===")


def main() -> int:
    """Warm-sweep the given modules for dead-import candidates; --confirm to verify."""
    args = sys.argv[1:]
    do_confirm = "--confirm" in args
    files = [a for a in args if not a.startswith("--")]
    if not files:
        emit("usage: python -m tools.warm_dead_imports [--confirm] <relpath.agda> [...]")
        return 2
    start = time.time()
    with WarmAgda() as agda:
        candidates, times = _sweep(agda, files)
    _print_summary(files, times, candidates, time.time() - start)
    if do_confirm and candidates:
        _confirm_all(candidates)
    return 0


if __name__ == "__main__":
    sys.exit(main())

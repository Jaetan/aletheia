#!/usr/bin/env python3
"""PROTOTYPE (ci-speed branch): warm-process dead-import detection via
`agda --interaction-json`.

Supersedes oneshot_dead_imports.py's per-file `agda --html`:
  * ONE warm agda process loads many files (`Cmd_load` each) -> per-file agda
    startup + stdlib/interface reload is amortized across the whole batch (the
    production win — the gate runs on N files, not 1).
  * structured JSON: every token carries `definitionSite = {filepath, position}`
    (the exact def identity) -> no HTML parse, no 343-file closure written to disk.
  * reuses prune_unused_imports.parse_imports (multi-line / `public` / `renaming`).

DEAD = a checked import name whose DEFINITION (definitionSite) never reappears
among the file's BODY tokens.  Matching by def-id (not name) handles mixfix /
operators uniformly (`using (_∷_)` and body `∷` share a def).  `public`
re-export blocks are SKIPPED (their only uses are downstream — flagging them
would let a prune break the consumer's build) and reported, NOT silently.

Protocol notes (verified): a `Cmd_load` emits HighlightingInfo chunks, then
`Status{checked:true}` (type-check OK) ... `InteractionPoints` (terminal).
Read until InteractionPoints; absence of `Status{checked:true}` = failed load.
"""
from __future__ import annotations

import atexit
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prune_unused_imports import (  # noqa: E402  (block parser + confirm primitives)
    _warning_count_for,
    parse_imports,
    remove_name_from_raw,
    remove_rename_from_raw,
    replace_block_in_lines,
    typecheck,
)

AGDA = "/home/nicolas/.cabal/bin/agda"
SRC = Path("/home/nicolas/dev/agda/aletheia/src")


def line_offsets(text: str) -> list[int]:
    """Cumulative 0-based char offset of the start of each line."""
    offs = [0]
    for line in text.splitlines(keepends=True):
        offs.append(offs[-1] + len(line))
    return offs


class WarmAgda:
    """One long-lived `agda --interaction-json` process driven over pipes.

    Pipe discipline (deadlock-critical): line-buffered text pipes, flush after
    every command, and drain a command's responses fully (to InteractionPoints)
    before sending the next — otherwise the stdout pipe fills and agda blocks.
    """

    def __init__(self) -> None:
        self.proc = subprocess.Popen(  # noqa: S603
            [AGDA, "--interaction-json"],
            cwd=str(SRC),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
            env={**os.environ, "GHCRTS": "-M16G -N8"},
        )

    def load(self, abspath: str) -> tuple[list[dict], bool]:
        """Send Cmd_load; collect HighlightingInfo tokens until InteractionPoints.

        Returns (tokens, ok) where ok == saw `Status{checked:true}`."""
        assert self.proc.stdin is not None and self.proc.stdout is not None
        cmd = f'IOTCM "{abspath}" NonInteractive Direct (Cmd_load "{abspath}" [])\n'
        self.proc.stdin.write(cmd)
        self.proc.stdin.flush()
        tokens: list[dict] = []
        ok = False
        saw_error = False
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError("agda --interaction-json exited unexpectedly")
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            kind = d.get("kind")
            if kind == "HighlightingInfo":
                tokens += d.get("info", {}).get("payload", [])
            elif kind == "JumpToError":
                # a load that FAILS (scope/type error) emits JumpToError and ends
                # on Status{checked:false} — it never emits InteractionPoints, so
                # waiting only for InteractionPoints would hang on a broken file.
                saw_error = True
            elif kind == "Status":
                if d.get("status", {}).get("checked"):
                    ok = True
                elif saw_error:
                    break  # failure terminal: Status{checked:false} after the error
            elif kind == "InteractionPoints":
                break  # success terminal
        return tokens, ok

    def close(self) -> None:
        try:
            assert self.proc.stdin is not None
            self.proc.stdin.close()
            self.proc.wait(timeout=10)
        except Exception:
            self.proc.kill()


def detect_dead(text: str, tokens: list[dict], abspath: str) -> dict:
    """Return {dead, dead_defid_only, public_skipped, unresolved}.

    Identity model (from Agda's highlighting): a body reference's def-id is
    `(definitionSite.filepath, position)`; an imported name is ALIVE when its
    import-clause token's def-id reappears among body tokens' def-ids.  Cases
    this codebase exercises (each verified against real token data):
      * mixfix (`using (_∷_)` / body `∷`): both share one def-id.
      * renaming dest (`renaming (_≟_ to _≟ₛ_)`): the DEST token has def==None,
        but body uses point at `(this-file, dest-offset)` — synthesize that.
      * qualified use `n.foo` (module/record/type as a qualifier): import def-id
        is `n`'s, but body `n.foo` carries the FIELD's def-id — detect via the
        `n.` name prefix (covers `using (module X)` AND record-type qualifiers
        like `Identifier.name`).
      * re-export aliases (`[]`): decl/use def-ids differ -> exact-name fallback.
    No-FP bias: dead only if NONE of these say alive.  `dead_defid_only` drops
    the name/prefix fallbacks (reported, to show what they catch)."""
    blocks = parse_imports(text)
    offs = line_offsets(text)

    import_ranges: list[tuple[int, int]] = []
    check_names: set[str] = set()
    public_skipped: list[str] = []
    for b in blocks:
        start = offs[b.line_start]
        end = offs[b.line_end + 1] if b.line_end + 1 < len(offs) else offs[-1]
        import_ranges.append((start, end))
        names: list[str] = []
        for n in b.using_names:
            # `using (module X)` brings X into scope (used qualified as `X.foo`)
            names.append(n[7:].strip() if n.startswith("module ") else n)
        names += [dst for _src, dst in b.renaming_pairs]  # renaming DEST is in-scope
        if b.has_public:
            public_skipped += names
        else:
            check_names.update(names)

    def in_import(off0: int) -> bool:
        return any(s <= off0 < e for s, e in import_ranges)

    import_defid: dict[str, tuple] = {}
    body_defids: set[tuple] = set()
    # The name fallback (re-export aliases like `[]`) is restricted to names whose
    # body token resolves to a def OUTSIDE this file: a LOCAL def of the same name
    # is a shadow, NOT a use of the import, so it must not keep the import alive
    # (guards FN scenario 1 — `import foo` dead + local `foo`).
    body_names_external: set[str] = set()
    # Qualified uses `q.field` -> the files `field` is defined in.  A qualifier is
    # kept alive only if the IMPORT's own def lives in one of those files (guards
    # FN scenario 2 — a LOCAL module `q` masking a dead import `q`).
    qualified_use_files: dict[str, set[str]] = {}
    for t in tokens:
        rng = t.get("range")
        if not rng:
            continue
        off0 = rng[0] - 1  # Agda ranges are 1-based; Python str is 0-based
        name = text[off0 : rng[1] - 1]
        ds = t.get("definitionSite")
        defid = (ds["filepath"], ds["position"]) if ds else None
        if in_import(off0):
            if name in check_names:
                # def==None for a renaming dest / local binding: body refs point
                # at THIS token's position in THIS file -> synthesize that def-id.
                import_defid.setdefault(name, defid or (abspath, rng[0]))
        elif defid is not None:  # def-less body tokens (pattern vars, keywords) can't be import-uses
            body_defids.add(defid)
            if defid[0] != abspath:
                body_names_external.add(name)
            if "." in name:  # qualified use `q.field`
                qualified_use_files.setdefault(name.split(".", 1)[0], set()).add(defid[0])

    def alive(n: str, did: tuple) -> bool:
        if did in body_defids:  # precise: the import's OWN def is used in the body
            return True
        if n in body_names_external:  # re-export alias (decl/use def-ids differ across files)
            return True
        # qualified use `n.field` whose field is defined in the import's OWN module
        return did is not None and did[0] in qualified_use_files.get(n, ())

    dead = sorted(n for n, did in import_defid.items() if not alive(n, did))
    dead_defid_only = sorted(
        n for n, did in import_defid.items() if did not in body_defids
    )
    unresolved = sorted(check_names - set(import_defid))  # no import-block token found
    return {
        "dead": dead,
        "dead_defid_only": dead_defid_only,
        "public_skipped": public_skipped,
        "unresolved": unresolved,
    }


# ---- confirmation: authoritatively classify candidates by removing JUST each
# ---- one and asking agda (ground truth) — NOT the O(all-imports) brute-force.

_inflight: dict[str, str] = {}  # path -> original content, for crash-safe restore


def _restore_inflight(*_: object) -> None:
    for p, orig in list(_inflight.items()):
        try:
            Path(p).write_text(orig)
        except OSError:
            pass
    _inflight.clear()


_HANDLERS_INSTALLED = False


def _install_restore_handlers() -> None:
    global _HANDLERS_INSTALLED
    if _HANDLERS_INSTALLED:
        return
    atexit.register(_restore_inflight)
    for sig in (signal.SIGINT, signal.SIGTERM):
        prev = signal.getsignal(sig)
        signal.signal(sig, lambda s, f: (_restore_inflight(), sys.exit(128 + s)))
        _ = prev
    _HANDLERS_INSTALLED = True


def confirm_candidates(
    rel: str, names: list[str],
    rts_cores: int = 8, rts_heap_gb: int = 8, timeout: int = 300,
) -> tuple[list[str], list[str]]:
    """Classify each warm-flagged candidate by removing JUST it and recompiling.

    Returns (truly_dead, false_positives).  Each candidate is tested in
    isolation against the original file; the file is ALWAYS restored (finally +
    atexit/signal handlers cover exception / SIGINT / SIGTERM — the user's
    cleanup requirement).  `typecheck`'s baseline_warning_count guards the
    PatternShadowsConstructor silent-breakage class (removing `true`/`false`
    compiles but flips a constructor pattern into a variable binding)."""
    _install_restore_handlers()
    path = SRC / rel
    original = path.read_text()
    baseline = _warning_count_for(rel, SRC, rts_cores, rts_heap_gb, timeout)
    truly_dead: list[str] = []
    fps: list[str] = []
    for name in names:
        new_raw = target = None
        for b in parse_imports(original):
            if name in b.using_names:
                cand = remove_name_from_raw(b.raw, name)
            elif ("module " + name) in b.using_names:
                cand = remove_name_from_raw(b.raw, "module " + name)
            else:
                pair = next(((s, d) for s, d in b.renaming_pairs if d == name), None)
                cand = remove_rename_from_raw(b.raw, pair[0], pair[1]) if pair else None
            if cand is not None and cand != b.raw:
                new_raw, target = cand, b
                break
        if new_raw is None:
            fps.append(name)  # can't locate the clause entry -> conservatively NOT dead
            continue
        new_lines = replace_block_in_lines(original.splitlines(keepends=True), target, new_raw)
        try:
            _inflight[str(path)] = original
            path.write_text("".join(new_lines))
            ok = typecheck(rel, SRC, rts_cores, rts_heap_gb, timeout, baseline)
        finally:
            path.write_text(original)  # ALWAYS restore
            _inflight.pop(str(path), None)
        (truly_dead if ok else fps).append(name)
    return truly_dead, fps


def main() -> int:
    args = sys.argv[1:]
    do_confirm = "--confirm" in args
    files = [a for a in args if not a.startswith("--")]
    if not files:
        print("usage: warm_dead_imports.py [--confirm] <relpath.agda> [...]")
        return 2

    agda = WarmAgda()
    t_start = time.time()
    times: list[float] = []
    candidates: dict[str, list[str]] = {}
    try:
        for i, rel in enumerate(files, 1):
            text = (SRC / rel).read_text()
            t0 = time.time()
            tokens, ok = agda.load(str(SRC / rel))
            dt = time.time() - t0
            times.append(dt)
            if not ok:
                print(f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  ⚠️ LOAD FAILED "
                      f"(no Status checked:true — agda could not check it)")
                continue
            r = detect_dead(text, tokens, str(SRC / rel))
            if r["dead"]:
                candidates[rel] = r["dead"]
            extra = ""
            if r["public_skipped"]:
                extra += f"  public-skipped={len(r['public_skipped'])}"
            if r["unresolved"]:
                extra += f"  unresolved={r['unresolved']}"
            cand_s = r["dead"] if r["dead"] else "—"
            print(f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  "
                  f"tokens={len(tokens)} CANDIDATES={cand_s}{extra}")
    finally:
        agda.close()

    total = time.time() - t_start
    ncand = sum(len(v) for v in candidates.values())
    if len(times) > 1:
        warm = sum(times[1:]) / len(times[1:])
        print(f"--- warm sweep: {len(files)} files {total:.1f}s "
              f"(file1={times[0]:.1f}s cold, mean 2..N={warm:.1f}s) — "
              f"{ncand} candidate(s) in {len(candidates)} file(s) ---")
    else:
        print(f"--- 1 file: {total:.1f}s — {ncand} candidate(s) ---")

    if do_confirm and candidates:
        print(f"=== confirming {ncand} candidate(s): remove-one + recompile (ground truth) ===")
        tc = time.time()
        n_dead = 0
        for rel, cands in candidates.items():
            td, fp = confirm_candidates(rel, cands)
            n_dead += len(td)
            print(f"  {rel}: TRULY-DEAD={td if td else '—'}  fp/used={fp if fp else '—'}")
        print(f"=== confirm: {n_dead} truly-dead of {ncand} in {time.time() - tc:.1f}s ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())

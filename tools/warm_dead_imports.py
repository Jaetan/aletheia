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

import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prune_unused_imports import parse_imports  # noqa: E402  (robust block parser)

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
            elif kind == "Status" and d.get("status", {}).get("checked"):
                ok = True
            elif kind == "InteractionPoints":  # terminal marker for a load
                break
        return tokens, ok

    def close(self) -> None:
        try:
            assert self.proc.stdin is not None
            self.proc.stdin.close()
            self.proc.wait(timeout=10)
        except Exception:
            self.proc.kill()


def detect_dead(text: str, tokens: list[dict]) -> dict:
    """Return {dead, dead_defid_only, public_skipped, unresolved}.

    `dead` uses def-id OR name match (no-FP bias: a name is alive if either its
    definition or its exact spelling appears in the body).  `dead_defid_only`
    drops the name fallback — reported so we can see whether def-id alone already
    resolves re-export aliases (if dead == dead_defid_only on real files, the
    name fallback is redundant and can go)."""
    blocks = parse_imports(text)
    offs = line_offsets(text)

    import_ranges: list[tuple[int, int]] = []
    check_names: set[str] = set()
    public_skipped: list[str] = []
    for b in blocks:
        start = offs[b.line_start]
        end = offs[b.line_end + 1] if b.line_end + 1 < len(offs) else offs[-1]
        import_ranges.append((start, end))
        names = list(b.using_names) + [dst for _src, dst in b.renaming_pairs]
        if b.has_public:
            public_skipped += names
        else:
            check_names.update(names)

    def in_import(off0: int) -> bool:
        return any(s <= off0 < e for s, e in import_ranges)

    import_defid: dict[str, tuple] = {}
    body_defids: set[tuple] = set()
    body_names: set[str] = set()
    for t in tokens:
        rng = t.get("range")
        if not rng:
            continue
        off0 = rng[0] - 1  # Agda ranges are 1-based; Python str is 0-based
        name = text[off0 : rng[1] - 1]
        ds = t.get("definitionSite")
        defid = (ds["filepath"], ds["position"]) if ds else None
        if in_import(off0):
            if name in check_names and defid is not None:
                import_defid.setdefault(name, defid)
        else:
            if defid is not None:
                body_defids.add(defid)
            body_names.add(name)

    dead = sorted(
        n for n, did in import_defid.items()
        if did not in body_defids and n not in body_names
    )
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


def main() -> int:
    files = sys.argv[1:]
    if not files:
        print("usage: warm_dead_imports.py <relpath.agda> [<relpath2.agda> ...]")
        return 2

    agda = WarmAgda()
    t_start = time.time()
    times: list[float] = []
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
            r = detect_dead(text, tokens)
            extra = ""
            if r["public_skipped"]:
                extra += f"  public-skipped={len(r['public_skipped'])}"
            if r["dead"] != r["dead_defid_only"]:
                extra += f"  [def-id-only would add {sorted(set(r['dead_defid_only'])-set(r['dead']))}]"
            if r["unresolved"]:
                extra += f"  unresolved={r['unresolved']}"
            dead_s = r["dead"] if r["dead"] else "—"
            print(f"[{i}/{len(files)}] {dt:5.1f}s  {rel}  "
                  f"tokens={len(tokens)} DEAD={dead_s}{extra}")
    finally:
        agda.close()

    total = time.time() - t_start
    print(f"--- {len(files)} files in ONE warm process: {total:.1f}s total "
          f"(file1={times[0]:.1f}s cold, mean files 2..N="
          f"{(sum(times[1:])/len(times[1:])):.1f}s warm)" if len(times) > 1
          else f"--- 1 file: {total:.1f}s ---")
    return 0


if __name__ == "__main__":
    sys.exit(main())

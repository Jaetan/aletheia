#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Neutral warm-Agda infrastructure shared by the IWYU import tooling.

Three concerns, none of them import *resolution* (that is the `.agdai` reader's
job — :mod:`tools.iwyu_reader` / :mod:`tools.iwyu_narrow`):

  * **paths** — the repo root, project ``src/`` dir, and the ``agda`` binary,
    resolved once at import;
  * **the warm process** — :class:`WarmAgda`, one long-lived
    ``agda --interaction-json`` driven over pipes.  Its only consumer-facing
    capability is ``load(path)`` → re-check a module (writing a fresh ``.agdai``)
    and report whether it type-checked;
  * **file scope** — ``--all`` (whole tree), ``--diff`` (changed vs ``main``),
    or explicit paths, via :func:`select_files`.

This is the substrate the reader gates stand on; it carries no sieve, no
def-id token indexing, and no remove-recompile confirm — those belonged to the
retired brute-force resolution tools.
"""

from __future__ import annotations

import json
import os
import queue
import subprocess
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple, Self, TypedDict, cast

from tools._common import agda_tree_lock, emit, find_executable, git_toplevel, run_capture

if TYPE_CHECKING:
    from collections.abc import Callable


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

# Resolve agda from PATH (via shutil.which, S607-clean) rather than hardcoding
# an absolute path; the AGDA_BIN env var overrides for non-standard installs.
# An agda-driving module that cannot find agda should fail loud at import.
AGDA_BIN = Path(os.environ.get("AGDA_BIN") or find_executable("agda"))

AGDA = str(AGDA_BIN)
SRC = SRC_DIR

# An imported identifier — a `using (...)` entry or renaming dest, e.g. "_∷_".
type Name = str
# A src-relative Agda module path, e.g. "Aletheia/LTL/Coalgebra.agda".
type RelPath = str

# Max seconds of agda SILENCE (no output line) before a Cmd_load read gives up,
# so no command can hang on a silent agda.  A Cmd_load terminal arrives within
# one module's check time even cold; the cap only fires on a genuinely wedged
# process.
_LOAD_SILENCE_S = 300.0


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
    failure message ('' when ok) — the `[NotInScope]` text whose `did you mean
    'M.x'` hint a narrowing-completion step could read.  `tokens` is the deduped
    highlighting; `warnings` the AllGoalsWarnings messages.
    """

    tokens: list[Token]
    ok: bool
    error: str
    warnings: list[str]


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
    carry the warning tags (`-W[no]UnreachableClauses`, …).
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
        complete, token per range) so every consumer sees each token once.
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
        emit("iwyu gate: could not diff vs main (rely on the periodic --all sweep)")
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
    There is NO file-count skip: the warm load is fast enough (~0.6 s/file after
    the first) to run on every scoped file, so the gate never silently passes.
    """
    if "--all" in args:
        files = all_agda_files()
        emit(f"iwyu gate: whole tree — {len(files)} file(s)")
        return files
    if "--diff" in args:
        files = changed_agda_files()
        emit(f"iwyu gate: {len(files)} .agda file(s) changed vs main")
        return files
    explicit = [a for a in args if not a.startswith("--")]
    if not explicit:
        emit("usage: (--all | --diff | FILE.agda ...)")
        return None
    return explicit


def run_warm_gate(args: list[str], action: Callable[[WarmAgda, list[RelPath]], int]) -> int:
    """Resolve scope, warm-load each file (fresh `.agdai`), then run ``action``.

    The shared CLI shell of the reader gates (:mod:`tools.iwyu_reader` and
    :mod:`tools.iwyu_narrow`): scope selection (usage error → exit 2; empty scope
    → exit 0 no-op), the agda-tree lock + one warm process, and a `Cmd_load` of
    every scoped file so the `.agdai` interfaces the reader reads are current.
    ``action(agda, files)`` does the per-tool work; its return is the exit code.
    """
    files = select_files(args)
    if files is None:
        return 2
    if not files:
        return 0  # nothing in scope (e.g. --diff with no .agda change): a true no-op
    with agda_tree_lock(), WarmAgda() as agda:
        for rel in files:
            _ = agda.load(str(SRC / rel))  # refresh `.agdai` so the reader sees current interfaces
        return action(agda, files)

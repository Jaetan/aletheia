# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Staleness + incrementality gate — the build rebuilds what changed, only that, never stale.

The build's honest dependency graph (the Shakefile ``.so`` rule depends on the
``.agda`` sources; ``aletheia.cabal`` lists every MAlonzo module so cabal tracks
the real ``.hs -> .so`` graph) must rebuild ``libaletheia-ffi.so`` when — and
only when — a source changes.  This gate is the behavioral regression test that
the graph stays correct.  It checks two properties:

1. **Never stale** — editing a runtime string literal in a source must REACH the
   ``.so``, and reverting it must too.  This is the failure the old ``rm -rf``
   sledgehammer masked by always full-rebuilding.  Probed at TWO structurally
   distant modules (Protocol/ResponseFormat and DBC/Formatter) so a graph bug that
   breaks propagation for only one subtree is caught: both edits land in one build,
   and BOTH distinct tokens must appear in the ``.so``.

2. **Incremental** — a no-op build (nothing changed) must NOT relink the ``.so``
   (its mtime stays put).  A regression back to the always-full-rebuild
   sledgehammer would pass property 1 (edits still reach the ``.so``) but fail
   here.  Asserted structurally (was the artifact rewritten?), never by wall-clock.

The oracle is *behavioral* (does the edit reach the artifact? was it relinked?),
never bit-identical — an incremental build differs benignly from a from-scratch one.

Crash behaviour: every edited source is restored on exit, on SIGINT and on
SIGTERM.  SIGKILL bypasses that and leaves the run's marker in the two sources.
The build runs under ``run_guarded``, so it stops when the run dies, SIGKILL
included, rather than relinking the ``.so`` with the marker in it.  The marker
names the run that wrote it, by pid and start time, and the startup check
refuses on one, saying which run left it, whether that run still lives, and the
edit that restores the file.  The check also refuses while a build still holds
Shake's lock, naming the process, since a build nothing stopped looks like that
from outside.  Two runs
cannot overlap: the gate holds the repo-wide Agda lock for its whole body, and a
second run reports the lock as held.  A marker left in the ``.so`` clears on the
next build over restored sources, and this gate refuses to run against one.
Run this isolated from any other ``.so`` consumer (it transiently mutates the
shared artifact).

Run: ``python -m tools.check_build_incremental``  (exit 0 = pass, 1 = fail).
"""

from __future__ import annotations

import fcntl
import os
import re
import struct
import sys
from datetime import UTC, datetime
from typing import TYPE_CHECKING, NamedTuple

from tools._common import (
    agda_tree_lock,
    emit,
    find_executable,
    install_restore_handlers,
    process_alive,
    run_guarded,
    track_inflight,
    untrack_inflight,
)
from tools._warm import REPO_ROOT
from tools.check_install_freshness import (
    RelinkCertificate,
    chain_baseline,
    gnu_build_id,
    load_relink_certificate,
    relink_certificate_path,
    write_relink_certificate,
)

if TYPE_CHECKING:
    from pathlib import Path

_SO = REPO_ROOT / "build" / "libaletheia-ffi.so"
_SHAKE_LOCK = REPO_ROOT / "build" / ".shake.lock"

# A marker is the token this gate splices into a runtime string literal.  It
# names the run that wrote it, so a leftover can say which run was killed and
# whether that run still lives; the unnamed form is what an older gate wrote.
MARKER_PREFIX = "ALETHEIA_STALE_PROBE_"
_MARKER = re.compile(rb"ALETHEIA_STALE_PROBE_([A-Z]+)(?:_pid(\d+)_(\d{8}T\d{6}Z))?")
_RUN_ID = f"pid{os.getpid()}_{datetime.now(UTC):%Y%m%dT%H%M%SZ}"

# Linux x86_64 ``struct flock``: l_type, l_whence, l_start, l_len, l_pid.
_FLOCK = "hhqqi"


class RunMarker(NamedTuple):
    """One marker found in a source or in the ``.so``, and the run it names."""

    text: str  # the whole token as found
    tag: str  # which probe wrote it
    pid: int | None  # the writing process, or None for the unnamed form
    started: str | None  # the run's UTC start, or None for the unnamed form


def markers_in(data: str | bytes) -> list[RunMarker]:
    """Every marker in ``data``, in order of appearance."""
    raw = data.encode() if isinstance(data, str) else data
    found: list[RunMarker] = []
    for match in _MARKER.finditer(raw):
        pid = match.group(2)
        started = match.group(3)
        found.append(
            RunMarker(
                text=match.group(0).decode(),
                tag=match.group(1).decode(),
                pid=int(pid) if pid else None,
                started=started.decode() if started else None,
            )
        )
    return found


def describe_run(marker: RunMarker) -> str:
    """Say which run wrote ``marker`` and whether it still lives."""
    if marker.pid is None:
        return "an unnamed run, from a gate older than this one"
    state = "still alive" if process_alive(marker.pid) else "gone"
    return f"pid {marker.pid}, started {marker.started}, {state}"


def shake_lock_holder(lock: Path) -> int | None:
    """Return the pid holding Shake's lock on ``lock``, or None when nobody does.

    Shake takes a POSIX record lock on the file for the whole build, and the
    kernel releases it when the holder exits however it exits, so the file's
    existence says nothing and only F_GETLK does.  A lock this process holds
    reads as free, which is fine: the gate asks before it builds.
    """
    if not lock.exists():
        return None
    fd = os.open(lock, os.O_RDONLY)
    try:
        query = struct.pack(_FLOCK, fcntl.F_WRLCK, os.SEEK_SET, 0, 0, 0)
        answer = fcntl.fcntl(fd, fcntl.F_GETLK, query)
    finally:
        os.close(fd)
    kind, _, _, _, pid = struct.unpack(_FLOCK, answer[: struct.calcsize(_FLOCK)])
    return None if kind == fcntl.F_UNLCK else int(pid)


class Probe(NamedTuple):
    """One runtime-string edit site, in a distinct module, that must reach the .so."""

    file: Path
    anchor: str  # the literal as it appears in source, e.g. '"uncached_atom"'
    sentinel: str  # the anchor with the token spliced in before the closing quote
    token: bytes  # distinctive bytes present in the .so iff the edit propagated


def _probe(rel: str, anchor_inner: str, tag: str) -> Probe:
    """Build a probe from a repo-relative file, the inner literal text, and a unique tag."""
    token = f"{MARKER_PREFIX}{tag}_{_RUN_ID}"
    return Probe(
        file=REPO_ROOT / rel,
        anchor=f'"{anchor_inner}"',
        sentinel=f'"{anchor_inner}_{token}"',
        token=token.encode(),
    )


# Two probes in structurally distant runtime modules — the `uncached_atom`
# warning-kind label (Protocol/ResponseFormat) and the `little_endian` byte-order
# key the DBC formatter emits (DBC/Formatter).  Each is a runtime string literal
# compiled verbatim into the .so (response formatting / formatDBCText are live),
# with a distinct token so BOTH must propagate — a graph bug in one subtree can't
# hide behind the other.  If an anchor is renamed the gate fails LOUDLY (startup
# check); repoint it at a current runtime literal the .so actually contains.  Note
# a spec-only module (e.g. LTL/JSON/Format) is NOT in the runtime closure even if
# its string also appears in the .so via a sibling — its edit won't propagate.
_PROBES: tuple[Probe, ...] = (
    _probe("src/Aletheia/Protocol/ResponseFormat.agda", "uncached_atom", "RF"),
    _probe("src/Aletheia/DBC/Formatter.agda", "little_endian", "DBC"),
)


def _build() -> None:
    """Run ``cabal run shake -- build`` under ``run_guarded``; raise, echoing output, on failure."""
    result = run_guarded(
        [find_executable("cabal"), "run", "shake", "--", "build"],
        cwd=REPO_ROOT,
    )
    if result.returncode != 0:
        emit(result.stdout)
        message = f"`cabal run shake -- build` failed (exit {result.returncode})"
        raise RuntimeError(message)


def _fail(msg: str) -> None:
    """Emit a gate-failure line under the standard prefix."""
    emit(f"build-incremental gate: FAIL — {msg}")


def _rel(path: Path) -> str:
    """Spell ``path`` relative to the repository root, for messages."""
    return str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)


def _check_no_leftovers() -> bool:
    """Refuse on what a killed run leaves behind, before anything is built or captured.

    Runs before the baseline build on purpose: a build over a marked source
    relinks the marker into the ``.so``, and capturing the marked text as the
    original would write it back as the restore.
    """
    clean = True
    for probe in _PROBES:
        for marker in markers_in(probe.file.read_text(encoding="utf-8")):
            clean = False
            _fail(
                f"{_rel(probe.file)} carries the marker of an interrupted gate run "
                + f"({describe_run(marker)}): the run was killed after editing the "
                + "file and before restoring it"
            )
            left = f'"{probe.anchor[1:-1]}_{marker.text}"'
            emit(f"  restore it by replacing {left} with {probe.anchor}")
    holder = shake_lock_holder(_SHAKE_LOCK)
    if holder is not None:
        clean = False
        _fail(
            f"a build (pid {holder}) holds {_rel(_SHAKE_LOCK)}; wait for it to finish. "
            + "This gate edits sources the build reads and rebuilds the .so, so it does not "
            + "run beside another build"
        )
    return clean


def _check_baseline() -> dict[Path, str] | None:
    """Establish a clean baseline; return each probe file's original text, or None on failure."""
    _build()  # a no-op ~0.1s when already built
    if not _SO.exists():
        _fail(f"{_SO} was not produced")
        return None
    for marker in markers_in(_SO.read_bytes()):
        _fail(
            f"the .so carries the marker {marker.text!r} of an earlier run ({describe_run(marker)})"
        )
        return None
    originals: dict[Path, str] = {}
    for probe in _PROBES:
        text = probe.file.read_text(encoding="utf-8")
        if probe.anchor not in text:
            _fail(f"anchor {probe.anchor} not found in {probe.file}")
            emit("  (the probe string moved; point it at a current runtime string literal)")
            return None
        originals[probe.file] = text
    return originals


def _check_edits_and_reverts(originals: dict[Path, str]) -> bool:
    """Edit all anchors → build → all reach .so; revert all → build → none do.  True iff sound."""
    # 1. edit ALL → one build: every edit MUST reach the .so (else the build is stale).
    for probe in _PROBES:
        edited = originals[probe.file].replace(probe.anchor, probe.sentinel)
        _ = probe.file.write_text(edited, encoding="utf-8")
    _build()
    so_bytes = _SO.read_bytes()
    for probe in _PROBES:
        if probe.token not in so_bytes:
            _fail(f"an edit to {probe.file.name} did not reach the .so (STALE)")
            return False
        emit(f"  edit to {probe.file.name} reached the .so ✓")
    # 2. revert ALL → one build: every revert MUST reach the .so too.
    for probe in _PROBES:
        _ = probe.file.write_text(originals[probe.file], encoding="utf-8")
    _build()
    so_bytes = _SO.read_bytes()
    for probe in _PROBES:
        if probe.token in so_bytes:
            _fail(f"a revert of {probe.file.name} did not reach the .so (STALE)")
            return False
        emit(f"  revert of {probe.file.name} reached the .so ✓")
    return True


def _check_incremental() -> bool:
    """Assert a no-op build does not relink the .so (mtime stable); True iff incremental."""
    mtime_before = _SO.stat().st_mtime_ns
    _build()
    if _SO.stat().st_mtime_ns != mtime_before:
        _fail("a no-op build relinked the .so (NOT incremental — sledgehammer?)")
        return False
    emit("  no-op build did not relink the .so ✓")
    return True


def _run() -> int:
    """Run the staleness + incrementality checks; restore every edited source always."""
    if not _check_no_leftovers():
        return 1
    originals = _check_baseline()
    if originals is None:
        return 1

    # The probes below RELINK the .so, and GHC recompilation is not
    # symbol-deterministic — the reverted final relink carries a fresh GNU
    # build-id for the same link inputs.  Record the baseline id now (chaining
    # through any prior certificate whose post-probe id matches — consecutive
    # probe cycles keep vouching for the oldest baseline) and drop the old
    # certificate immediately, so a run that dies mid-probe leaves nothing
    # vouching for a half-probed library.  On full PASS the certificate is
    # rewritten, letting the freshness gate accept a deployed copy of the
    # baseline build against the post-probe library (same inputs, proven by
    # this gate's own edit/revert checks).
    baseline_id = chain_baseline(load_relink_certificate(REPO_ROOT), gnu_build_id(_SO) or "")
    cert_file = relink_certificate_path(REPO_ROOT)
    cert_file.unlink(missing_ok=True)

    install_restore_handlers()
    for probe in _PROBES:
        track_inflight(str(probe.file), originals[probe.file])
    try:
        if not _check_edits_and_reverts(originals):
            return 1
        if not _check_incremental():
            return 1
    finally:
        for probe in _PROBES:
            _ = probe.file.write_text(originals[probe.file], encoding="utf-8")
            untrack_inflight(str(probe.file))

    post_probe_id = gnu_build_id(_SO)
    if baseline_id and post_probe_id is not None and post_probe_id != baseline_id:
        write_relink_certificate(
            REPO_ROOT,
            RelinkCertificate(baseline_build_id=baseline_id, post_probe_build_id=post_probe_id),
        )

    emit("=== build-incremental gate: PASS — edits/reverts reach the .so; no-op is incremental ===")
    return 0


def main() -> int:
    """Hold the repo-wide Agda lock, so two runs cannot overlap, and run the checks."""
    with agda_tree_lock():
        return _run()


if __name__ == "__main__":
    sys.exit(main())

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
   distant modules (Protocol and LTL) so a graph bug that breaks propagation for
   only one subtree is caught: both edits land in one build, and BOTH distinct
   tokens must appear in the ``.so``.

2. **Incremental** — a no-op build (nothing changed) must NOT relink the ``.so``
   (its mtime stays put).  A regression back to the always-full-rebuild
   sledgehammer would pass property 1 (edits still reach the ``.so``) but fail
   here.  Asserted structurally (was the artifact rewritten?), never by wall-clock.

The oracle is *behavioral* (does the edit reach the artifact? was it relinked?),
never bit-identical — an incremental build differs benignly from a from-scratch one.

Crash behaviour: every edited *source* is restored (atexit + SIGINT/SIGTERM), so
an interrupt never leaves a mutated Agda source.  The ``.so`` artifact is NOT
transactional, though — an interrupt after an edit-build can leave
``build/libaletheia-ffi.so`` carrying a probe sentinel; the next normal build
restores it, and this gate refuses to run against such a leftover (its startup
check asserts a clean baseline first).  Run this isolated from any other ``.so``
consumer (it transiently mutates the shared artifact).

Run: ``python -m tools.check_build_incremental``  (exit 0 = pass, 1 = fail).
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, NamedTuple

from tools._common import (
    emit,
    find_executable,
    install_restore_handlers,
    run_capture,
    track_inflight,
    untrack_inflight,
)
from tools._warm import REPO_ROOT

if TYPE_CHECKING:
    from pathlib import Path

_SO = REPO_ROOT / "build" / "libaletheia-ffi.so"


class _Probe(NamedTuple):
    """One runtime-string edit site, in a distinct module, that must reach the .so."""

    file: Path
    anchor: str  # the literal as it appears in source, e.g. '"uncached_atom"'
    sentinel: str  # the anchor with the token spliced in before the closing quote
    token: bytes  # distinctive bytes present in the .so iff the edit propagated


def _probe(rel: str, anchor_inner: str, tag: str) -> _Probe:
    """Build a probe from a repo-relative file, the inner literal text, and a unique tag."""
    token = f"ALETHEIA_STALE_PROBE_{tag}"
    return _Probe(
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
_PROBES: tuple[_Probe, ...] = (
    _probe("src/Aletheia/Protocol/ResponseFormat.agda", "uncached_atom", "RF"),
    _probe("src/Aletheia/DBC/Formatter.agda", "little_endian", "DBC"),
)


def _build() -> None:
    """Run ``cabal run shake -- build``; raise (echoing output) on a non-zero exit."""
    result = run_capture(
        [find_executable("cabal"), "run", "shake", "--", "build"],
        cwd=REPO_ROOT,
    )
    if result.returncode != 0:
        emit(result.stdout)
        emit(result.stderr)
        message = f"`cabal run shake -- build` failed (exit {result.returncode})"
        raise RuntimeError(message)


def _fail(msg: str) -> None:
    """Emit a gate-failure line under the standard prefix."""
    emit(f"build-incremental gate: FAIL — {msg}")


def _check_baseline() -> dict[Path, str] | None:
    """Establish a clean baseline; return each probe file's original text, or None on failure."""
    _build()  # a no-op ~0.1s when already built
    if not _SO.exists():
        _fail(f"{_SO} was not produced")
        return None
    so_bytes = _SO.read_bytes()
    originals: dict[Path, str] = {}
    for probe in _PROBES:
        if probe.token in so_bytes:
            _fail(f"stale sentinel {probe.token!r} left in .so by a prior run")
            return None
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


def main() -> int:
    """Run the staleness + incrementality checks; restore every edited source always."""
    originals = _check_baseline()
    if originals is None:
        return 1

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

    emit("=== build-incremental gate: PASS — edits/reverts reach the .so; no-op is incremental ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())

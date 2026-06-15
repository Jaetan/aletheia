# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Staleness gate — prove the build is incremental AND never silently stale.

The build's honest dependency graph (the Shakefile ``.so`` rule depends on the
``.agda`` sources; ``aletheia.cabal`` lists every MAlonzo module so cabal tracks
the real ``.hs -> .so`` graph) must rebuild ``libaletheia-ffi.so`` when — and
only when — a source changes.  This gate is the behavioral regression test that
the graph stays correct.  It is the exact probe that first caught the staleness
bug the ``rm -rf`` sledgehammer was hiding:

  1. edit a known runtime string in an Agda source, ``cabal run shake -- build``,
     and assert the change REACHES the ``.so`` (a stale build would not propagate
     it — this is the failure the sledgehammer masked by always full-rebuilding);
  2. revert, rebuild, and assert the revert reaches the ``.so`` too.

The oracle is *behavioral* (does the edit reach the artifact?), never
bit-identical — an incremental build differs benignly from a from-scratch one.

Crash-safe: the edited source is always restored (atexit + SIGINT/SIGTERM), so an
interrupted run never leaves the tree mutated.  Run this as a post-``build`` step,
isolated from any other ``.so`` consumer (it transiently mutates the shared
artifact, then restores it).

Run: ``python -m tools.check_build_incremental``  (exit 0 = pass, 1 = fail).
"""

from __future__ import annotations

import sys

from tools._common import (
    emit,
    find_executable,
    install_restore_handlers,
    run_capture,
    track_inflight,
    untrack_inflight,
)
from tools._warm import REPO_ROOT

_SO = REPO_ROOT / "build" / "libaletheia-ffi.so"

# A leaf runtime string that flows verbatim into the .so's string table: the
# `uncached_atom` warning-kind label, emitted in streaming JSON output.  Anchored
# explicitly so the gate fails LOUDLY (rather than silently passing) if the string
# is ever renamed — update `_ANCHOR` to any current runtime string literal.
_ANCHOR_FILE = REPO_ROOT / "src" / "Aletheia" / "Protocol" / "ResponseFormat.agda"
_ANCHOR = '"uncached_atom"'
_SENTINEL = '"uncached_atom_ALETHEIA_STALE_PROBE"'
_TOKEN = b"ALETHEIA_STALE_PROBE"


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


def _so_contains(token: bytes) -> bool:
    """Return True iff the built ``.so``'s bytes contain ``token`` (its string table)."""
    return token in _SO.read_bytes()


def main() -> int:
    """Edit→build→assert-present, revert→build→assert-absent; restore the source always."""
    _build()  # establish a current baseline (a no-op ~0.1s when already built)
    if not _SO.exists():
        emit(f"build-incremental gate: FAIL — {_SO} was not produced")
        return 1
    if _so_contains(_TOKEN):
        emit("build-incremental gate: FAIL — stale probe sentinel left in .so by a prior run")
        return 1
    original = _ANCHOR_FILE.read_text(encoding="utf-8")
    if _ANCHOR not in original:
        emit(f"build-incremental gate: FAIL — anchor {_ANCHOR} not found in {_ANCHOR_FILE}")
        emit("  (the probe string moved; point _ANCHOR at a current runtime string literal)")
        return 1

    install_restore_handlers()
    track_inflight(str(_ANCHOR_FILE), original)
    try:
        # 1. edit -> build: the change MUST reach the .so (else the build is stale).
        _ = _ANCHOR_FILE.write_text(original.replace(_ANCHOR, _SENTINEL), encoding="utf-8")
        _build()
        if not _so_contains(_TOKEN):
            emit("build-incremental gate: FAIL — an edit did not reach the .so (STALE build)")
            return 1
        emit(f"  edit to {_ANCHOR_FILE.name} reached the .so ✓")
        # 2. revert -> build: the revert MUST reach the .so too.
        _ = _ANCHOR_FILE.write_text(original, encoding="utf-8")
        _build()
        if _so_contains(_TOKEN):
            emit("build-incremental gate: FAIL — a revert did not reach the .so (STALE build)")
            return 1
        emit(f"  revert of {_ANCHOR_FILE.name} reached the .so ✓")
    finally:
        _ = _ANCHOR_FILE.write_text(original, encoding="utf-8")
        untrack_inflight(str(_ANCHOR_FILE))

    emit("=== build-incremental gate: PASS — edit and revert both reach libaletheia-ffi.so ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())

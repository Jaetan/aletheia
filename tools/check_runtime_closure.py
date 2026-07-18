# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Pin the runtime `.so` closure to a reviewed snapshot.

``gen-ffi-modules`` auto-writes the foreign library's ``other-modules`` list in
``haskell-shim/aletheia.cabal`` from the actual Agda import graph. That makes
the cabal file the honest *generated truth* — and means a dependency drag
(one new import transitively pulling proof modules into the compiled `.so`)
updates the closure silently, visible only to a human reading the cabal diff.
Name-based checks cannot cover this: proof modules are not obliged to carry
``Properties`` in their names, and the closure legitimately contains dozens of
``Properties``-named modules (the ``@0``-erased Format-DSL round-trip proofs
and the stdlib lemma modules they pull).

This gate diffs the generated truth against a *reviewed* snapshot
(``haskell-shim/runtime-closure.snapshot``). Any change — growth or shrinkage —
fails with the exact added/removed module lists until the snapshot is
consciously regenerated (``--update``) in the same change, making every
closure edit a reviewed decision instead of a silent side effect. Added
modules whose names look proof-shaped (a ``.Properties``/``.Sound`` segment or
``Roundtrip`` in the name) are called out separately: those are the likeliest
accidental drags.

Exit codes: 0 = closure matches the snapshot (or ``--update`` wrote it);
1 = drift (or missing snapshot); 2 = could not check (vacuous input).

Run: ``python -m tools.check_runtime_closure`` (add ``--update`` after
reviewing a legitimate closure change).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tools._common import emit

CABAL_DEFAULT = Path("haskell-shim/aletheia.cabal")
SNAPSHOT_DEFAULT = Path("haskell-shim/runtime-closure.snapshot")

_MODULE_RE = re.compile(r"^\s*(MAlonzo\.Code\.[A-Za-z0-9_.']+)\s*$")
_PROOF_SHAPED_RE = re.compile(r"\.Properties(\.|$)|\.Sound(\.|$)|Roundtrip")

COULD_NOT_CHECK = 2


def closure_modules(cabal_text: str) -> list[str]:
    """Extract the sorted ``MAlonzo.Code.*`` module list from cabal text."""
    found = {m.group(1) for line in cabal_text.splitlines() if (m := _MODULE_RE.match(line))}
    return sorted(found)


def proof_shaped(module: str) -> bool:
    """Classify a module name as proof-shaped (advisory, for the error message).

    Advisory classification only — the gate fails on ANY drift; this merely
    sharpens the error message for the likeliest accidental drags.
    """
    return _PROOF_SHAPED_RE.search(module) is not None


def compare(current: list[str], pinned: list[str]) -> tuple[list[str], list[str]]:
    """Return (added, removed) of the current closure vs the pinned snapshot."""
    cur, pin = set(current), set(pinned)
    return sorted(cur - pin), sorted(pin - cur)


def main() -> int:
    """Diff the generated closure against the snapshot; ``--update`` rewrites it."""
    ap = argparse.ArgumentParser(description="Pin the runtime .so closure to a reviewed snapshot.")
    _ = ap.add_argument(
        "--update", action="store_true", help="rewrite the snapshot from the cabal closure"
    )
    _ = ap.add_argument("--cabal", type=Path, default=CABAL_DEFAULT, help="cabal file (test seam)")
    _ = ap.add_argument(
        "--snapshot", type=Path, default=SNAPSHOT_DEFAULT, help="snapshot file (test seam)"
    )
    args = ap.parse_args()

    try:
        cabal_text = args.cabal.read_text(encoding="utf-8")
    except OSError as exc:
        emit(f"check-runtime-closure: COULD NOT CHECK — cabal unreadable: {exc}")
        return COULD_NOT_CHECK

    current = closure_modules(cabal_text)
    if not current:
        emit(
            "check-runtime-closure: COULD NOT CHECK — no MAlonzo.Code.* modules "
            + f"found in {args.cabal}; a pass here would be vacuous."
        )
        return COULD_NOT_CHECK

    if args.update:
        _ = args.snapshot.write_text("\n".join(current) + "\n", encoding="utf-8")
        emit(f"check-runtime-closure: snapshot updated ({len(current)} modules).")
        return 0

    try:
        pinned = [ln for ln in args.snapshot.read_text(encoding="utf-8").splitlines() if ln.strip()]
    except OSError:
        emit(
            f"check-runtime-closure: FAIL — snapshot {args.snapshot} is missing. "
            + "Review the closure, then create it: python -m tools.check_runtime_closure --update"
        )
        return 1

    added, removed = compare(current, pinned)
    if not added and not removed:
        emit(f"check-runtime-closure: OK — closure matches the snapshot ({len(current)} modules).")
        return 0
    _report_drift(added, removed)
    return 1


def _report_drift(added: list[str], removed: list[str]) -> None:
    """Print the drift, calling out proof-shaped additions first."""
    emit("check-runtime-closure: FAIL — the runtime .so closure drifted from the snapshot.")
    proofish = [m for m in added if proof_shaped(m)]
    if proofish:
        emit("  PROOF-SHAPED additions (likeliest accidental drag — a runtime import")
        emit("  is transitively pulling proof modules into the compiled .so):")
        for m in proofish:
            emit(f"    + {m}")
    for m in added:
        if m not in proofish:
            emit(f"    + {m}")
    for m in removed:
        emit(f"    - {m}")
    emit(
        "  If every change above is intended, regenerate in the SAME change: "
        + "python -m tools.check_runtime_closure --update"
    )


if __name__ == "__main__":
    sys.exit(main())

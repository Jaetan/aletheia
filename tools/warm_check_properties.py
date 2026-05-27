#!/usr/bin/env python3
"""Warm-process check-properties: type-check all proof-only modules in ONE
`agda --interaction-json` process — stdlib + shared deps load once — instead of
N separate `agda Module.agda` invocations, each of which pays agda startup +
stdlib interface reload (~14s measured) even on a fully-warm cache.

Equivalence to batch `agda Module.agda` (verified before adopting this):
  * Cmd_load runs the FULL type-checker — a proof-obligation failure (not just a
    scope error) yields Status{checked:false} (tested: `1 ≡ 2` by `refl`).
  * Cmd_load WRITES `.agdai` (tested: delete an interface, load, it reappears),
    so downstream `build` / `check-fidelity` reuse the warm interfaces.
  * Warning behaviour matches: neither mode passes `--werror`.

Exit 0 iff every module reached Status{checked:true}; non-zero (listing the
failures) otherwise.  The module list is passed as argv by the Shakefile's
`proofModules` value (single source of truth — see `check-properties-warm`).

Run as a script so the script's own directory is on sys.path for the sibling
`warm_dead_imports` import.
"""

from __future__ import annotations

import sys
import time

from tools.warm_dead_imports import SRC, WarmAgda


def main() -> int:
    """Type-check every proof module given as argv in one warm agda process.

    Exit 0 iff all reach Status{checked:true}; else 1, listing the failures.
    """
    mods = sys.argv[1:]
    if not mods:
        print("usage: python -m tools.warm_check_properties <Module.agda> ...", file=sys.stderr)
        return 2

    t0 = time.time()
    failures: list[str] = []
    with WarmAgda() as agda:
        for i, mod in enumerate(mods, 1):
            t = time.time()
            _, ok = agda.load(str(SRC / mod))
            if not ok:
                failures.append(mod)
            status = "OK  " if ok else "FAIL"
            print(f"[{i:2d}/{len(mods)}] {time.time() - t:5.1f}s {status} {mod}", flush=True)

    elapsed = time.time() - t0
    if failures:
        print(
            f"\ncheck-properties-warm: FAILED {len(failures)}/{len(mods)} " + f"in {elapsed:.0f}s:",
            file=sys.stderr,
        )
        for mod in failures:
            print(f"  {mod}", file=sys.stderr)
        return 1
    print(
        f"\nAll {len(mods)} proof modules type-checked in {elapsed:.0f}s " + "(one warm process)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

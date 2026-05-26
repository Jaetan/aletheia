#!/usr/bin/env python3
"""Warm-process check-properties: type-check all proof-only modules in ONE
`agda --interaction-json` process — stdlib + shared deps load once — instead of
N separate `agda Module.agda` invocations, each of which pays agda startup +
stdlib interface reload (~2-3s) even on a fully-warm cache.

Equivalence to batch `agda Module.agda` (verified before adopting this):
  * Cmd_load runs the FULL type-checker — a proof-obligation failure (not just a
    scope error) yields Status{checked:false} (tested: `1 ≡ 2` by `refl`).
  * Cmd_load WRITES `.agdai` (tested: delete an interface, load, it reappears),
    so downstream `build` / `check-fidelity` reuse the warm interfaces — the
    speedup does not evaporate one step later.
  * Warning behaviour matches: neither mode passes `--werror`, so both accept
    warning-only modules (e.g. PatternShadowsConstructor) identically.

Exit 0 iff every module reached Status{checked:true}; non-zero (listing the
failures) otherwise.  Module list is passed as argv by the Shakefile's
`proofModules` value (single source of truth — see `check-properties-warm`).

Intended as the FAST inner-loop proof gate; the batch `check-properties` stays
the authority until warm and batch are seen to agree across many commits.
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from warm_dead_imports import SRC, WarmAgda  # noqa: E402  (shared warm-process driver)


def main() -> int:
    mods = sys.argv[1:]
    if not mods:
        print("usage: warm_check_properties.py <Module.agda> ...", file=sys.stderr)
        return 2

    agda = WarmAgda()
    t0 = time.time()
    failures: list[str] = []
    try:
        for i, m in enumerate(mods, 1):
            t = time.time()
            _, ok = agda.load(str(SRC / m))
            if not ok:
                failures.append(m)
            print(f"[{i:2d}/{len(mods)}] {time.time() - t:5.1f}s "
                  f"{'OK  ' if ok else 'FAIL'} {m}", flush=True)
    finally:
        agda.close()

    elapsed = time.time() - t0
    if failures:
        print(f"\ncheck-properties-warm: FAILED {len(failures)}/{len(mods)} "
              f"in {elapsed:.0f}s:", file=sys.stderr)
        for m in failures:
            print(f"  {m}", file=sys.stderr)
        return 1
    print(f"\nAll {len(mods)} proof modules type-checked in {elapsed:.0f}s "
          f"(one warm process).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

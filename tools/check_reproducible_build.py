#!/usr/bin/env python3
"""tools/check_reproducible_build.py — Reproducible-build hash gate.

Implements R18 Universal Rule UR-3 (Reproducible build verification).
Runs two clean ``cabal run shake -- build`` invocations, compares
sha256 of ``build/libaletheia-ffi.so``, fails on drift.

Drift indicates build-time non-determinism (timestamp embedding via
``__DATE__``/``__TIME__``, build-path leakage into binaries, cabal-store
ordering variance, Shake target ordering, GHC ``-fllvm`` cache pollution)
that must be tracked down — never accepted as flake.

Wall-clock cost: ~10-25 minutes (two cold builds back-to-back).  Not
wired into the default ``tools/run_ci.py`` battery; opt in via
``ALETHEIA_REPRO_CHECK=1 tools/run_ci.py``.

Exit codes:
  0 — both builds produced bit-identical libaletheia-ffi.so.
  1 — hashes differ (real reproducibility finding; track down root cause).
  2 — usage error / build failure (fail-closed; don't claim repro on a broken build).

Reference: AGENTS.md § Universal Rules → "Reproducible build verification".
"""

from __future__ import annotations

import argparse
import datetime
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from tools._common import emit, find_executable, git_toplevel, now_iso, sha256_file

ARTIFACT = Path("build/libaletheia-ffi.so")
MAX_DIFF_BYTES = 20


def _git_root() -> Path:
    try:
        return git_toplevel()
    except RuntimeError:
        _ = sys.stderr.write("check-reproducible-build: not inside a git work tree\n")
        sys.exit(2)


def _run_clean_build(label: int, work_dir: Path, copy_to: Path) -> str:
    """Clean and build; return the produced .so sha256, exiting 2 on build failure."""
    emit(f"check-reproducible-build: clean build {label} (started {now_iso()})")

    cabal = find_executable("cabal")
    clean_log = work_dir / f"clean-{label}.log"
    build_log = work_dir / f"build-{label}.log"

    with clean_log.open("w") as logf:
        rc = subprocess.run(
            [cabal, "run", "shake", "--", "clean"],
            stdout=logf,
            stderr=subprocess.STDOUT,
            check=False,
        ).returncode
    if rc != 0:
        _ = sys.stderr.write(f"check-reproducible-build: shake clean failed (build {label})\n")
        _ = sys.stderr.write(f"  log: {clean_log}\n")
        sys.exit(2)

    with build_log.open("w") as logf:
        rc = subprocess.run(
            [cabal, "run", "shake", "--", "build"],
            stdout=logf,
            stderr=subprocess.STDOUT,
            check=False,
        ).returncode
    if rc != 0:
        _ = sys.stderr.write(f"check-reproducible-build: shake build failed (build {label})\n")
        _ = sys.stderr.write(f"  log: {build_log}\n")
        sys.exit(2)

    if not ARTIFACT.is_file():
        _ = sys.stderr.write(f"check-reproducible-build: {ARTIFACT} missing after build {label}\n")
        sys.exit(2)

    shutil.copy2(ARTIFACT, copy_to)
    return sha256_file(copy_to)


def _emit_diff_bytes(work_dir: Path) -> None:
    """Write the first differing-byte offsets to stderr, mirroring ``cmp -l``."""
    lib1 = work_dir / "lib1.so"
    lib2 = work_dir / "lib2.so"
    if not (lib1.is_file() and lib2.is_file()):
        return

    _ = sys.stderr.write(
        f"First {MAX_DIFF_BYTES} differing bytes (offset, build1, build2):\n",
    )
    with lib1.open("rb") as f1, lib2.open("rb") as f2:
        offset = 1  # cmp -l uses 1-based offsets
        shown = 0
        while shown < MAX_DIFF_BYTES:
            b1 = f1.read(1)
            b2 = f2.read(1)
            if not b1 and not b2:
                break
            if b1 != b2:
                # Format mirrors `cmp -l`: octal byte values.
                v1 = f"{b1[0]:o}" if b1 else "???"
                v2 = f"{b2[0]:o}" if b2 else "???"
                _ = sys.stderr.write(f"  {offset:>10}  {v1:>4}  {v2:>4}\n")
                shown += 1
            offset += 1
    _ = sys.stderr.write("\n")


def _emit_failure(hash1: str, hash2: str, work_dir: Path, *, keep: bool) -> None:
    _ = sys.stderr.write(
        "check-reproducible-build: FAIL — libaletheia-ffi.so is not "
        + "bit-identical across two clean builds.\n\n"
        + f"  build 1: {hash1}\n"
        + f"  build 2: {hash2}\n\n",
    )

    # First 20 differing-byte offsets, for forensic anchoring.  Mirror the
    # bash gate's `cmp -l` behavior with native Python.
    _emit_diff_bytes(work_dir)

    _ = sys.stderr.write(
        "Common reproducibility hazards (priority order):\n"
        + "  1. Build-path leakage (developer absolute paths in debug info).\n"
        + "     Fix: ensure -ffile-prefix-map=$PWD=. is in cabal ghc-options.\n"
        + "  2. Timestamp embedding via __DATE__/__TIME__ in C/C++ sources.\n"
        + "     Fix: pass -Wno-date-time / -Wdate-time to surface them.\n"
        + "  3. Cabal store ordering variance / GHC -fllvm cache pollution.\n"
        + "     Fix: pin cabal-version + freeze cabal.project.freeze.\n"
        + "  4. Filesystem-order dependence in Shake's getDirectoryFiles.\n"
        + "     Fix: sort the result list before consuming it.\n"
        + "\n",
    )
    if keep:
        _ = sys.stderr.write(f"Artifacts retained at {work_dir} (--keep-artifacts).\n")
    else:
        _ = sys.stderr.write(
            f"Re-run with --keep-artifacts to retain {work_dir} for forensic diff.\n",
        )
    _ = sys.stderr.write(
        "Reference: AGENTS.md § Universal Rules → Reproducible build verification.\n",
    )


def _run_two_builds(work_dir: Path) -> tuple[str, str]:
    """Run two clean builds and return their .so hashes, emitting timing lines."""
    start = datetime.datetime.now(datetime.UTC)
    hash1 = _run_clean_build(1, work_dir, work_dir / "lib1.so")
    mid = datetime.datetime.now(datetime.UTC)
    emit(
        f"check-reproducible-build: build 1 sha256 {hash1} "
        + f"({(mid - start).total_seconds():.0f}s)",
    )

    hash2 = _run_clean_build(2, work_dir, work_dir / "lib2.so")
    end = datetime.datetime.now(datetime.UTC)
    emit(
        f"check-reproducible-build: build 2 sha256 {hash2} "
        + f"({(end - mid).total_seconds():.0f}s; "
        + f"total {(end - start).total_seconds():.0f}s)",
    )
    return hash1, hash2


def _synthesize_mismatch(work_dir: Path) -> tuple[str, str]:
    """Skip the real builds and fabricate a mismatch for failure-path testing."""
    emit(
        "check-reproducible-build: TEST-FAIL mode — synthesizing "
        + "mismatch (real builds skipped)",
    )
    hash1 = "0" * 64
    hash2 = "f" * 64
    _ = (work_dir / "lib1.so").write_bytes(b"")
    _ = (work_dir / "lib2.so").write_bytes(b"\x01")
    return hash1, hash2


def main() -> int:
    """Run the gate: parse args, perform the two builds, compare, report."""
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n", maxsplit=1)[0])
    ap.add_argument(
        "--keep-artifacts",
        action="store_true",
        help="retain the temp shadow trees on exit (for forensic diff)",
    )
    ap.add_argument(
        "--test-fail",
        action="store_true",
        help=(
            "skip the two real builds and synthesise a mismatch — used by "
            "gate-shape verification per "
            "memory/feedback_orchestrator_end_to_end_validation.md.  Real "
            "non-reproducibility is hard to provoke artificially, so this flag "
            "exists to exercise the failure path in seconds."
        ),
    )
    args = ap.parse_args()

    repo_root = _git_root()
    if not (repo_root / "Shakefile.hs").is_file():
        _ = sys.stderr.write(
            "check-reproducible-build: Shakefile.hs not found in repo root — "
            + "wrong working directory?\n",
        )
        return 2

    # Run from repo root so cabal/shake/git invocations all see the right tree.
    os.chdir(repo_root)

    work_dir = Path(tempfile.mkdtemp(prefix="aletheia-repro-"))
    emit(f"check-reproducible-build: scratch dir {work_dir}")

    try:
        if args.test_fail:
            hash1, hash2 = _synthesize_mismatch(work_dir)
        else:
            hash1, hash2 = _run_two_builds(work_dir)

        if hash1 == hash2:
            emit(f"check-reproducible-build: ok ({hash1})")
            return 0

        _emit_failure(hash1, hash2, work_dir, keep=args.keep_artifacts)
        return 1
    finally:
        if not args.keep_artifacts:
            shutil.rmtree(work_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())

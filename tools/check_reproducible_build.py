# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_reproducible_build.py — Reproducible-build hash gate.

Implements reproducible build verification.  Builds over what the tree
holds, then runs two clean ``cabal run shake -- build`` invocations, and
compares the sha256 of ``build/libaletheia-ffi.so`` after each: the two clean
builds must agree, and the tree's build must agree with them.

Drift indicates build-time non-determinism (timestamp embedding via
``__DATE__``/``__TIME__``, build-path leakage into binaries, cabal-store
ordering variance, Shake target ordering, GHC ``-fllvm`` cache pollution)
that must be tracked down — never accepted as flake.  Drift between the
tree's build and the clean ones means bytes that depend on what was built
before: a module compiled on its own giving other objects than in a clean
build, which the kernel's ``-fobject-determinism`` is there to prevent and the build-id
comparison of ``tools/check_install_freshness.py`` rests on.  GitHub's job
restores the build tree its sweep saved before this runs, so its tree's build
is an incremental one; on a fresh checkout it is a third clean build.

Every command of each build runs under ``run_guarded``, so a build stops when
the gate dies, SIGKILL included, rather than holding Shake's lock after it.

Wall-clock cost: ~10-25 minutes (two cold builds back-to-back, after the
tree's own build).  Not
wired into the default ``tools/run_ci.py`` battery; opt in via
``ALETHEIA_REPRO_CHECK=1 tools/run_ci.py``.

Exit codes:
  0 — the three builds produced one bit-identical libaletheia-ffi.so.
  1 — two clean builds differ, or the tree's build differs from them (a real
      reproducibility finding; track down root cause).
  2 — usage error / build failure (fail-closed; don't claim repro on a broken build).

Reference: AGENTS.md § Universal Rules → "Reproducible build verification".
"""

from __future__ import annotations

import argparse
import datetime as dt
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import NewType

from tools._common import (
    emit,
    find_executable,
    git_toplevel,
    now_iso,
    run_guarded,
    sha256_file,
)
from tools._progress import ItemCount, report, reporting

from aletheia.common_types import Prose

ARTIFACT = Path("build/libaletheia-ffi.so")
# The sha256 of a built library, as hex.
LibraryDigest = NewType("LibraryDigest", str)
# Which build a run is: 0 the tree's own, 1 and 2 the clean ones.
BuildLabel = NewType("BuildLabel", int)
MAX_DIFF_BYTES = 20


def _git_root() -> Path:
    try:
        return git_toplevel()
    except RuntimeError:
        _ = sys.stderr.write("check-reproducible-build: not inside a git work tree\n")
        sys.exit(2)


def _build_and_copy(label: BuildLabel, work_dir: Path, copy_to: Path) -> LibraryDigest:
    """Build; copy the .so to ``copy_to`` and return its sha256, exiting 2 on build failure."""
    build_log = work_dir / f"build-{label}.log"
    with build_log.open("w") as logf:
        words = [find_executable("cabal"), "run", "shake", "--", "build"]
        rc = run_guarded(words, output=logf).returncode
    if rc != 0:
        _ = sys.stderr.write(f"check-reproducible-build: shake build failed (build {label})\n")
        _ = sys.stderr.write(f"  log: {build_log}\n")
        sys.exit(2)

    if not ARTIFACT.is_file():
        _ = sys.stderr.write(f"check-reproducible-build: {ARTIFACT} missing after build {label}\n")
        sys.exit(2)

    shutil.copy2(ARTIFACT, copy_to)
    return LibraryDigest(sha256_file(copy_to))


def _run_tree_build(work_dir: Path, copy_to: Path) -> LibraryDigest:
    """Build over what the tree holds; return the .so's sha256, exiting 2 on build failure."""
    held = "over the library it holds" if ARTIFACT.is_file() else "the tree holding no library"
    emit(f"check-reproducible-build: the tree's own build, {held} (started {now_iso()})")
    return _build_and_copy(BuildLabel(0), work_dir, copy_to)


def _run_clean_build(label: BuildLabel, work_dir: Path, copy_to: Path) -> LibraryDigest:
    """Clean and build; return the produced .so sha256, exiting 2 on build failure."""
    emit(f"check-reproducible-build: clean build {label} (started {now_iso()})")

    clean_log = work_dir / f"clean-{label}.log"
    with clean_log.open("w") as logf:
        words = [find_executable("cabal"), "run", "shake", "--", "clean"]
        rc = run_guarded(words, output=logf).returncode
    if rc != 0:
        _ = sys.stderr.write(f"check-reproducible-build: shake clean failed (build {label})\n")
        _ = sys.stderr.write(f"  log: {clean_log}\n")
        sys.exit(2)
    return _build_and_copy(label, work_dir, copy_to)


def _emit_diff_bytes(first: Path, second: Path) -> None:
    """Write the first differing-byte offsets of two libraries to stderr, mirroring ``cmp -l``."""
    if not (first.is_file() and second.is_file()):
        return

    _ = sys.stderr.write(
        f"First {MAX_DIFF_BYTES} differing bytes (offset, {first.stem}, {second.stem}):\n",
    )
    with first.open("rb") as f1, second.open("rb") as f2:
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


def _emit_kept(work_dir: Path, *, keep: bool) -> None:
    """Say where the libraries are kept, or how to keep them."""
    if keep:
        _ = sys.stderr.write(f"Artifacts retained at {work_dir} (--keep-artifacts).\n")
    else:
        _ = sys.stderr.write(
            f"Re-run with --keep-artifacts to retain {work_dir} for forensic diff.\n",
        )


def _emit_failure(
    hash1: LibraryDigest, hash2: LibraryDigest, work_dir: Path, *, keep: bool
) -> None:
    _ = sys.stderr.write(
        "check-reproducible-build: FAIL — libaletheia-ffi.so is not "
        + "bit-identical across two clean builds.\n\n"
        + f"  build 1: {hash1}\n"
        + f"  build 2: {hash2}\n\n",
    )

    # First 20 differing-byte offsets, for forensic anchoring.  Mirror the
    # bash gate's `cmp -l` behavior with native Python.
    _emit_diff_bytes(work_dir / "lib1.so", work_dir / "lib2.so")

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
    _emit_kept(work_dir, keep=keep)
    _ = sys.stderr.write(
        "Reference: AGENTS.md § Universal Rules → Reproducible build verification.\n",
    )


def _emit_history_failure(
    tree: LibraryDigest, clean: LibraryDigest, work_dir: Path, *, keep: bool
) -> None:
    _ = sys.stderr.write(
        "check-reproducible-build: FAIL: the library the tree's own build left is not the one "
        + "a clean build makes from the same sources.\n\n"
        + f"  the tree's build: {tree}\n"
        + f"  clean build:      {clean}\n\n",
    )
    _emit_diff_bytes(work_dir / "lib0.so", work_dir / "lib1.so")
    _ = sys.stderr.write(
        "Either a build's bytes depend on what was built before it (a module compiled on\n"
        + "its own giving other objects than in a clean build, which the kernel's\n"
        + "-fobject-determinism in haskell-shim/aletheia.cabal is there to prevent), or the\n"
        + "tree's build kept something stale (which the staleness gate exists to catch).\n"
        + "check-install-freshness compares a deployed copy with build/ by build-id, so\n"
        + "either breaks it.\n\n",
    )
    _emit_kept(work_dir, keep=keep)


# The tree's build and the two clean builds, in the order they run.
Builds = tuple[LibraryDigest, LibraryDigest, LibraryDigest]


def run_builds(work_dir: Path) -> Builds:
    """Build over the tree, then twice from clean; return the three hashes, with timing lines."""
    start = dt.datetime.now(dt.UTC)
    report(ItemCount(0), ItemCount(3), Prose("builds"))
    tree = _run_tree_build(work_dir, work_dir / "lib0.so")
    report(ItemCount(1), ItemCount(3), Prose("builds"))
    built = dt.datetime.now(dt.UTC)
    emit(
        f"check-reproducible-build: the tree's build sha256 {tree} "
        + f"({(built - start).total_seconds():.0f}s)",
    )

    hash1 = _run_clean_build(BuildLabel(1), work_dir, work_dir / "lib1.so")
    report(ItemCount(2), ItemCount(3), Prose("builds"))
    mid = dt.datetime.now(dt.UTC)
    emit(
        f"check-reproducible-build: build 1 sha256 {hash1} "
        + f"({(mid - built).total_seconds():.0f}s)",
    )

    hash2 = _run_clean_build(BuildLabel(2), work_dir, work_dir / "lib2.so")
    report(ItemCount(3), ItemCount(3), Prose("builds"))
    end = dt.datetime.now(dt.UTC)
    emit(
        f"check-reproducible-build: build 2 sha256 {hash2} "
        + f"({(end - mid).total_seconds():.0f}s; "
        + f"total {(end - start).total_seconds():.0f}s)",
    )
    return tree, hash1, hash2


def judge(work_dir: Path, builds: Builds, *, keep: bool) -> int:
    """Return 0 when the three builds made one library; report the disagreement and return 1."""
    tree, hash1, hash2 = builds
    if hash1 != hash2:
        _emit_failure(hash1, hash2, work_dir, keep=keep)
        return 1
    if tree != hash1:
        _emit_history_failure(tree, hash1, work_dir, keep=keep)
        return 1
    emit(f"check-reproducible-build: ok ({hash1})")
    return 0


def _synthesize_mismatch(work_dir: Path) -> Builds:
    """Skip the real builds and fabricate a mismatch for failure-path testing."""
    emit(
        "check-reproducible-build: TEST-FAIL mode — synthesizing "
        + "mismatch (real builds skipped)",
    )
    _ = (work_dir / "lib0.so").write_bytes(b"")
    _ = (work_dir / "lib1.so").write_bytes(b"")
    _ = (work_dir / "lib2.so").write_bytes(b"\x01")
    return LibraryDigest("0" * 64), LibraryDigest("0" * 64), LibraryDigest("f" * 64)


def main() -> int:
    """Run the gate: parse args, perform the three builds, compare, report."""
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
            "skip the real builds and synthesise a mismatch — used by "
            "gate-shape verification to prove this gate actually fails.  Real "
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
        builds = _synthesize_mismatch(work_dir) if args.test_fail else run_builds(work_dir)
        return judge(work_dir, builds, keep=args.keep_artifacts)
    finally:
        if not args.keep_artifacts:
            shutil.rmtree(work_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(reporting(main, Prose("check-reproducible-build")))

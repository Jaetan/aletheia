# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_gate_claim.py — Enforce gate-claim integrity.

Mechanical enforcer for ``memory/feedback_gate_claim_integrity.md``.  When
a commit message contains a gate-clean assertion ("all gates clean",
"gates green", etc.), verify that ``build/libaletheia-ffi.so`` mtime
postdates every build-relevant staged source file's mtime — i.e., the
gates the commit claims to have run on actually observed the post-edit
state.

Usage::

    tools/check_gate_claim.py                # default: HEAD (read HEAD's message)
    tools/check_gate_claim.py HEAD           # post-commit mode (read HEAD's message)
    tools/check_gate_claim.py <commit-hash>  # audit mode (read named commit's message)

Strategy:
  1. Identify commit message + diffed files (mode-dependent).
  2. Pattern-match the message for gate-claim phrases.  If no claim, exit 0.
  3. Filter diff to build-relevant paths (Agda src, Shakefile, haskell-shim).
  4. If filter is empty, exit 0 (doc-only / binding-only edits don't
     invalidate the .so).
  5. Compare each build-relevant file's mtime against build/libaletheia-ffi.so
     mtime.  Any file newer than the .so → fail with diagnostic.

Exit codes:
  0 — no claim, OR claim with stale-file-free state.
  1 — claim made but .so missing or stale relative to build-relevant edits.
  2 — usage error / git failure.

v0 limitations (deliberate; documented for the v1+ artifact-based design):
  * mtime-based, not artifact-based.  A v1+ design will require an attached
    ``tools/ci-output/<sha>.log`` artifact emitted by the offline CI
    orchestrator with content asserting the full gate sweep succeeded.
  * Edge case: post-``git checkout`` mtime resets all files to checkout
    time.  The check therefore noisily fails right after a fresh clone or
    branch switch.  Acceptable v0: the enforcer is only load-bearing at
    commit time on the dev's actual working state.
  * Claim phrases are conservative.  Specific gate-output lines like
    "check-properties ✓" don't match; only broader "all gates" / "gates
    green" / "All N gates" assertions trigger the freshness check.
"""

from __future__ import annotations

import argparse
import datetime
import re
import sys
from pathlib import Path

from tools._common import emit, find_executable, run_capture

_GIT = find_executable("git")

GATE_CLAIM_PATTERN = re.compile(
    r"([Aa]ll [0-9]* ?[Aa]gda gates (clean|green|passed))"
    + r"|([Aa]ll gates (clean|green|passed))"
    + r"|([Gg]ates? (green|clean)\b)"
    + r"|(All proof modules type-checked successfully)",
)

BUILD_RELEVANT_PATTERN = re.compile(
    r"(^src/.*\.agda$)"
    + r"|(^Shakefile\.hs$)"
    + r"|(^haskell-shim/.*\.(hs|cabal)$)"
    + r"|(^aletheia\.agda-lib$)",
)

SO_PATH = Path("build/libaletheia-ffi.so")

_MTIME_FORMAT = "%Y-%m-%d %H:%M:%S"


def _format_mtime(epoch: float) -> str:
    """Render a mtime epoch as a local-time ``YYYY-MM-DD HH:MM:SS`` string."""
    aware = datetime.datetime.fromtimestamp(epoch, tz=datetime.UTC)
    return aware.astimezone().strftime(_MTIME_FORMAT)


def _git(*args: str) -> tuple[int, str]:
    out = run_capture([_GIT, *args])
    return out.returncode, out.stdout


def _resolve_mode(mode: str) -> tuple[str, list[str]]:
    """Return (commit message, diffed files) for the given mode.

    Modes read an ALREADY-WRITTEN commit, which is what makes them checkable:
    a message only exists once the commit does.  There is deliberately no
    ``pre-commit`` mode — ``pre-commit`` runs before the message is composed, so
    it could only ever read the PREVIOUS commit's ``.git/COMMIT_EDITMSG`` and
    would validate the wrong message.  Commit-time enforcement, if wanted, must
    hang off ``commit-msg``, which receives the real message path as an argument.
    """
    if mode in ("HEAD", "post-commit"):
        rc, msg = _git("log", "-1", "--format=%B", "HEAD")
        if rc != 0:
            _ = sys.stderr.write("check-gate-claim: failed to read HEAD message\n")
            sys.exit(2)
        rc, files = _git("diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD")
        if rc != 0:
            _ = sys.stderr.write("check-gate-claim: failed to read HEAD diff\n")
            sys.exit(2)
        return msg, [line for line in files.splitlines() if line]

    # Treat as a commit hash / ref
    rc, _ = _git("rev-parse", "--verify", mode)
    if rc != 0:
        _ = sys.stderr.write(
            "check-gate-claim: usage: check_gate_claim.py "
            + f"[HEAD|<commit-hash>]  (got {mode!r})\n"
        )
        sys.exit(2)
    rc, msg = _git("log", "-1", "--format=%B", mode)
    if rc != 0:
        sys.exit(2)
    rc, files = _git("diff-tree", "--no-commit-id", "--name-only", "-r", mode)
    if rc != 0:
        sys.exit(2)
    return msg, [line for line in files.splitlines() if line]


def main() -> int:
    """Run the gate-claim freshness check and return the process exit code."""
    ap = argparse.ArgumentParser(
        description="tools/check_gate_claim.py — Enforce gate-claim integrity.",
    )
    ap.add_argument(
        "mode",
        nargs="?",
        default="HEAD",
        help="HEAD (default) | <commit-hash>",
    )
    args = ap.parse_args()

    msg, diff_files = _resolve_mode(args.mode)

    if not GATE_CLAIM_PATTERN.search(msg):
        # No claim in the message; freshness invariant doesn't apply.
        return 0

    build_relevant = [f for f in diff_files if BUILD_RELEVANT_PATTERN.search(f)]
    if not build_relevant:
        # Doc-only / binding-only / lint-config-only commit.
        return 0

    if not SO_PATH.is_file():
        _ = sys.stderr.write(
            "check-gate-claim: FAIL — commit claims gates clean but "
            + f"{SO_PATH} does not exist.\n\n"
            + "The gate runs in the commit message must have produced the .so artifact.\n"
            + "Run `cabal run shake -- build` to produce it, then re-run the gates\n"
            + "the message asserts.\n\n"
            + "Reference: memory/feedback_gate_claim_integrity.md\n"
        )
        return 1

    so_mtime = SO_PATH.stat().st_mtime
    stale: list[tuple[str, float]] = []
    for f in build_relevant:
        p = Path(f)
        if p.is_file():
            f_mtime = p.stat().st_mtime
            if f_mtime > so_mtime:
                stale.append((f, f_mtime))

    if stale:
        so_mtime_str = _format_mtime(so_mtime)
        _ = sys.stderr.write(
            "check-gate-claim: FAIL — gate-clean claim made without fresh "
            + "build artifact.\n\n"
            + f"build/libaletheia-ffi.so mtime: {so_mtime_str}\n\n"
            + "Build-relevant source files NEWER than the .so:\n"
        )
        for f, m in stale:
            ts = _format_mtime(m)
            _ = sys.stderr.write(f"  {f} (mtime {ts})\n")
        _ = sys.stderr.write(
            "\n"
            + "The gate runs the commit message asserts must have observed these source\n"
            + "files.  Re-run the affected gates BEFORE committing the claim:\n\n"
            + "  cabal run shake -- build\n"
            + "  cabal run shake -- check-properties\n"
            + "  cabal run shake -- check-invariants\n"
            + "  cabal run shake -- check-no-properties-in-runtime\n"
            + "  cabal run shake -- check-erasure\n"
            + "  cabal run shake -- check-fidelity\n"
            + "  cabal run shake -- check-ffi-exports\n"
            + "  cabal run shake -- count-modules\n\n"
            + "Reference: memory/feedback_gate_claim_integrity.md\n"
        )
        return 1

    emit("check-gate-claim: ok (.so mtime postdates all build-relevant staged files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_gate_claim.py — Enforce gate-claim integrity.

A commit whose message asserts that the gates are clean ("all gates clean",
"gates green", and the like) must be backed by a sweep that observed the
build sources it commits.  The evidence is provenance the offline CI
orchestrator (``tools/run_ci.py``) writes, keyed to content: every sweep
records a digest of the build sources it observed, and this check asks
whether a successful sweep recorded the digest of the commit under audit.
Nothing here reads a timestamp.  A checkout, a clone or a cache restore
rewrites every mtime and moves no content, so the same tree carries the same
digest wherever it is checked.

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
  5. Compute the commit's build-source digest and look for a sweep that
     recorded it: the sweep this check runs inside, which exports the digest
     of the working tree it observes in ``ALETHEIA_GATE_SOURCES``, or a
     finished log under ``tools/ci-output/`` whose header carries the digest
     and whose summary says every step passed.  Neither → fail with
     diagnostic.

The digest is the SHA-256 over the sorted ``<blob id> <path>`` lines of every
build-relevant path, so it is the content identity git itself assigns and
the orchestrator computes it from the working tree with the same function
this check applies to the commit: the two sides cannot disagree about what
the key covers.  A record is a statement by the orchestrator, keyed to
content so it cannot be true by accident; a ``--fast`` sweep runs a subset
and records no digest.

Exit codes:
  0 — no claim, OR claim with a sweep record over the commit's build sources.
  1 — claim made but no successful sweep recorded these build sources.
  2 — usage error / git failure.

Claim phrases are conservative.  Specific gate-output lines like
"check-properties ✓" don't match; only broader "all gates" / "gates green" /
"All N gates" assertions trigger the check.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
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

# The variable a running sweep exports, holding the digest of the build sources
# it observes, and the directory its finished logs land in.
SOURCES_ENV = "ALETHEIA_GATE_SOURCES"
LOG_DIR = Path("tools") / "ci-output"

# The lines a finished log carries: the digest in its header, the verdict in its
# summary.  The orchestrator writes both through these constants, so the reader
# and the writer are one definition.
SOURCES_LINE = "Sources:  "
SOURCES_UNRECORDED = "none (a fast-tier sweep runs a subset)"
PASSED_LINE = re.compile(r"^Result:   ALL \d+ STEPS PASSED$")

_DIGEST = re.compile(r"^[0-9a-f]{64}$")
# A log's header and summary sit within this many lines of its two ends.
_HEAD_LINES = 16
_TAIL_BYTES = 1024


def _git(*args: str, cwd: Path | None = None) -> tuple[int, str]:
    out = run_capture([_GIT, *args], cwd=cwd)
    return out.returncode, out.stdout


def _digest(entries: list[tuple[str, str]]) -> str:
    """Digest ``(blob id, path)`` pairs, order-free, as the build-source key."""
    lines = sorted(f"{blob} {path}" for blob, path in entries)
    return hashlib.sha256("\n".join(lines).encode()).hexdigest()


def sources_digest_of_revision(revision: str, *, repo: Path | None = None) -> str:
    """Return the build-source digest of ``revision``'s tree.

    Raises ``RuntimeError`` when git cannot list the tree.
    """
    rc, listing = _git("ls-tree", "-r", revision, cwd=repo)
    if rc != 0:
        message = f"cannot list the tree of {revision}"
        raise RuntimeError(message)
    entries: list[tuple[str, str]] = []
    for line in listing.splitlines():
        meta, _, path = line.partition("\t")
        if BUILD_RELEVANT_PATTERN.search(path):
            entries.append((meta.split()[2], path))
    return _digest(entries)


def sources_digest_of_worktree(repo: Path | None = None) -> str:
    """Return the build-source digest of the working tree at ``repo``.

    The paths are the tracked ones and the untracked ones git does not ignore,
    since a module not yet added is still one the build compiles; a tracked
    path deleted from the working tree is not there to observe and is left
    out.  Each blob id is the one git would give the file's content, so a
    clean checkout digests to its commit.
    """
    rc, listing = _git("ls-files", "--cached", "--others", "--exclude-standard", cwd=repo)
    if rc != 0:
        message = "cannot list the working tree"
        raise RuntimeError(message)
    root = repo if repo is not None else Path()
    paths = [
        path
        for path in listing.splitlines()
        if BUILD_RELEVANT_PATTERN.search(path) and (root / path).is_file()
    ]
    if not paths:
        return _digest([])
    return _digest(list(zip(_hash_paths(paths, repo), paths, strict=True)))


def _hash_paths(paths: list[str], repo: Path | None) -> list[str]:
    """Return git's blob id for each path's working-tree content, in order."""
    proc = subprocess.run(
        [_GIT, "hash-object", "--stdin-paths"],
        input="\n".join(paths) + "\n",
        capture_output=True,
        text=True,
        cwd=repo,
        check=False,
    )
    if proc.returncode != 0:
        message = f"git hash-object failed: {proc.stderr.strip()}"
        raise RuntimeError(message)
    return proc.stdout.split()


def _log_records(log_dir: Path) -> set[str]:
    """Return the digests of every finished, fully passed sweep log in ``log_dir``.

    Only the head and the tail of each log are read: the header carries the
    digest and the summary the verdict, and a log is evidence only when the
    same file carries both.
    """
    digests: set[str] = set()
    if not log_dir.is_dir():
        return digests
    for log in log_dir.glob("*.log"):
        digest = _recorded_digest(log)
        if digest is not None and _passed(log):
            digests.add(digest)
    return digests


def _recorded_digest(log: Path) -> str | None:
    """Return the digest a log's header records, or None when it records none."""
    try:
        with log.open(encoding="utf-8", errors="replace") as handle:
            for _ in range(_HEAD_LINES):
                line = handle.readline()
                if not line:
                    return None
                if line.startswith(SOURCES_LINE):
                    value = line[len(SOURCES_LINE) :].strip()
                    return value if _DIGEST.match(value) else None
    except OSError:
        return None
    return None


def _passed(log: Path) -> bool:
    """Return whether a log's summary says every step of its sweep passed."""
    try:
        with log.open("rb") as handle:
            _ = handle.seek(0, os.SEEK_END)
            size = handle.tell()
            _ = handle.seek(max(0, size - _TAIL_BYTES))
            tail = handle.read().decode("utf-8", errors="replace")
    except OSError:
        return False
    return any(PASSED_LINE.match(line) for line in tail.splitlines())


def evidence_for(digest: str, *, log_dir: Path, environ: dict[str, str]) -> str | None:
    """Name the record covering ``digest``, or None when no sweep recorded it.

    The running sweep is asked first, since inside a sweep no finished log of
    it exists yet; then the finished logs.
    """
    running = environ.get(SOURCES_ENV)
    if running == digest:
        return "the running sweep observes these build sources"
    if digest in _log_records(log_dir):
        return f"a passed sweep under {log_dir} recorded these build sources"
    return None


def _resolve_mode(mode: str) -> tuple[str, list[str]]:
    """Return (commit message, diffed files) for the given mode.

    Modes read an ALREADY-WRITTEN commit, which is what makes them checkable:
    a message only exists once the commit does.  The diff is taken with
    ``--root`` so a repository's first commit lists what it adds rather than
    nothing, which would let a claim on it pass unread.  There is deliberately no
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
        rc, files = _git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", "HEAD")
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
    rc, files = _git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", mode)
    if rc != 0:
        sys.exit(2)
    return msg, [line for line in files.splitlines() if line]


def main() -> int:
    """Run the gate-claim provenance check and return the process exit code."""
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
        # No claim in the message; the provenance invariant doesn't apply.
        return 0

    build_relevant = [f for f in diff_files if BUILD_RELEVANT_PATTERN.search(f)]
    if not build_relevant:
        # Doc-only / binding-only / lint-config-only commit.
        return 0

    rc, toplevel = _git("rev-parse", "--show-toplevel")
    if rc != 0:
        _ = sys.stderr.write("check-gate-claim: not inside a git work tree\n")
        return 2
    root = Path(toplevel.strip())
    revision = "HEAD" if args.mode == "post-commit" else args.mode
    try:
        digest = sources_digest_of_revision(revision, repo=root)
    except RuntimeError as exc:
        _ = sys.stderr.write(f"check-gate-claim: {exc}\n")
        return 2

    evidence = evidence_for(digest, log_dir=root / LOG_DIR, environ=dict(os.environ))
    if evidence is None:
        running = os.environ.get(SOURCES_ENV)
        observed = (
            f"the running sweep observes build sources {running},\n"
            + "which are not the commit's: the working tree carries a build-relevant\n"
            + "edit the commit does not, or lacks one it has.\n"
            if running is not None
            else "no sweep is running, and no passed log under\n"
            + f"{root / LOG_DIR} records this digest.\n"
        )
        _ = sys.stderr.write(
            "check-gate-claim: FAIL — gate-clean claim made without a sweep "
            + "over the commit's build sources.\n\n"
            + f"build sources of {revision}: {digest}\n"
            + observed
            + "\nBuild-relevant files the commit changes:\n"
            + "".join(f"  {f}\n" for f in build_relevant)
            + "\nThe sweep the message asserts must have observed the committed\n"
            + "sources.  Run it at this tree; its log is the evidence:\n\n"
            + "  tools/run_ci.py\n"
        )
        return 1

    emit(f"check-gate-claim: ok ({evidence})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

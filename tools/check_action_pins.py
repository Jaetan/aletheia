# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""tools/check_action_pins.py — Verify action-pin policy on GHA workflows.

Aletheia's action-pin policy:
  * GitHub-owned actions (``actions/*``, ``github/*``) — ``@v<n>`` tag
    accepted.  These are first-party, less risk of supply-chain compromise;
    tags are stable enough.
  * All other actions — must be SHA-pinned (40-char hex commit hash) to
    defend against supply-chain attacks where a tag is moved to a
    malicious commit.

Reference: GitHub Security Hardening for GitHub Actions (Sept 2022),
advisory after the tj-actions/changed-files compromise.

Runs as both:
  * Offline (pre-push hook via ``tools/run_ci.py``, manual invocation).
  * Push-time (GHA workflow ``.github/workflows/gha-checks.yml``).

Exit codes:
  0 — all ``uses:`` references comply with the pin policy.
  1 — at least one ``uses:`` reference violates the policy.
  2 — no ``.github/workflows/`` directory (skips silently with exit 0).
"""

from __future__ import annotations

import re
import sys

from tools._common import emit, git_toplevel

USES_RE = re.compile(r"uses:\s*(\S+?)@(\S+)")
SHA_RE = re.compile(r"^[a-f0-9]{40}$")
BRANCH_REF_RE = re.compile(r"^(main|master|develop|HEAD)$")

LOCAL_PREFIXES = ("./", "docker://")
GITHUB_OWNED_PREFIXES = ("actions/", "github/")


def _classify(repo: str, ref: str) -> str | None:
    """Return the pin-policy violation reason for ``repo@ref``, or ``None``.

    ``None`` means the reference complies (or is a skipped local/docker ref).
    The returned string is the parenthetical reason appended to a violation
    line by the caller, which holds the workflow path and repo-root context.
    """
    # Skip local + docker references.
    if repo.startswith(LOCAL_PREFIXES):
        return None

    # GitHub-owned: tag OK, branch ref forbidden.
    if repo.startswith(GITHUB_OWNED_PREFIXES):
        if BRANCH_REF_RE.match(ref):
            return "(branch ref disallowed even for github-owned)"
        return None

    # Third-party: must be SHA-pinned.
    if not SHA_RE.match(ref):
        return "(third-party — must be SHA-pinned, not tag/branch)"
    return None


def main() -> int:
    """Verify every workflow ``uses:`` reference against the action-pin policy.

    Returns the process exit code (0 compliant, 1 violation, 2 no git repo).
    """
    try:
        repo_root = git_toplevel()
    except RuntimeError:
        _ = sys.stderr.write("check-action-pins: not inside a git repo\n")
        return 2

    workflows_dir = repo_root / ".github" / "workflows"
    if not workflows_dir.is_dir():
        emit(f"check-action-pins: {workflows_dir} does not exist; skipping")
        return 0

    violations: list[str] = []
    checked = 0

    for workflow in sorted(workflows_dir.glob("*.y*ml")):
        for line in workflow.read_text(encoding="utf-8").splitlines():
            m = USES_RE.search(line)
            if not m:
                continue
            repo, ref = m.group(1), m.group(2)
            checked += 1

            reason = _classify(repo, ref)
            if reason is not None:
                violations.append(
                    f"  {workflow.relative_to(repo_root)}: {repo}@{ref} " + reason,
                )

    if violations:
        _ = sys.stderr.write(
            "check-action-pins: FAIL — action-pin policy violations detected.\n\n"
            + "Pin policy:\n"
            + "  * GitHub-owned (actions/*, github/*) — @v<n> tag accepted (no branch refs)\n"
            + "  * Third-party — must be SHA-pinned (40-char hex)\n\n"
            + f"Violations ({checked} refs checked):\n",
        )
        _ = sys.stderr.write("\n".join(violations) + "\n")
        _ = sys.stderr.write(
            "\n"
            + "Fix: replace tag refs with the underlying SHA.  Look up via:\n"
            + "  gh api repos/<owner>/<name>/git/ref/tags/<tag> --jq .object.sha\n\n"
            + "Reference: GitHub Security Hardening for GitHub Actions.\n",
        )
        return 1

    emit(f"check-action-pins: ok ({checked} refs checked, all comply with pin policy)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

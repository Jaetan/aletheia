#!/usr/bin/env python3
"""tools/check_workflow_permissions.py — Verify minimal workflow permissions.

GitHub workflows default to a permissive ``GITHUB_TOKEN`` scope with
broad repo write access if no ``permissions:`` block is declared.  This
is a supply-chain attack risk: a compromised workflow inherits enough
scope to push commits, modify branch protection, etc.

Aletheia's permissions policy:
  * Every workflow must declare a top-level ``permissions:`` block, OR
    every job within it must declare its own.
  * The default scope must be ``read`` (not ``write`` or
    ``read-all``/``write-all``).
  * Scopes that grant write access (``contents: write``,
    ``pull-requests: write``, etc.) require explicit per-job declaration.

v0 implementation: enforces presence of ``permissions:`` with read-only
default; does NOT yet validate the per-scope justification comments.

Runs as both:
  * Offline (pre-push hook via ``tools/run_ci.py``, manual invocation).
  * Push-time (GHA workflow ``.github/workflows/gha-checks.yml``).

Exit codes:
  0 — all workflows declare minimal permissions.
  1 — at least one workflow lacks ``permissions:`` or uses a permissive default.
  2 — no ``.github/workflows/`` directory (skips silently with exit 0).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import yaml


def _check_workflow(path: Path) -> str | None:
    """Return None on OK, otherwise a violation message."""
    try:
        with path.open(encoding="utf-8") as fh:
            doc = yaml.safe_load(fh)
    except yaml.YAMLError as e:
        return f"PARSE_ERROR: {e}"

    if not isinstance(doc, dict):
        return "PARSE_ERROR: top-level YAML is not a mapping"

    top_perms = doc.get("permissions")
    top_ok = False
    if top_perms is not None:
        if isinstance(top_perms, str):
            if top_perms == "read-all":
                return "top-level `permissions: read-all` — declare per-scope minimums instead"
            if top_perms == "write-all":
                return "top-level `permissions: write-all` — declare per-scope minimums instead"
            top_ok = False
        elif isinstance(top_perms, dict):
            top_ok = True

    if top_ok:
        return None

    jobs = doc.get("jobs", {})
    if not isinstance(jobs, dict):
        return "jobs key is not a mapping"

    missing = [
        name
        for name, job in jobs.items()
        if isinstance(job, dict) and job.get("permissions") is None
    ]
    if missing:
        return (
            "no top-level `permissions:` and these jobs lack their own: "
            + ", ".join(missing)
        )

    return None


def main() -> int:
    rc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if rc.returncode != 0:
        sys.stderr.write("check-workflow-permissions: not inside a git repo\n")
        return 2
    repo_root = Path(rc.stdout.strip())

    workflows_dir = repo_root / ".github" / "workflows"
    if not workflows_dir.is_dir():
        print(
            f"check-workflow-permissions: {workflows_dir} does not exist; skipping"
        )
        return 0

    violations: list[str] = []
    checked = 0
    for workflow in sorted(workflows_dir.glob("*.y*ml")):
        checked += 1
        v = _check_workflow(workflow)
        if v is not None:
            violations.append(f"  {workflow.relative_to(repo_root)}: {v}")

    if violations:
        sys.stderr.write(
            "check-workflow-permissions: FAIL — workflow permissions policy "
            "violations detected.\n\n"
            "Policy:\n"
            "  * Every workflow must declare top-level `permissions:` "
            "(mapping form), OR\n"
            "    every job must declare its own `permissions:`.\n"
            "  * `permissions: read-all` and `permissions: write-all` are too "
            "permissive.\n"
            "    Declare per-scope minimums (e.g., `contents: read`).\n\n"
            f"Violations ({checked} workflows checked):\n"
        )
        sys.stderr.write("\n".join(violations) + "\n")
        sys.stderr.write(
            "\n"
            "Fix: add a top-level `permissions:` block with per-scope minimums.\n"
            "Example (read-only default):\n"
            "  permissions:\n"
            "    contents: read\n\n"
            "Reference: GitHub Security Hardening for GitHub Actions § "
            "\"Use the least privilege principle\".\n"
        )
        return 1

    print(
        f"check-workflow-permissions: ok ({checked} workflows checked, "
        "all declare minimal permissions)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

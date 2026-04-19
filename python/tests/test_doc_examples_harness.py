"""Cat 32 gate: every ``python`` fence in the published docs must run.

Per AGENTS.md § Python Cat 32 and the doc-example harness in the repo-root
``conftest.py``, every ``python`` fenced code block across README plus the
user-facing ``docs/**`` files is harvested by ``pytest --markdown-docs``
and executed end-to-end against the real FFI. Pseudo-signatures and
design-sketch fences (class-body shape, JSON return-value examples, etc.)
must use the ``text`` fence language tag so they are invisible to the
harness.

This test is a structural invariant guard: it rejects ``python notest``
tags anywhere in the documented surface, which would silently skip a
doc example from the harness while still *looking* like a Python code
block to a reader. If a fence is genuinely non-runnable, the contributor
must change the language tag from ``python`` to ``text`` (or add a
``continuation`` / ``fixture:<name>`` tag so it chains into a preceding
runnable fence). The gate fails loudly on the first ``notest`` it finds.

The companion invariant — that every runnable ``python`` fence actually
passes — is enforced by ``pytest --markdown-docs`` itself; running that
command is part of the AGENTS.md Python verification block.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]

# Canonical list of user-facing docs whose ``python`` fences run under
# the markdown-docs harness. Keep this in sync with the list in AGENTS.md
# § Python Cat 32 Verification. Adding a new user-facing doc means adding
# it here AND to the AGENTS.md verification command line.
DOC_FILES: tuple[str, ...] = (
    "README.md",
    "docs/PITCH.md",
    "docs/guides/QUICKSTART.md",
    "docs/guides/COOKBOOK.md",
    "docs/reference/CLI.md",
    "docs/architecture/DESIGN.md",
    "docs/architecture/PROTOCOL.md",
    "docs/reference/PYTHON_API.md",
    "docs/reference/INTERFACES.md",
    "python/README.md",
    "examples/README.md",
)

# Matches an opening fence whose info string starts with ``python``.
# Captures (indent, options_after_python) so we can inspect the option
# line — e.g. ``python notest`` → options == " notest".
_PYTHON_FENCE_RE = re.compile(r"^(\s*)```python\b(.*)$")


def _iter_python_fences(text: str):
    """Yield ``(lineno, options)`` for every ``python`` opening fence.

    ``options`` is the trailing portion of the info string after
    ``python`` with leading/trailing whitespace stripped.
    """
    for lineno, line in enumerate(text.splitlines(), start=1):
        m = _PYTHON_FENCE_RE.match(line)
        if m:
            yield lineno, m.group(2).strip()


@pytest.mark.parametrize("doc_path", DOC_FILES)
def test_no_notest_python_fences(doc_path: str) -> None:
    """``python notest`` is banned — use ``text`` for non-runnable fences.

    The harness sees every ``python`` fence; adding ``notest`` would
    silently opt out without changing what a human reader perceives.
    Pseudocode and class-body-shape fences must use ``text`` instead so
    the intent (not runnable) is unambiguous in both harness and prose.
    """
    file = REPO_ROOT / doc_path
    assert file.is_file(), f"doc file missing: {doc_path}"
    offenders: list[tuple[int, str]] = []
    for lineno, options in _iter_python_fences(file.read_text(encoding="utf-8")):
        if re.search(r"\bnotest\b", options):
            offenders.append((lineno, options))
    assert not offenders, (
        f"{doc_path} has ``python notest`` fences — switch the language tag to "
        f"``text`` (or drop ``notest`` so the harness runs the block): "
        f"{offenders!r}"
    )


def test_every_doc_file_has_at_least_one_python_fence() -> None:
    """Sanity: at least one of the tracked docs must ship a ``python`` fence.

    This guards against a mass rename (e.g. someone converting every
    ``python`` to ``text`` during a refactor) that would silently remove
    the doc-example surface. We don't require every individual file to
    carry a fence — some docs are prose-heavy — but the collective set
    must have live examples.
    """
    total = 0
    for doc_path in DOC_FILES:
        text = (REPO_ROOT / doc_path).read_text(encoding="utf-8")
        total += sum(1 for _ in _iter_python_fences(text))
    assert total >= 10, (
        f"expected the doc-example harness to cover ≥10 ``python`` fences "
        f"across the tracked docs, saw {total}"
    )

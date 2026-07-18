# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the citation gate (``tools/check_no_memory_citations.py``).

The citation-shaped strings in this file are deliberate FIXTURES for the
detector. The gate exempts this file by name (``_EXEMPT_FILES``), so they are
never flagged in the live tree — the same arrangement ``test_check_docs.py`` and
``test_check_no_review_marks.py`` use.

Following the gate-audit discipline (a gate that cannot fail has a bug): every
flag shape has a failure-path test that injects a real citation and asserts a
non-empty result, paired with a false-positive test that asserts an innocent
look-alike does NOT fire.
"""

from __future__ import annotations

import pytest

from tools.check_no_memory_citations import exit_code, in_scope, is_exempt, scan_text

_SRC = "src/Aletheia/Foo.agda"  # a representative in-scope file


@pytest.mark.parametrize(
    "citation",
    [
        "[[feedback_no_memory_citations_in_source]]",  # memory wikilink
        "[[project_r25_binding_review]]",
        "[[learnings_aletheia]]",
        "[[reference_python314_except_syntax]]",
        "memory/project_r25_binding_review.md",  # agent-store path
        "memory/feedback_doc_quality_bar.md",
        "feedback_gate_pass_is_absence_of_output.md",  # memory-note filename
        "project_e2_reexamination.md",
    ],
)
def test_citations_are_flagged(citation: str) -> None:
    """Every structured store-pointer shape is detected in a comment."""
    assert scan_text(_SRC, f"-- rationale: see {citation} for the rule")


@pytest.mark.parametrize(
    "keep",
    [
        "ISO 11898-1:2015 §10.4.2",  # external standard clause — MUST survive
        "[[maybe_unused]]",  # C++ attribute — not a memory prefix
        "[[nodiscard]]",
        "[[fallthrough]]",
        "[[gnu::always_inline]]",
        "project_root",  # bare identifier, no .md suffix
        "feedback loop",  # ordinary English, no slug/.md
        "extractSignalCoreFast",  # code cross-ref (greppable, rots loudly)
        "#include <memory>",  # C++ stdlib header, not memory/<name>.md
        "the memory budget",  # the word "memory" alone
        "commit 627ad25",  # a git SHA — ambiguous, intentionally not gated
    ],
)
def test_keeps_are_not_flagged(keep: str) -> None:
    """Legitimate references that merely resemble a citation are not flagged."""
    assert not scan_text(_SRC, f"-- see {keep} for context")


def test_memory_path_reports_once() -> None:
    """A ``memory/`` path reports once — the ``memory/`` lookbehind blocks a double report."""
    findings = scan_text(_SRC, "-- see memory/project_x.md here")
    assert len(findings) == 1
    assert "agent-store path" in findings[0]


@pytest.mark.parametrize(
    "citation",
    [
        "docs/project_x.md",  # a NON-memory path — the filename shape must still fire
        "~/.claude/projects/x/feedback_y.md",  # full store path, no bare ``memory/`` token
    ],
)
def test_non_memory_path_slug_is_flagged(citation: str) -> None:
    """A slug filename after any path other than ``memory/`` is still flagged.

    The ``memory/`` lookbehind suppresses ONLY the double-report of a ``memory/`` path.
    """
    assert scan_text(_SRC, f"-- see {citation}")


def test_subword_slug_is_not_flagged() -> None:
    """The word-char lookbehind keeps a slug inside a larger identifier from firing."""
    assert not scan_text(_SRC, "-- the subproject_x.md helper")


def test_exit_code_contract() -> None:
    """The 0/1/2 contract: exit 2 (could-not-check) dominates exit 1 (violation)."""
    assert exit_code([], could_not_check=False) == 0  # clean
    assert exit_code(["x"], could_not_check=False) == 1  # citations found, scan complete
    assert exit_code([], could_not_check=True) == 2  # scan incomplete
    assert exit_code(["x"], could_not_check=True) == 2  # both — could-not-check dominates


def test_citation_in_non_excluded_file_still_trips() -> None:
    """A citation in a non-exempt file still trips — self-exclusion is not a blind spot."""
    assert scan_text("go/aletheia/client.go", "// per [[feedback_pr_open_protocol]]")
    assert scan_text("cpp/src/backend.cpp", "// see project_r26_product_gaps.md")


def test_user_facing_docs_are_gated() -> None:
    """The user-facing docs (product Markdown + the logs) are scanned, not exempt.

    A store pointer is as dead for a CHANGELOG / tutorial reader as for anyone —
    being historical does not license an unresolvable pointer.
    """
    assert scan_text("CHANGELOG.md", "- fixed per `feedback_gate_claim_integrity.md`")
    assert scan_text("PROJECT_STATUS.md", "see [[project_e2_reexamination]]")
    assert scan_text("docs/guides/TUTORIAL.md", "- `feedback_doc_quality_bar.md` for the bar")
    assert scan_text("docs/operations/RUNBOOK.md", "(see `feedback_parsedbc_quadratic_scaling.md`)")


@pytest.mark.parametrize(
    "rel",
    [
        # detectors + their fixtures
        "tools/check_docs.py",
        "tools/check_no_review_marks.py",
        "tools/check_no_memory_citations.py",
        "python/tests/test_check_docs.py",
        "python/tests/test_check_no_review_marks.py",
        "python/tests/test_check_no_memory_citations.py",
        # AI-process-infra docs whose purpose includes citing the store
        "CLAUDE.md",
        "AGENTS.md",
        "AGENTS/python.md",
        "docs/development/DEFERRED_ITEMS.md",
        # review work record
        ".archive/reviews/r20/round.yaml",
    ],
)
def test_exempt_files_are_exempt(rel: str) -> None:
    """Detectors/fixtures, AI-infra docs, the E2 backlog, and the archive are exempt."""
    assert is_exempt(rel)


@pytest.mark.parametrize(
    "rel",
    [
        # source of every binding language
        "src/Aletheia/Error.agda",
        "python/aletheia/backend.py",
        "go/aletheia/client.go",
        "rust/src/lib.rs",
        "cpp/src/backend.cpp",
        "haskell-shim/src/AletheiaFFI.hs",
        "tools/run_ci.py",
        # user-facing docs + logs (NOT exempt — a dead pointer is dead for readers)
        "CHANGELOG.md",
        "PROJECT_STATUS.md",
        "README.md",
        "docs/guides/TUTORIAL.md",
        "docs/operations/RUNBOOK.md",
        "rust/README.md",
        # data / config
        "docs/FEATURE_MATRIX.yaml",
        "tools/ci-output/.gitignore",
    ],
)
def test_gated_files_are_in_scope(rel: str) -> None:
    """Source, user-facing docs, and data files are all scanned."""
    assert in_scope(rel)


@pytest.mark.parametrize(
    "rel",
    [
        "assets/logo.png",  # binary
        "build/x.agdai",  # binary interface
        "CLAUDE.md",  # exempt AI-infra doc
        "tools/check_no_review_marks.py",  # exempt detector
    ],
)
def test_out_of_scope_files_are_skipped(rel: str) -> None:
    """Binaries and exempt files are not scanned."""
    assert not in_scope(rel)

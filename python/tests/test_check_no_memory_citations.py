# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Unit tests for the citation gate (``tools/check_no_memory_citations.py``).

The citation-shaped strings in this file, and its spellings of the records' place,
are deliberate FIXTURES for the detector. No arm of the gate reads this file, so
they are never flagged in the live tree.

Following the gate-audit discipline (a gate that cannot fail has a bug): every
flag shape has a failure-path test that injects a real citation and asserts a
non-empty result, paired with a false-positive test that asserts an innocent
look-alike does NOT fire.
"""

from __future__ import annotations

import contextlib
import io
from typing import TYPE_CHECKING

import pytest

from tools._common import RelPath, TreeScan, tree_scan_exit_code
from tools.check_no_memory_citations import in_scope, main, scan_text

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

_SRC = "src/Aletheia/Foo.agda"  # a representative in-scope file
# What a finding of the records arm says, after its file and line.
_RECORDS_WHY = "the records' place, which `python/.venv/bin/python -m tools._records` names"


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
    assert tree_scan_exit_code(TreeScan([], [])) == 0  # clean
    assert tree_scan_exit_code(TreeScan(["x"], [])) == 1  # citations found, scan complete
    assert tree_scan_exit_code(TreeScan([], ["f: gone"])) == 2  # scan incomplete
    assert tree_scan_exit_code(TreeScan(["x"], ["f: gone"])) == 2  # both: could-not-check dominates


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
        "tools/check_no_review_marks.py",
        "tools/check_no_memory_citations.py",
        "python/tests/test_docs_arm_labels.py",
        "python/tests/test_check_no_review_marks.py",
        "python/tests/test_check_no_memory_citations.py",
        # AI-process-infra docs whose purpose includes citing the store
        "CLAUDE.md",
        "AGENTS.md",
        "AGENTS/python.md",
        # review work record
        ".archive/reviews/r20/round.yaml",
    ],
)
def test_exempt_files_are_exempt(rel: str) -> None:
    """Detectors/fixtures, AI-infra docs, and the archive may cite the store."""
    assert not scan_text(rel, "see [[learnings_aletheia]] and memory/project_x.md")


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
        "tools/_records.py",
        # read for the records' place though they may cite the store
        "CLAUDE.md",
        "AGENTS/python.md",
        "tools/check_no_review_marks.py",
        # user-facing docs and logs, read for store pointers: a dead pointer is dead for readers
        "CHANGELOG.md",
        "PROJECT_STATUS.md",
        "README.md",
        "docs/guides/TUTORIAL.md",
        "docs/operations/RUNBOOK.md",
        "rust/README.md",
        # data / config
        "docs/FEATURE_MATRIX.yaml",
        "benchmarks/results/.gitignore",
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
        "tools/check_no_memory_citations.py",  # this gate, which no arm reads
        "python/tests/test_check_no_memory_citations.py",  # its fixtures
        ".archive/reviews/r20/notes.md",  # the review work record
    ],
)
def test_out_of_scope_files_are_skipped(rel: str) -> None:
    """Binaries and the files no arm reads are not scanned."""
    assert not in_scope(rel)


def test_a_tracked_file_that_cannot_be_read_is_not_clean(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tracked file the gate cannot read exits 2 and is named, through the shared walk."""

    def tracked(_repo: Path) -> list[RelPath]:
        return [RelPath("note.txt")]

    monkeypatch.setattr("tools._common.git_ls_files", tracked)
    assert main([], repo=tmp_path) == 2
    assert "note.txt" in capsys.readouterr().err


def test_a_line_is_numbered_by_newlines_alone() -> None:
    """A form feed before a citation moves no line number."""
    findings = scan_text("docs/x.md", "a\x0cb\nsee [[learnings_aletheia]] here\n")
    assert [finding.split(" ", 1)[0] for finding in findings] == ["docs/x.md:2:"]


@pytest.mark.parametrize(
    ("line", "spelled"),
    [
        (Prose("logs land in tools/ci-output/ci.log"), Prose("tools/ci-output")),
        (Prose("records in ../aletheia-ci-output/probes"), Prose("aletheia-ci-output")),
        (Prose('log_dir = repo / "tools" / "ci-output"'), Prose("ci-output")),
    ],
)
def test_the_records_place_is_flagged_with_the_module_to_ask(line: Prose, spelled: Prose) -> None:
    """Each spelling of the records' place, a joined path included, names the command to ask."""
    assert scan_text(_SRC, line) == [f"{_SRC}:1: {_RECORDS_WHY} -> {spelled!r}"]


def test_the_records_variable_is_not_the_place() -> None:
    """The variable naming the place is not a spelling of it."""
    assert not scan_text(_SRC, "export ALETHEIA_CI_OUTPUT=/srv/records")


@pytest.mark.parametrize(
    "rel",
    [
        RelPath("tools/_records.py"),
        RelPath("python/tests/test_records.py"),
        RelPath("CHANGELOG.md"),
        RelPath("tools/check_no_memory_citations.py"),
        RelPath("python/tests/test_check_no_memory_citations.py"),
        RelPath(".archive/reviews/r20/round.yaml"),
    ],
)
def test_the_records_arm_leaves_its_owner_the_changelog_and_this_gate_alone(rel: RelPath) -> None:
    """The module owning the place, its test, the changelog, this gate and the archive spell it."""
    assert not scan_text(rel, "under tools/ci-output, now aletheia-ci-output")


@pytest.mark.parametrize(
    "rel",
    [RelPath("tools/_records.py"), RelPath("python/tests/test_records.py")],
)
def test_owning_the_place_leaves_a_file_read_for_store_pointers(rel: RelPath) -> None:
    """The records module and its test are exempt from the records arm alone."""
    assert scan_text(rel, "see [[learnings_aletheia]]")


@pytest.mark.parametrize(
    "rel",
    [
        RelPath("CLAUDE.md"),
        RelPath("AGENTS.md"),
        RelPath("AGENTS/python.md"),
        RelPath("tools/check_no_review_marks.py"),
        RelPath("python/tests/test_docs_arm_labels.py"),
        RelPath("python/tests/test_check_no_review_marks.py"),
    ],
)
def test_a_file_that_may_cite_the_store_is_read_for_the_records_place(rel: RelPath) -> None:
    """Citing the store, by purpose or by construction, does not license spelling the place."""
    assert scan_text(rel, "under tools/ci-output")


def _run_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, tracked: dict[RelPath, Prose]
) -> tuple[ExitStatus, Prose]:
    """Run the gate over a tree tracking ``tracked``, each file holding its text."""
    for rel, text in tracked.items():
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        _ = path.write_text(text, encoding="utf-8")

    def listed(_repo: Path) -> list[RelPath]:
        return list(tracked)

    monkeypatch.setattr("tools._common.git_ls_files", listed)
    printed = io.StringIO()
    with contextlib.redirect_stdout(printed):
        status = ExitStatus(main([], repo=tmp_path))
    return status, Prose(printed.getvalue())


def test_a_tracked_file_spelling_the_records_place_fails_the_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The walk reads a file the citation arms leave alone; its finding names the module."""
    tracked = {RelPath("CLAUDE.md"): Prose("Run records land in tools/ci-output.\n")}
    status, printed = _run_gate(tmp_path, monkeypatch, tracked)
    assert status == 1
    assert printed == (
        "check_no_memory_citations: 1 store pointer(s) or spelling(s) of the records' place:\n"
        f"  CLAUDE.md:1: {_RECORDS_WHY} -> 'tools/ci-output'\n"
    )


def test_a_tree_spelling_the_place_in_its_module_alone_is_clean(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A tree whose one spelling of the place is the records module's passes, and says so."""
    tracked = {
        RelPath("README.md"): Prose("Run records land where the records module says.\n"),
        RelPath("tools/_records.py"): Prose('_BESIDE_THE_CHECKOUT = "aletheia-ci-output"\n'),
    }
    status, printed = _run_gate(tmp_path, monkeypatch, tracked)
    assert status == 0
    assert printed == (
        "check_no_memory_citations: no store pointer and no spelling of the records' place"
        " in the gated tree.\n"
    )

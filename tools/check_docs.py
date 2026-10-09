# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The documentation gate: every claim the tracked documents make about the tree, one arm each.

The gate reads every tracked Markdown file once and runs each arm under
``tools/docs_arms/`` over the same texts; it fails (exit 1) when any arm has a
finding. ``ARMS`` registers every arm module, and each holds one claim:

* ``links``: every relative link and anchor resolves in a fresh checkout;
* ``labels``: no living document carries a transient label or a link into the
  agent memory store;
* ``ffi_symbols``: every ``aletheia_<name>`` symbol the building guide names
  is a foreign export of the shim;
* ``fuzz_targets``: the Go standard names exactly the fuzz targets the
  binding defines, and nothing schedules a fuzz run;
* ``ignored_build_trees``: every build tree the build file and the documents
  name is ignored by the tracked rules, and no top-level venv but the
  sanctioned one is;
* ``index_coverage``: ``docs/INDEX.md`` names every tracked document under
  ``docs/`` and ``AGENTS/`` and the root ``AGENTS.md``;
* ``one_line_paragraphs``: every paragraph, list item and blockquote of the
  building guide is one line;
* ``phase_word``: the phase table names one current phase, and every
  document uses the table's word for it;
* ``readme_extras``: every pip extra a README names is one
  ``python/pyproject.toml`` defines;
* ``readme_tree``: the project tree ``README.md`` prints names exactly the
  top-level directories git tracks;
* ``retired_document``: the dependency ledger has one home, a section of the
  building guide;
* ``section_citations``: a section number cited beside a link names a
  heading of the link's target;
* ``shake_targets``: every ``cabal run shake -- <target>`` a document shows
  is a target the Shakefile defines;
* ``shared_opening``: the sections ``README.md`` and ``docs/PITCH.md`` both
  carry are one text;
* ``stated_measurements``: every measurement the benchmarks guide states is
  what its sources record;
* ``tree_paths``: every repository path the building guide names in
  backticks is tracked.

Run ``python -m tools.check_docs`` from the repo root. The gate is tested by
``python/tests/test_check_docs.py``, each arm by
``python/tests/test_docs_arm_<arm>.py``.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import TYPE_CHECKING

from tools._common import MARKDOWN_SUFFIXES, RelPath, emit, git_ls_files
from tools.docs_arms import (
    ffi_symbols,
    fuzz_targets,
    ignored_build_trees,
    index_coverage,
    labels,
    links,
    one_line_paragraphs,
    phase_word,
    readme_extras,
    readme_tree,
    retired_document,
    section_citations,
    shake_targets,
    shared_opening,
    stated_measurements,
    tree_paths,
)

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Mapping, Sequence

    from tools.docs_arms import Arm

REPO = Path(__file__).resolve().parent.parent

# Every arm under tools/docs_arms/, each run over the same reads.
ARMS: tuple[Arm, ...] = (
    links.findings,
    labels.findings,
    ffi_symbols.findings,
    fuzz_targets.findings,
    ignored_build_trees.findings,
    index_coverage.findings,
    one_line_paragraphs.findings,
    phase_word.findings,
    readme_extras.findings,
    readme_tree.findings,
    retired_document.findings,
    section_citations.findings,
    shake_targets.findings,
    shared_opening.findings,
    stated_measurements.findings,
    tree_paths.findings,
)


def read_documents(root: Path, tracked: Sequence[RelPath]) -> dict[RelPath, Prose]:
    """Return the text of every tracked Markdown file under ``root``, read once for every arm.

    A byte that is not UTF-8 reads as U+FFFD, so one such document is checked
    like any other rather than stopping the gate.
    """
    return {
        rel: Prose((root / rel).read_text(encoding="utf-8", errors="replace"))
        for rel in tracked
        if Path(rel).suffix in MARKDOWN_SUFFIXES
    }


def check_tree(
    root: Path, tracked: Sequence[RelPath], documents: Mapping[RelPath, Prose]
) -> list[Prose]:
    """Return every arm's findings over the tree at ``root``, in the order ``ARMS`` lists them."""
    return [finding for arm in ARMS for finding in arm(root, tracked, documents)]


def main(argv: list[str] | None = None) -> ExitStatus:
    """Run every arm over the repository; 1 (listing the findings) when any has one, else 0."""
    argparse.ArgumentParser(description=__doc__).parse_args(argv)  # no options; --help only
    tracked = git_ls_files(REPO)
    findings = check_tree(REPO, tracked, read_documents(REPO, tracked))
    if findings:
        emit(f"check_docs: {len(findings)} documentation defect(s):")
        for finding in findings:
            emit(f"  {finding}")
        return ExitStatus(1)
    emit("check_docs: every arm holds over the tracked documents.")
    return ExitStatus(0)


if __name__ == "__main__":
    sys.exit(main())

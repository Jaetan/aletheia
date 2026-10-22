# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The CHANGELOG texts the changelog gate's tests share: one entry, unreleased and cut."""

from __future__ import annotations

from tools.commit_subjects import ReleaseVersion

from aletheia.common_types import Prose

# The unreleased entry, and the same entry cut under 1.2.3, each after a title line.
ENTRY_TAIL = "\n## [Unreleased]\n\n### Fixed\n\n- **A bug.** Gone.\n"
CUT_TAIL = "\n## [Unreleased]\n\n## [1.2.3] — 2026-10-12\n\n### Fixed\n\n- **A bug.** Gone.\n"
ENTRY = Prose("# Changelog\n" + ENTRY_TAIL)
CUT = Prose("# Changelog\n" + CUT_TAIL)
VERSION = ReleaseVersion("1.2.3")
SHAPE_FIX = Prose(
    "Cut it as docs/development/RELEASE.md says: the entries move under "
    + "'## [1.2.3] — YYYY-MM-DD', below an empty '## [Unreleased]', and nothing else changes."
)

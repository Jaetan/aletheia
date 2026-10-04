# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_gates_reached`` — every Shake check target is run by something.

Each way a target can be reached (the CI fan-in, a rule's ``need``, the
on-demand list) is shown to clear it, a target none of them reaches is shown to
fail, and so is a list naming a target the Shakefile no longer declares; an
unreadable Shakefile and one declaring no check target exit 2.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools._common import GateName
from tools.check_gates_reached import ShakeSource, run, unreached

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

SHAKEFILE = ShakeSource("""\
    phony "check-ci" $ do
        cmd_ pythonBin "-m" "tools.a"
    phony "check-needed" $ do
        cmd_ pythonBin "-m" "tools.b"
    phony "check-hand" $ do
        cmd_ pythonBin "-m" "tools.c"
    phony "build" $ do
        need ["check-needed", "build/x"]
""")


def test_each_route_reaches_its_target() -> None:
    """Each route reaches its target."""
    assert unreached(
        SHAKEFILE, (GateName("check-ci"),), {GateName("check-hand"): Prose("by hand")}
    ) == (set(), set())


def test_target_nothing_runs_fails() -> None:
    """Target nothing runs fails."""
    orphans, _ = unreached(SHAKEFILE, (GateName("check-ci"),), {})
    assert orphans == {GateName("check-hand")}


def test_listed_target_the_shakefile_lacks_fails() -> None:
    """Listed target the shakefile lacks fails."""
    _, gone = unreached(
        SHAKEFILE,
        (GateName("check-ci"), GateName("check-gone")),
        {GateName("check-hand"): Prose("by hand")},
    )
    assert gone == {GateName("check-gone")}


def test_run_exit_codes(tmp_path: Path) -> None:
    """Run exit codes."""
    shakefile = tmp_path / "Shakefile.hs"
    _ = shakefile.write_text(SHAKEFILE, encoding="utf-8")
    assert run(shakefile, (GateName("check-ci"),), {GateName("check-hand"): Prose("by hand")}) == 0
    assert run(shakefile, (GateName("check-ci"),), {}) == 1
    assert run(tmp_path / "missing.hs", (GateName("check-ci"),), {}) == 2
    _ = shakefile.write_text('    phony "build" $ do\n', encoding="utf-8")
    assert run(shakefile, (), {}) == 2

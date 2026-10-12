# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``check_gates_reached`` — every Shake check target is run by something.

Each way a target can be reached (the CI fan-in, a rule's ``need``, the
on-demand list) is shown to clear it, a target none of them reaches is shown to
fail, and so is a list naming a target no rule declares any more; a tree with
no build program and one declaring no check target exit 2, and a target or a
``need`` in a module under ``shake/`` counts as one in ``Shakefile.hs`` does.
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
    assert run(tmp_path, (GateName("check-ci"),), {GateName("check-hand"): Prose("by hand")}) == 0
    assert run(tmp_path, (GateName("check-ci"),), {}) == 1
    assert run(tmp_path / "missing", (GateName("check-ci"),), {}) == 2
    _ = shakefile.write_text('    phony "build" $ do\n', encoding="utf-8")
    assert run(tmp_path, (), {}) == 2


def test_a_phony_spelled_in_a_comment_is_no_target() -> None:
    """A comment quoting a phony declaration declares nothing a list must reach."""
    commented = ShakeSource(f'{SHAKEFILE}    -- there is no `phony "check-ghost"` target\n')
    assert unreached(
        commented, (GateName("check-ci"),), {GateName("check-hand"): Prose("by hand")}
    ) == (set(), set())


def test_run_reads_the_modules_under_shake(tmp_path: Path) -> None:
    """A target a module declares is checked, and a module's ``need`` reaches one."""
    _ = (tmp_path / "Shakefile.hs").write_text("main = pure ()\n", encoding="utf-8")
    rules = tmp_path / "shake" / "Rules"
    rules.mkdir(parents=True)
    _ = (rules / "Gates.hs").write_text(SHAKEFILE, encoding="utf-8")
    assert run(tmp_path, (GateName("check-ci"),), {GateName("check-hand"): Prose("by hand")}) == 0
    assert run(tmp_path, (GateName("check-ci"),), {}) == 1

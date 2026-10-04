# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``tools.iwyu`` takes one mode and one scope, and refuses any other command line before Agda runs.

The modes (``--check``, ``--apply``, ``--self-test``) exclude one another, and
so do the scopes (``--all``, ``--diff``, files named under ``src/``).  An
argument the tool does not know is refused rather than read as nothing, so a
mistyped ``--check`` cannot run the report that never fails in its place.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

import pytest

from tools import iwyu

from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    from collections.abc import Callable

    from tools._warm import RelPath, WarmAgda


class _GateCall(NamedTuple):
    """What the tool handed the warm gate: the scoped files, and whether it waits for the lock."""

    files: list[RelPath] | None
    wait_lock: bool


def test_a_command_line_without_one_mode_and_one_scope_is_refused(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """No scope, two scopes, files beside a scope, two modes or an unknown flag: exit 2."""

    def unreachable(*, whole_tree: bool, diff: bool, paths: list[RelPath]) -> list[RelPath]:
        raise AssertionError((whole_tree, diff, paths))

    monkeypatch.setattr(iwyu, "select_files", unreachable)
    for line in (
        ["--check"],
        ["--check", "--all", "--diff"],
        ["--check", "--all", "Aletheia/A.agda"],
        ["--check", "--apply", "--all"],
        ["--chek", "--all"],
    ):
        monkeypatch.setattr("sys.argv", ["iwyu", *line])
        with pytest.raises(SystemExit) as stop:
            _ = iwyu.main()
        assert stop.value.code == 2, line


def test_the_pre_commit_line_scopes_its_files_and_waits_for_the_lock(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``--check --wait-lock FILE.agda`` hands that file to the gate, queued behind the lock."""
    seen: list[_GateCall] = []

    def gate(
        files: list[RelPath] | None,
        _action: Callable[[WarmAgda, list[RelPath]], ExitStatus],
        *,
        wait_lock: bool,
    ) -> ExitStatus:
        seen.append(_GateCall(files, wait_lock))
        return ExitStatus(0)

    monkeypatch.setattr(iwyu, "run_warm_gate", gate)
    monkeypatch.setattr("sys.argv", ["iwyu", "--check", "--wait-lock", "Aletheia/A.agda"])
    assert iwyu.main() == 0
    assert seen == [_GateCall(["Aletheia/A.agda"], wait_lock=True)]

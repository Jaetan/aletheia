# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Run a gate's check that must stop it with exit 2, for the suites of the mutation-setup gate."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Callable


def stderr_of_exit_2[Result](
    capsys: pytest.CaptureFixture[Prose], check: Callable[[], Result]
) -> Prose:
    """Run ``check``, which must stop the gate with exit 2, and return what it wrote on stderr."""
    with pytest.raises(SystemExit) as exit_info:
        _ = check()
    assert exit_info.value.code == 2
    return Prose(capsys.readouterr().err)

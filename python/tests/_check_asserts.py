# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared assertions for the YAML check-loader test suites.

Centralises the ``load_checks`` -> single-element -> ``to_dict()`` comparison so
the standard and RTS-free loader suites drive it from one place (and do not trip
pylint's duplicate-code detector on the shared body).
"""

from __future__ import annotations

import textwrap
from typing import TYPE_CHECKING

from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from aletheia import CheckResult


def assert_yaml_single_check(yaml_text: str, expected: CheckResult) -> None:
    """Assert ``yaml_text`` loads to exactly one check equal to ``expected``.

    ``yaml_text`` is ``textwrap.dedent``-ed here, so callers pass an indented
    triple-quoted block verbatim.
    """
    checks = load_checks(textwrap.dedent(yaml_text))
    assert len(checks) == 1
    assert checks[0].to_dict() == expected.to_dict()

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The order a mutant's tests run in under mutmut: their ids', on every machine and run.

mutmut orders a mutant's tests by the timings it measures on each run, so the
first test it reaches, and with it whether a mutant one test alone can crash
on is killed or ends its process, would move between machines and runs;
sorted by id, the verdict is the tree's alone. Outside mutmut, which names its
mutant in MUTANT_UNDER_TEST, the tests keep their files' order.
"""

from __future__ import annotations

import os
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import pytest


def order_for_mutation(items: list[pytest.Item]) -> None:
    """Sort the collected tests by id while mutmut names a mutant, and leave them otherwise."""
    if "MUTANT_UNDER_TEST" in os.environ:
        items.sort(key=lambda item: item.nodeid)

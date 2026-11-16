# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Under mutmut a mutant's tests run in one order on every machine; outside it, in the files' own.

mutmut orders a mutant's tests by the timings it measures on each run, so the
conftest sorts them by id while mutmut names a mutant: whether a mutant one test
alone can crash on is then killed or ends its process is the same on every
machine and run, and the lane's crash ceiling holds it the same way everywhere.
The items are this session's own, laid out against their ids' order.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from _mutation_order import order_for_mutation

if TYPE_CHECKING:
    import pytest


def _against_id_order(request: pytest.FixtureRequest) -> list[pytest.Item]:
    """Return this session's collected tests in the reverse of their ids' order."""
    return sorted(request.session.items, key=lambda item: item.nodeid, reverse=True)


def test_under_mutmut_a_mutants_tests_run_in_the_order_of_their_ids(
    monkeypatch: pytest.MonkeyPatch, request: pytest.FixtureRequest
) -> None:
    """While mutmut names a mutant, the collected tests are sorted by id."""
    monkeypatch.setenv("MUTANT_UNDER_TEST", "aletheia.client._ffi.x__start__mutmut_1")
    items = _against_id_order(request)
    order_for_mutation(items)
    assert [item.nodeid for item in items] == sorted(item.nodeid for item in items)
    assert len({item.nodeid for item in items}) > 1


def test_outside_mutmut_the_tests_keep_the_order_they_were_collected_in(
    monkeypatch: pytest.MonkeyPatch, request: pytest.FixtureRequest
) -> None:
    """Without a mutant named, the collected tests stay in the order they arrived in."""
    monkeypatch.delenv("MUTANT_UNDER_TEST", raising=False)
    items = _against_id_order(request)
    order_for_mutation(items)
    assert items == _against_id_order(request)

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The three LTL patterns over a formula: infinitely often, eventually always, never.

Each is the fluent form a helper names, kept for clarity when a property states
the pattern; :mod:`aletheia.dsl` exports them beside the classes they apply to.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from aletheia.dsl import Predicate, Property


def infinitely_often(formula: Property | Predicate) -> Property:
    """G(F phi) - Property holds infinitely many times (liveness pattern).

    Standard LTL pattern for liveness properties that must occur repeatedly.
    This is NOT a primitive operator, but a composition of Always and Eventually.

    Use this when: You need to verify recurring behaviors (e.g., periodic signals,
    repeated state transitions, cyclic patterns).

    Args:
        formula: Property or Predicate that must hold infinitely often

    Returns:
        Always(Eventually(formula)) property

    Example:
    ```python
    # Speed exceeds 100 infinitely often (repeated acceleration)
    infinitely_often(Signal("Speed").greater_than(100))

    # Equivalent fluent form:
    Signal("Speed").greater_than(100).eventually().always()
    ```

    Note: Helper exists for clarity when expressing this common LTL pattern.

    """
    return formula.eventually().always()


def eventually_always(formula: Property | Predicate) -> Property:
    """F(G phi) - Property eventually holds forever (stability pattern).

    Standard LTL pattern for stability/convergence properties.
    This is NOT a primitive operator, but a composition of Eventually and Always.

    Use this when: You need to verify that a system reaches a stable state
    (e.g., temperature stabilization, mode transitions, initialization complete).

    Args:
        formula: Property or Predicate that must eventually stabilize

    Returns:
        Eventually(Always(formula)) property

    Example:
    ```python
    # Temperature eventually stabilizes below 70 degrees
    eventually_always(Signal("Temperature").less_than(70))

    # Equivalent fluent form:
    Signal("Temperature").less_than(70).always().eventually()
    ```

    Note: Helper exists for clarity when expressing this common LTL pattern.

    """
    return formula.always().eventually()


def never(formula: Property | Predicate) -> Property:
    """G(not phi) - Property never holds (strongest safety property).

    Equivalent to always(not(formula)) but more readable.

    Args:
        formula: Property or Predicate that must never hold

    Returns:
        Always(Not(formula)) property

    Example:
    ```python
    # Critical fault never occurs
    never(Signal("CriticalFault").equals(1))

    # Equivalent to:
    Signal("CriticalFault").equals(1).not_().always()
    ```

    """
    return formula.not_().always()

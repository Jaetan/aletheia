# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared condition vocabulary for YAML and Excel check loaders.

Both loaders accept the same set of condition keywords and dispatch them
through the same Check API builders.  This module defines the keyword sets
and dispatch helpers so that the two loaders stay in sync.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, Literal

from aletheia import checks
from aletheia.client._types import ValidationError

if TYPE_CHECKING:
    from collections.abc import Mapping
    from fractions import Fraction

    from aletheia.checks import CheckResult, ThenCondition, ThenSignal, WhenCondition, WhenSignal

# ============================================================================
# Condition keyword sets
# ============================================================================

SIMPLE_VALUE_CONDITIONS = frozenset(
    {
        "never_exceeds",
        "never_below",
        "never_equals",
    }
)
SIMPLE_RANGE_CONDITIONS = frozenset(
    {
        "stays_between",
    }
)
SIMPLE_SETTLES_CONDITIONS = frozenset(
    {
        "settles_between",
    }
)
SIMPLE_EQUALS_CONDITIONS = frozenset(
    {
        "equals",
    }
)
ALL_SIMPLE_CONDITIONS = (
    SIMPLE_VALUE_CONDITIONS
    | SIMPLE_RANGE_CONDITIONS
    | SIMPLE_SETTLES_CONDITIONS
    | SIMPLE_EQUALS_CONDITIONS
)

WHEN_CONDITIONS = frozenset({"exceeds", "equals", "drops_below"})

ThenSlots = Literal["value", "range"]
#: Which value slots each obligation reads, written once.  A loader asks this
#: rather than deciding again, because a loader that decides does so with a
#: trailing branch: a word this table gained and that branch did not was built
#: as whatever the branch happened to be, which was the range obligation in both
#: loaders.  The set a loader accepts is this table's keys, so an obligation
#: cannot be accepted and unclassified.
THEN_SLOTS: Final[Mapping[str, ThenSlots]] = {
    "equals": "value",
    "exceeds": "value",
    "stays_between": "range",
}
ALL_THEN_CONDITIONS = frozenset(THEN_SLOTS)


# ============================================================================
# Dispatch helpers
# ============================================================================


def dispatch_when(
    builder: WhenSignal,
    condition: str,
    value: int | Fraction,
) -> WhenCondition:
    """Apply a when-condition to a WhenSignal builder."""
    if condition == "exceeds":
        return builder.exceeds(value)
    if condition == "equals":
        return builder.equals(value)
    if condition == "drops_below":
        return builder.drops_below(value)
    msg = f"Unknown when condition: {condition!r}"
    raise ValidationError(msg)


def dispatch_then(
    builder: ThenSignal,
    condition: str,
    value: int | Fraction,
    lo: int | Fraction,
    hi: int | Fraction,
) -> ThenCondition:
    """Build the obligation a word names, from the slots THEN_SLOTS says it reads.

    The slots the obligation does not read are whatever the loader passed and
    are ignored, as in the Go and C++ bindings' dispatchers of the same name.  A
    word outside the table is refused here rather than built as whichever branch
    came last, which is what both loaders used to do.
    """
    if condition == "equals":
        return builder.equals(value)
    if condition == "exceeds":
        return builder.exceeds(value)
    if condition == "stays_between":
        return builder.stays_between(lo, hi)
    msg = f"Unknown then condition: {condition!r}"
    raise ValidationError(msg)


def dispatch_simple(
    signal: str,
    condition: str,
    value: int | Fraction,
) -> CheckResult:
    """Apply a simple single-signal, single-value condition (never_exceeds/below/equals)."""
    if condition == "never_exceeds":
        return checks.signal(signal).never_exceeds(value)
    if condition == "never_below":
        return checks.signal(signal).never_below(value)
    if condition == "never_equals":
        return checks.signal(signal).never_equals(value)
    msg = f"Unknown simple condition: {condition!r}"
    raise ValidationError(msg)

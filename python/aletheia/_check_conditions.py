"""Shared condition vocabulary for YAML and Excel check loaders.

Both loaders accept the same set of condition keywords and dispatch them
through the same Check API builders.  This module defines the keyword sets
and dispatch helpers so that the two loaders stay in sync.
"""

from .checks import Check, CheckResult, WhenCondition, WhenSignal


# ============================================================================
# Condition keyword sets
# ============================================================================

SIMPLE_VALUE_CONDITIONS = frozenset({
    "never_exceeds", "never_below", "never_equals",
})
SIMPLE_RANGE_CONDITIONS = frozenset({
    "stays_between",
})
SIMPLE_SETTLES_CONDITIONS = frozenset({
    "settles_between",
})
SIMPLE_EQUALS_CONDITIONS = frozenset({
    "equals",
})
ALL_SIMPLE_CONDITIONS = (
    SIMPLE_VALUE_CONDITIONS
    | SIMPLE_RANGE_CONDITIONS
    | SIMPLE_SETTLES_CONDITIONS
    | SIMPLE_EQUALS_CONDITIONS
)

WHEN_CONDITIONS = frozenset({"exceeds", "equals", "drops_below"})
_THEN_VALUE_CONDITIONS = frozenset({"equals", "exceeds"})
_THEN_RANGE_CONDITIONS = frozenset({"stays_between"})
ALL_THEN_CONDITIONS = _THEN_VALUE_CONDITIONS | _THEN_RANGE_CONDITIONS


# ============================================================================
# Dispatch helpers
# ============================================================================

def dispatch_when(
    builder: WhenSignal, condition: str, value: float,
) -> WhenCondition:
    """Apply a when-condition to a WhenSignal builder."""
    if condition == "exceeds":
        return builder.exceeds(value)
    if condition == "equals":
        return builder.equals(value)
    if condition == "drops_below":
        return builder.drops_below(value)
    raise ValueError(f"Unknown when condition: {condition!r}")


def dispatch_simple(
    signal: str, condition: str, value: float,
) -> CheckResult:
    """Apply a simple single-signal, single-value condition (never_exceeds/below/equals)."""
    if condition == "never_exceeds":
        return Check.signal(signal).never_exceeds(value)
    if condition == "never_below":
        return Check.signal(signal).never_below(value)
    if condition == "never_equals":
        return Check.signal(signal).never_equals(value)
    raise ValueError(f"Unknown simple condition: {condition!r}")

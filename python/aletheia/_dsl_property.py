# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The DSL's temporal property, and the helpers its operators share with ``Predicate``.

:mod:`aletheia.dsl` exports :class:`Property` beside the signal and predicate
builders that make one; a :class:`~aletheia.dsl.Predicate` is accepted wherever
an operand of a binary operator is, as the atomic formula it is.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from aletheia.client._helpers.property_check import check_formula

if TYPE_CHECKING:
    from aletheia.dsl import Predicate
    from aletheia.types import (
        AlwaysFormula,
        AndFormula,
        EventuallyFormula,
        LTLFormula,
        MetricReleaseFormula,
        MetricUntilFormula,
        NextFormula,
        NotFormula,
        OrFormula,
        ReleaseFormula,
        UntilFormula,
        WeakNextFormula,
    )


def implies_formula(antecedent: LTLFormula, consequent: LTLFormula) -> OrFormula:
    """Desugar implication to ``or(not(antecedent), consequent)``."""
    return {
        "operator": "or",
        "left": {"operator": "not", "formula": antecedent},
        "right": consequent,
    }


class Property:
    """Temporal property (LTL formula).

    Created by Predicate temporal methods. Can be composed with
    other properties using logical operators.

    **Recommended combinators**:
        ``and_``, ``or_``, ``not_``, ``implies``, ``until``, ``release``,
        ``metric_until``, ``metric_release``, ``always``, ``eventually``

    **Discouraged** (see the "Discouraged in CAN analysis" section at the
    bottom of this class): ``next``; use ``metric_until`` /
    ``Predicate.within`` instead on real CAN traces.
    """

    def __init__(self, formula: LTLFormula) -> None:
        """Construct a Property wrapping a finished LTLFormula dict.

        Not part of the public API: derive Properties via temporal
        combinators on a :class:`Predicate` (``always`` / ``eventually``
        / ``never`` / ``within`` / ``for_at_least`` / ``metric_until``
        / ``metric_release``) or via composition operators (``and_``
        / ``or_`` / ``not_`` / ``implies``).  Direct callers must
        supply a fully-formed LTLFormula matching the Agda JSON schema;
        the stored ``_formula`` is assumed to be schema-valid and is
        passed verbatim to the kernel via ``to_formula()``.
        """
        self._formula: LTLFormula = formula

    def to_formula(self) -> LTLFormula:
        """Convert to LTL formula for use in composition.

        Returns:
            LTL formula representation

        """
        return self._formula

    def and_(self, other: Property) -> Property:
        """Logical AND of two properties.

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        speed_ok = Signal("Speed").less_than(220).always()
        voltage_ok = Signal("Voltage").between(11, 15).always()
        speed_ok.and_(voltage_ok)
        ```

        """
        formula: AndFormula = {
            "operator": "and",
            "left": self._formula,
            "right": other.to_formula(),
        }
        return Property(formula)

    def or_(self, other: Property) -> Property:
        """Logical OR of two properties.

        Args:
            other: Another property

        Returns:
            Combined property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        charging = Signal("Charger").equals(1).eventually()
        engine_running = Signal("EngineRPM").greater_than(0).eventually()
        charging.or_(engine_running)
        ```

        """
        formula: OrFormula = {"operator": "or", "left": self._formula, "right": other.to_formula()}
        return Property(formula)

    def implies(self, other: Property | Predicate) -> Property:
        """Logical implication: if self then other.

        Desugars to or(not(self), other) for Agda compatibility.

        Args:
            other: Consequent property or predicate

        Returns:
            Implication property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # Whenever the ignition has been on for a second, the engine runs within 500 ms
        ignition_held = Signal("Ignition").equals(1).for_at_least(1_000_000)
        ignition_held.implies(Signal("EngineRunning").equals(1).within(500_000)).always()
        ```

        """
        return Property(implies_formula(self._formula, other.to_formula()))

    def until(self, other: Property | Predicate) -> Property:
        """Temporal until: self holds until other becomes true.

        Args:
            other: Property or Predicate that must eventually hold

        Returns:
            Until property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # The brake light follows the brake until the ignition turns off, which it does
        follows = Signal("Brake").equals(1).implies(Signal("BrakeLight").equals(1))
        follows.until(Signal("Ignition").equals(0))
        ```

        """
        formula: UntilFormula = {
            "operator": "until",
            "left": self._formula,
            "right": other.to_formula(),
        }
        return Property(formula)

    def release(self, other: Property | Predicate) -> Property:
        """Temporal release: other holds until self releases it (dual of until).

        Args:
            other: Property or Predicate that must hold until released

        Returns:
            Release property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # The brake stays engaged up to the frame the ignition has been on for a
        # second, and forever if that never happens
        ignition_held = Signal("Ignition").equals(1).for_at_least(1_000_000)
        ignition_held.release(Signal("Brake").equals(1))
        ```

        """
        formula: ReleaseFormula = {
            "operator": "release",
            "left": self._formula,
            "right": other.to_formula(),
        }
        return Property(formula)

    def metric_until(self, time_us: int, other: Property | Predicate) -> Property:
        """Temporal until with time bound: self holds until other, within time_us.

        More robust than Next for checking "next frame" conditions.
        Tolerates CAN jitter and ECU timing uncertainty.

        Args:
            time_us: Time bound in whole microseconds, at most 2^64-1
            other: Property or Predicate that must hold within time_us

        Returns:
            Metric Until property

        Raises:
            FFIError: the GHC runtime is not started.
            ValidationError: the kernel refused the time bound (``time_us`` is
                negative), its text the kernel's reason.
            InputBoundExceededError: ``time_us`` is past 2^64-1.

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # The speed holds above 50 for 100 ms at every frame until the brake is
        # pressed, which happens within 1 s
        speed_held = Signal("Speed").greater_than(50).for_at_least(100_000)
        speed_held.metric_until(1_000_000, Signal("Brake").equals(1))
        ```

        """
        formula: MetricUntilFormula = {
            "operator": "metricUntil",
            "timebound": time_us,
            "left": self._formula,
            "right": other.to_formula(),
        }
        check_formula(formula)
        return Property(formula)

    def metric_release(self, time_us: int, other: Property | Predicate) -> Property:
        """Temporal release with time bound: other holds until self releases it, within time_us.

        Args:
            time_us: Time bound in whole microseconds, at most 2^64-1
            other: Property or Predicate that must hold until released

        Returns:
            Metric Release property

        Raises:
            FFIError: the GHC runtime is not started.
            ValidationError: the kernel refused the time bound (``time_us`` is
                negative), its text the kernel's reason.
            InputBoundExceededError: ``time_us`` is past 2^64-1.

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # The brake stays engaged through the first 5 s, released sooner once the
        # ignition has been on for a second
        ignition_held = Signal("Ignition").equals(1).for_at_least(1_000_000)
        ignition_held.metric_release(5_000_000, Signal("Brake").equals(1))
        ```

        """
        formula: MetricReleaseFormula = {
            "operator": "metricRelease",
            "timebound": time_us,
            "left": self._formula,
            "right": other.to_formula(),
        }
        check_formula(formula)
        return Property(formula)

    def always(self) -> Property:
        """Property must always hold (globally) - applies to nested formulas.

        Returns:
            Nested temporal property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # G(F(p)) - infinitely often pattern
        Signal("Speed").greater_than(100).eventually().always()
        ```

        """
        formula: AlwaysFormula = {"operator": "always", "formula": self._formula}
        return Property(formula)

    def eventually(self) -> Property:
        """Property must eventually hold - applies to nested formulas.

        Returns:
            Nested temporal property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # F(G(p)) - eventually always (stability) pattern
        Signal("Temperature").less_than(70).always().eventually()
        ```

        """
        formula: EventuallyFormula = {"operator": "eventually", "formula": self._formula}
        return Property(formula)

    def not_(self) -> Property:
        """Logical negation of property - applies to nested formulas.

        Returns:
            Negated property

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # G(not F(p)) - never occurs pattern
        fault_eventually = Signal("Fault").equals(1).eventually()
        fault_eventually.not_().always()
        ```

        """
        formula: NotFormula = {"operator": "not", "formula": self._formula}
        return Property(formula)

    def to_dict(self) -> LTLFormula:
        """Convert to dictionary for use with AletheiaClient.

        Returns:
            Dictionary representation suitable for JSON serialization

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        property = Signal("VehicleSpeed").less_than(220).always()
        client.set_properties([property.to_dict()])
        ```

        """
        return self._formula

    # ------------------------------------------------------------------
    # Discouraged in CAN analysis, kept for standard-LTLf completeness.
    # See ``Predicate.next`` for the full rationale.
    # ------------------------------------------------------------------

    def next(self) -> Property:
        """Apply Next operator to nested formula.

        **DISCOURAGED on CAN networks.** See :meth:`Predicate.next` for the
        full rationale; prefer ``.within(time_us)`` in practice.

        Use this for nested temporal operators like X(G(phi)), "next, then
        always", when working on deterministic replay traces where the
        next-frame notion is well-defined.

        Returns:
            Nested temporal property (X(nested))

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # X(G(p)): next frame, then always
        Signal("State").equals(1).always().next()
        ```

        """
        formula: NextFormula = {"operator": "next", "formula": self._formula}
        return Property(formula)

    def weak_next(self) -> Property:
        """Apply Weak Next operator to nested formula.

        Like ``next()``, but satisfied at end of stream. See
        :meth:`Predicate.weak_next` for the full rationale.

        Returns:
            Nested temporal property (WX(nested))

        Example:
        ```python
        from aletheia import start_runtime

        start_runtime(1)

        # WX(G(p)): weak next frame, then always
        Signal("State").equals(1).always().weak_next()
        ```

        """
        formula: WeakNextFormula = {"operator": "weakNext", "formula": self._formula}
        return Property(formula)

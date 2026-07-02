# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The outbound float-principle guard (``reject_inexact``) and its boundaries.

``reject_inexact`` is the outbound twin of ``decode_wire_rational``: it rejects a
``float`` or ``bool`` at exactly the fields the Agda kernel parses as ℚ — signal
``factor``/``offset``/``minimum``/``maximum``, env-var ``initial``/``minimum``/
``maximum``, float-kind attribute ``min``/``max``/``value``, and predicate
``value``/``min``/``max``/``delta``/``tolerance``.

A float there is serialised by ``json.dumps`` as e.g. ``0.30000000000000004`` (the
Fraction encoder only intercepts ``Fraction``) and silently absorbed by the kernel
as an exact-but-*wrong* rational.  **Integer** wire fields (``multiplex_values``,
``startBit``, ``id``, …) are deliberately *not* guarded here — a non-integer there
is the kernel's own loud, typed error (e.g. ``parse_non_integer_multiplex_value``),
never silent corruption.  This module pins both halves: rational fields are
rejected client-side; integer fields fall through to the kernel.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, cast

import pytest
from _dbc_helpers import dbc, message, mux_signal, signal

from aletheia import AletheiaClient, ProtocolError, ValidationError

# Private outbound wire-guards — sanctioned reach-throughs (see
# test_private_import_whitelist.py): the public-API boundary tests below cannot
# assert the validators' branch behaviour (every rational field, operator
# descent, list operand, timebound fall-through) precisely.
from aletheia.client._client import reject_formula_inexact
from aletheia.client._helpers.rational import reject_inexact

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition, DBCEnvironmentVar, LTLFormula


class TestRejectInexactContract:
    """Direct contract of the single-value validator (pure — no RTS needed)."""

    def test_accepts_int_and_fraction(self) -> None:
        """An exact ``int`` or ``Fraction`` passes."""
        reject_inexact(5, "factor")
        reject_inexact(Fraction(1, 10), "factor")  # does not raise

    def test_rejects_a_float(self) -> None:
        """A ``float`` is rejected, the error naming the field and the value."""
        with pytest.raises(ValidationError, match=r"factor: a float \(0\.5\).*not exact"):
            reject_inexact(0.5, "factor")

    def test_rejects_a_bool(self) -> None:
        """A ``bool`` is rejected at a rational field (it is not a numeric value)."""
        bool_value: object = True  # bound to object to avoid a boolean-positional literal
        with pytest.raises(ValidationError, match=r"offset: a bool is not an exact"):
            reject_inexact(bool_value, "offset")


def _dbc_with_raw_float(field: str, value: float) -> DBCDefinition:
    """Build a DBC whose signal *field* holds a raw float (the silent-corruption case).

    The ``signal`` helper ``Fraction``-wraps its numeric overrides, so the raw
    float is injected after construction.  A cast is the sanctioned escape for
    invalid adversarial input (the type system rightly forbids it otherwise).
    """
    definition = dbc([message(0x100, "M", [signal("S")])])
    cast("dict[str, object]", definition["messages"][0]["signals"][0])[field] = value
    return definition


class TestDBCFloatHandling:
    """Float handling at the DBC outbound boundary.

    Rational fields reject a float before it reaches the kernel; integer fields
    fall through to the kernel's own typed error (the field-aware contract).
    """

    def test_parse_dbc_rejects_a_float_factor(self) -> None:
        """The headline leak: ``0.1 + 0.2`` in a DBC factor is rejected, not absorbed."""
        bad = _dbc_with_raw_float("factor", 0.1 + 0.2)
        with (
            AletheiaClient() as client,
            pytest.raises(ValidationError, match=r"signal 'S' factor"),
        ):
            client.parse_dbc(bad)

    def test_parse_dbc_rejects_a_float_in_an_env_var(self) -> None:
        """A float in an environment-variable rational field is rejected too."""
        env_var = cast(
            "DBCEnvironmentVar",
            {"name": "Throttle", "varType": 0, "initial": 1.5, "minimum": 0, "maximum": 100},
        )
        bad = dbc([message(0x100, "M", [signal("S")])])
        cast("dict[str, object]", bad)["environmentVars"] = [env_var]
        with (
            AletheiaClient() as client,
            pytest.raises(ValidationError, match=r"environment variable 'Throttle' initial"),
        ):
            client.parse_dbc(bad)

    def test_parse_dbc_rejects_a_float_in_a_float_attribute(self) -> None:
        """A float in a FLOAT-kind attribute bound is rejected (kind-aware)."""
        attr = {
            "kind": "definition",
            "name": "GenSigStartValue",
            "scope": "signal",
            "attrType": {"kind": "float", "min": 0, "max": 1.5},
        }
        bad = dbc([message(0x100, "M", [signal("S")])])
        cast("dict[str, object]", bad)["attributes"] = [attr]
        with (
            AletheiaClient() as client,
            pytest.raises(ValidationError, match=r"attribute 'GenSigStartValue' type max"),
        ):
            client.parse_dbc(bad)

    def test_valid_fraction_dbc_still_parses(self) -> None:
        """Control: an all-``Fraction`` DBC passes the guard and parses successfully."""
        good = dbc([message(0x100, "M", [signal("S", factor=Fraction(1, 10))])])
        with AletheiaClient() as client:
            result = client.parse_dbc(good)
        assert result["status"] == "success"

    def test_float_multiplex_value_is_the_kernel_typed_error(self) -> None:
        """A float in ``multiplex_values`` (an integer field) surfaces the kernel's code.

        This is the whole point of the field-aware design: the float guard must
        *not* intercept an integer field and mask the kernel's precise
        ``parse_non_integer_multiplex_value`` with a generic float message.
        """
        sig = mux_signal("Mode", "Mux", [0], start_bit=0, length=8)
        cast("dict[str, object]", sig)["multiplex_values"] = cast("list[int]", [1.5])
        bad = dbc([message(0x100, "M", [sig])])
        with AletheiaClient() as client, pytest.raises(ProtocolError) as excinfo:
            client.validate_dbc(bad)
        assert excinfo.value.code == "parse_non_integer_multiplex_value"


class TestSetPropertiesBoundary:
    """``set_properties`` rejects a float in a raw ``LTLFormula`` tree."""

    def test_rejects_a_float_predicate_value(self) -> None:
        """A hand-built atomic formula bypasses the DSL's ``to_predicate_fraction`` guard."""
        bad_formula = cast(
            "LTLFormula",
            {
                "operator": "atomic",
                "predicate": {"predicate": "equals", "signal": "X", "value": 0.1 + 0.2},
            },
        )
        with (
            AletheiaClient() as client,
            # The path prefix (properties[index]) is asserted so a dropped/wrong
            # ctx in set_properties' loop is caught, not just "a float".
            pytest.raises(ValidationError, match=r"properties\[0\]\.predicate\.value"),
        ):
            client.set_properties([bad_formula])

    def test_rejects_a_float_nested_under_an_operator(self) -> None:
        """The walker descends operator formulas to reach a deeply-nested predicate."""
        nested = cast(
            "LTLFormula",
            {
                "operator": "always",
                "formula": {
                    "operator": "atomic",
                    "predicate": {"predicate": "lessThan", "signal": "Speed", "value": 2.5},
                },
            },
        )
        with (
            AletheiaClient() as client,
            pytest.raises(ValidationError, match=r"a float \(2\.5\)"),
        ):
            client.set_properties([nested])


class TestRejectFormulaInexact:
    """Direct branch coverage of the formula-tree walker (pure — no RTS needed)."""

    @pytest.mark.parametrize(
        "predicate",
        [
            {"predicate": "equals", "signal": "X", "value": 0.5},
            {"predicate": "between", "signal": "X", "min": 0.5, "max": 1},
            {"predicate": "between", "signal": "X", "min": 0, "max": 0.5},
            {"predicate": "changedBy", "signal": "X", "delta": 0.5},
            {"predicate": "stableWithin", "signal": "X", "tolerance": 0.5},
        ],
    )
    def test_rejects_a_float_at_each_predicate_field(self, predicate: dict[str, object]) -> None:
        """Every ℚ threshold field (value/min/max/delta/tolerance) is checked."""
        formula = {"operator": "atomic", "predicate": predicate}
        with pytest.raises(ValidationError, match=r"a float"):
            reject_formula_inexact(formula, "p")

    def test_rejects_a_bool_threshold(self) -> None:
        """A bool threshold is rejected (reject_inexact rejects both float and bool)."""
        formula = {
            "operator": "atomic",
            "predicate": {"predicate": "equals", "signal": "X", "value": True},
        }
        with pytest.raises(ValidationError, match=r"a bool"):
            reject_formula_inexact(formula, "p")

    @pytest.mark.parametrize("key", ["formula", "left", "right"])
    def test_descends_operator_operands(self, key: str) -> None:
        """The walker recurses into every operator operand to reach a nested predicate."""
        atom = {
            "operator": "atomic",
            "predicate": {"predicate": "equals", "signal": "X", "value": 0.5},
        }
        formula = {"operator": "op", key: atom}
        with pytest.raises(ValidationError, match=r"a float"):
            reject_formula_inexact(formula, "p")

    def test_descends_a_list_valued_operand(self) -> None:
        """A list-valued operand is walked element-by-element (the list branch).

        The full path (``operands[0]``…) is asserted so the list branch's index
        context is exercised, not just that a float is rejected somewhere.
        """
        atom = {
            "operator": "atomic",
            "predicate": {"predicate": "equals", "signal": "X", "value": 0.5},
        }
        formula = {"operator": "and", "operands": [atom]}
        with pytest.raises(ValidationError, match=r"p\.operands\[0\]\.predicate\.value"):
            reject_formula_inexact(formula, "p")

    def test_error_names_the_full_json_path(self) -> None:
        """The error pinpoints the offending field's JSON-path through the whole tree."""
        formula = {
            "operator": "always",
            "formula": {
                "operator": "atomic",
                "predicate": {"predicate": "equals", "signal": "X", "value": 0.5},
            },
        }
        with pytest.raises(ValidationError, match=r"p\.formula\.predicate\.value"):
            reject_formula_inexact(formula, "p")

    def test_integer_timebound_falls_through(self) -> None:
        """A metric operator's ``timebound`` is not a ℚ field — even a float falls through.

        Like the DBC's integer fields, a non-integer ``timebound`` is the kernel's
        own ℕ validation, so the guard does not raise on it; only the nested
        predicate's rational fields are checked (the field-aware contract).
        """
        formula = {
            "operator": "metricAlways",
            "timebound": 1.5,  # a float here is NOT this guard's concern
            "formula": {
                "operator": "atomic",
                "predicate": {"predicate": "equals", "signal": "X", "value": 1},
            },
        }
        reject_formula_inexact(formula, "p")  # does not raise

    def test_valid_formula_passes(self) -> None:
        """An all-exact formula passes the guard untouched."""
        formula = {
            "operator": "atomic",
            "predicate": {"predicate": "between", "signal": "X", "min": 0, "max": Fraction(3, 2)},
        }
        reject_formula_inexact(formula, "p")  # does not raise

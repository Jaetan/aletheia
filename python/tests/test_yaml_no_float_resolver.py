# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""RTS-free behaviour of the YAML check loader.

An *integer*-valued check loads without a live backend: only a *decimal* value
needs the verified kernel (``from_decimal`` is RTS-gated). These tests drive the
public :func:`~aletheia.yaml_loader.load_checks` — and thereby the no-float YAML
scalar loader it calls — without bringing up the GHC RTS, complementing the
RTS-gated decimal tests in ``test_yaml_loader.py``. Kept in its own module
(without that file's module-wide ``rts_up`` fixture) so the RTS-free path is
exercised even where a backend is unavailable.

An explicitly ``!!float``-tagged scalar is also RTS-free: the loader's
float-tag constructor converts it to the double's exact rational value
(``Fraction(float)``), no ``from_decimal`` involved.
"""

import textwrap
from fractions import Fraction

import pytest
from _check_asserts import assert_yaml_single_check

from aletheia import ValidationError
from aletheia.checks import signal
from aletheia.yaml_loader import load_checks


def test_integer_valued_check_loads_without_a_backend() -> None:
    """An integer-valued check parses from YAML with no live RTS.

    ``never_exceeds(220)`` is an exact ``int`` (no ``from_decimal``), so the whole
    load is RTS-free; it still flows through the no-float YAML loader.
    """
    assert_yaml_single_check(
        """\
        checks:
          - signal: Speed
            condition: never_exceeds
            value: 220
    """,
        signal("Speed").never_exceeds(220),
    )


def test_negative_integer_value_loads_without_a_backend() -> None:
    """A negative integer threshold also loads RTS-free (no float coercion)."""
    assert_yaml_single_check(
        """\
        checks:
          - signal: Temp
            condition: never_below
            value: -40
    """,
        signal("Temp").never_below(-40),
    )


def test_tagged_float_check_loads_exactly() -> None:
    """An explicitly ``!!float``-tagged scalar loads at the double's exact value.

    Cross-binding convergence: the Go/C++/Rust loaders read the tagged scalar
    from its literal text and load it exactly (verified against Go's yaml.v3
    ``UnmarshalYAML`` on this very snippet); the literals are the shared
    fixture's ``stays_between`` operands (``go/aletheia/testdata/doc_examples/
    checks.yaml``).  ``11.5`` and ``14.5`` are losslessly-representable
    doubles, so ``Fraction(float)`` yields the same exact rationals the other
    bindings' ``from_decimal`` path produces — all four bindings agree.
    """
    assert_yaml_single_check(
        """\
        checks:
          - signal: Voltage
            condition: stays_between
            min: !!float 11.5
            max: !!float 14.5
    """,
        signal("Voltage").stays_between(Fraction("11.5"), Fraction("14.5")),
    )


@pytest.mark.parametrize("scalar", [".nan", ".inf", "-.inf"])
def test_tagged_non_finite_float_is_refused(scalar: str) -> None:
    """NaN / ±inf under a ``!!float`` tag are refused truthfully.

    No exact rational exists for a non-finite double, and the refusal wording
    is the YAML loader's own — not the Excel loader's "number cell" message.
    Exact-equality on the message kills the string-literal mutants
    (``yaml_loader.py`` is on the mutation surface).
    """
    yaml_text = textwrap.dedent(f"""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: !!float {scalar}
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert str(excinfo.value) == (
        f"YAML !!float scalar {scalar!r} is not finite; only finite "
        "tagged floats have an exact rational value"
    )


def test_tagged_float_invalid_literal_is_refused() -> None:
    """A ``!!float`` tag over a non-float literal is a typed ValidationError."""
    yaml_text = textwrap.dedent("""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: !!float not-a-number
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert str(excinfo.value) == "YAML !!float scalar 'not-a-number' is not a valid float literal"


def test_tagged_float_on_non_scalar_is_refused() -> None:
    """A ``!!float`` tag on a mapping (not a scalar) is a typed ValidationError."""
    yaml_text = textwrap.dedent("""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: !!float {a: 1}
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert str(excinfo.value) == "YAML !!float tag must be applied to a scalar value"

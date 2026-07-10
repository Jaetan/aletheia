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
"""

from _check_asserts import assert_yaml_single_check

from aletheia.checks import signal


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

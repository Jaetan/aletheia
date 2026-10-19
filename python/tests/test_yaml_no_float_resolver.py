# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The YAML check loader hands the kernel every number as the document spells it.

The loader drops PyYAML's implicit int, float, bool and timestamp resolvers
and constructs a scalar tagged ``!!int`` or ``!!float`` as its text, so an
integer, a tagged float and a tagged integer each load to the rational their
text spells, and a tagged scalar the kernel's grammar refuses is the kernel's
refusal, located at the check and the key.  ``docs/LOADER_SCENARIOS.yaml`` holds the spellings the
four bindings share; these hold the construction this loader adds.  Reading a
number runs the kernel's decimal parser, so the module brings the GHC RTS up.
"""

import textwrap
from fractions import Fraction
from typing import Literal, NewType

import pytest
from _check_asserts import assert_yaml_single_check

from aletheia import ValidationError
from aletheia.checks import signal
from aletheia.codes import ErrorCode
from aletheia.yaml_loader import load_checks

pytestmark = pytest.mark.usefixtures("rts_up")

# A value as the document writes it under a check's key, tag included.
YamlValue = NewType("YamlValue", str)


def test_integer_value_is_read_from_its_text() -> None:
    """A plain integer reaches the kernel as its text and reads exactly."""
    assert_yaml_single_check(
        """\
        checks:
          - signal: Speed
            condition: never_exceeds
            value: 220
    """,
        signal("Speed").never_exceeds(220),
    )


def test_negative_integer_value_is_read_from_its_text() -> None:
    """A negative integer threshold reads exactly, its sign the kernel's to read."""
    assert_yaml_single_check(
        """\
        checks:
          - signal: Temp
            condition: never_below
            value: -40
    """,
        signal("Temp").never_below(-40),
    )


def test_tagged_float_is_read_from_its_text() -> None:
    """A ``!!float`` scalar reaches the kernel as its text, under ``min`` and ``max`` alike."""
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


def test_tagged_int_is_read_from_its_text() -> None:
    """A ``!!int`` scalar reaches the kernel as its text: ``017`` is 17, not PyYAML's octal 15."""
    assert_yaml_single_check(
        """\
        checks:
          - signal: Speed
            condition: never_exceeds
            value: !!int 017
    """,
        signal("Speed").never_exceeds(17),
    )


@pytest.mark.parametrize("scalar", [".nan", ".inf", "-.inf", "not-a-number"])
def test_tagged_float_the_kernel_refuses_is_its_refusal(scalar: str) -> None:
    """A ``!!float`` text outside the kernel's grammar is the kernel's refusal, located.

    The error keeps the kernel's type and code and gains the check the loader
    read the number in and the key it sat under.
    """
    yaml_text = textwrap.dedent(f"""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: !!float {scalar}
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    exc = excinfo.value
    assert exc.code == ErrorCode.TEXT_PARSE_FAILURE
    assert exc.location == "Check '<unnamed>'"
    assert exc.key == "value"
    assert str(exc).startswith("Check '<unnamed>': invalid 'value': parse failed at line 1, ")


def test_quoted_number_keeps_its_spaces() -> None:
    """A quoted scalar's spaces reach the kernel, which refuses the leading one."""
    yaml_text = textwrap.dedent("""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: " 1.5"
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert excinfo.value.code == ErrorCode.TEXT_PARSE_FAILURE
    assert str(excinfo.value) == (
        "Check '<unnamed>': invalid 'value': parse failed at line 1, column 1"
    )


@pytest.mark.parametrize(
    ("node", "found"),
    [
        ("!!float {a: 1}", "mapping"),
        ("!!float {=: 1.5}", "mapping"),
        ("!!int [1]", "sequence"),
    ],
)
def test_number_tag_on_a_collection_is_invalid_yaml(
    node: YamlValue, found: Literal["mapping", "sequence"]
) -> None:
    """A number tag on a mapping or a sequence has no text to read, and is invalid YAML.

    A mapping holding a ``=`` key is refused too, where PyYAML's own scalar
    construction would read that key's value.
    """
    yaml_text = textwrap.dedent(f"""\
        checks:
          - signal: Voltage
            condition: never_exceeds
            value: {node}
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert excinfo.value.code is None
    assert str(excinfo.value).startswith(
        f"invalid YAML: expected a scalar node, but found {found}\n"
    )


def test_unreadable_yaml_is_invalid_yaml() -> None:
    """A document PyYAML cannot parse is a ``ValidationError`` naming PyYAML's reason."""
    with pytest.raises(ValidationError) as excinfo:
        load_checks("checks: [")
    assert excinfo.value.code is None
    assert str(excinfo.value).startswith("invalid YAML: while parsing a flow node\n")


@pytest.mark.parametrize("empty", ["~", "null", ""])
def test_null_value_reads_as_missing(empty: YamlValue) -> None:
    """The null resolver stays, so an empty value, ``~`` or ``null`` is a missing number."""
    yaml_text = textwrap.dedent(f"""\
        checks:
          - name: C
            signal: Voltage
            condition: never_exceeds
            value: {empty}
    """)
    with pytest.raises(ValidationError) as excinfo:
        load_checks(yaml_text)
    assert excinfo.value.code is None
    assert str(excinfo.value) == "Check 'C': missing or invalid 'value' (expected number)"

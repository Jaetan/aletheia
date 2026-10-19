# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The Python YAML and Excel loaders held to the contract ``docs/LOADER_SCENARIOS.yaml``.

Each scenario spells one number in a YAML check document or in an Excel row and
states what the loader answers: the exact rational it reads (the milliseconds,
for a ``within_ms``), or the kernel's refusal, which keeps the kernel's kind,
code and fields and gains the location the loader read the number at and the
key it sat under, its string form being
``<location>: invalid '<key>': <message>``.  The Go, C++ and Rust loaders are
held to the same file, so a row failing here alone is a defect of this binding.

Reading a number runs the kernel's decimal parser, so the module brings the GHC
RTS up via the shared ``rts_up`` fixture.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
from typing import TYPE_CHECKING, Final, Literal, NewType, NotRequired, TypedDict, TypeIs, cast

import pytest
import yaml
from _excel_helpers import make_checks_workbook, make_dbc_workbook

from aletheia import AletheiaError, InputBoundExceededError, ValidationError
from aletheia.checks import signal
from aletheia.excel_loader import load_checks_from_excel, load_dbc_from_excel
from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.codes import ErrorCode
    from aletheia.common_types import DocumentKey, Location, PositiveInt, Prose
    from aletheia.excel_loader import CellValue
    from aletheia.limits import BoundField, BoundKind, Limit
    from aletheia.types import LTLFormula

pytestmark = pytest.mark.usefixtures("rts_up")

_CONTRACT_PATH: Final = Path(__file__).resolve().parents[2] / "docs" / "LOADER_SCENARIOS.yaml"

# A scenario's identifier, which is its test id.
ScenarioName = NewType("ScenarioName", str)

# A number as the document spells it: a YAML scalar with its quotes and tag, or
# an Excel cell's text.
NumberText = NewType("NumberText", str)

# The numerator or the denominator of the rational a loader reads.
Component = NewType("Component", int)

# The time bound a loader reads from ``within_ms``, in milliseconds.
Milliseconds = NewType("Milliseconds", int)

# The kinds of refusal the contract names.
type RefusalKind = Literal["validation", "input_bound_exceeded"]

# The Excel sheets a scenario writes its number into.
type Sheet = Literal["Checks", "DBC"]


class Reading(TypedDict):
    """The rational a loader reads, as ``[numerator, denominator]``."""

    rational: list[Component]


class TimeReading(TypedDict):
    """The time bound a loader reads from ``within_ms``."""

    milliseconds: Milliseconds


class Bound(TypedDict):
    """The bound fields an ``input_bound_exceeded`` refusal carries."""

    kind: BoundKind
    observed: PositiveInt
    limit: Limit
    field: BoundField


class Refusal(TypedDict):
    """A refusal: the kernel's kind, code and fields, the loader's location and key."""

    kind: RefusalKind
    code: ErrorCode
    location: Location
    key: DocumentKey
    printed: Prose
    bound: NotRequired[Bound]


class YamlScenario(TypedDict):
    """A number written as the ``value`` of the contract's one-check document."""

    name: ScenarioName
    value: NumberText
    expect: Reading | Refusal


class WithinScenario(TypedDict):
    """A number written as the ``within_ms`` of the contract's one settles_between check."""

    name: ScenarioName
    value: NumberText
    expect: TimeReading | Refusal


class ExcelScenario(TypedDict):
    """A number written in the contract's data row of the Checks or the DBC sheet."""

    name: ScenarioName
    sheet: Sheet
    value: NumberText
    expect: Reading | Refusal


class LoaderContract(TypedDict):
    """The contract file: its YAML scenarios, its ``within_ms`` ones and its Excel ones."""

    yaml: list[YamlScenario]
    yaml_within_ms: list[WithinScenario]
    excel: list[ExcelScenario]


def _read_contract() -> LoaderContract:
    """Return the contract file as the YAML reader gives it.

    A section without a row, or a row whose ``expect`` gives other than one
    answer (a rational, milliseconds or a refusal), is a mistake in the
    contract, refused here rather than read as a skipped test or as one of its
    answers.
    """
    with _CONTRACT_PATH.open(encoding="utf-8") as fh:
        contract = cast("LoaderContract", yaml.safe_load(fh))
    sections = (
        ("yaml", contract["yaml"]),
        ("yaml_within_ms", contract["yaml_within_ms"]),
        ("excel", contract["excel"]),
    )
    for section, rows in sections:
        assert rows, f"{_CONTRACT_PATH}: no {section} scenarios"
        for row in rows:
            answers = [key for key in ("rational", "milliseconds", "kind") if key in row["expect"]]
            assert len(answers) == 1, (
                f"scenario {row['name']}: the contract's expect gives {answers}"
            )
    return contract


_CONTRACT: Final = _read_contract()

# The check document of a YAML scenario, its number in the ``value`` key.
_CHECK_DOCUMENT: Final = """\
checks:
  - name: "C"
    signal: Speed
    condition: never_exceeds
    value: {value}
"""

# The check document of a ``within_ms`` scenario, its number in the ``within_ms`` key.
_WITHIN_DOCUMENT: Final = """\
checks:
  - name: "C"
    signal: Speed
    condition: settles_between
    min: 0
    max: 100
    within_ms: {value}
"""


def _checks_row(value: NumberText) -> list[CellValue]:
    """Return the Checks sheet's data row, every cell text, ``value`` under Value."""
    return ["C", "Speed", "never_exceeds", value, "", "", "", ""]


def _dbc_row(value: NumberText) -> list[CellValue]:
    """Return the DBC sheet's data row, every cell text but Signed, ``value`` under Factor."""
    message = ["256", "M", "", "8"]
    return [*message, "Sig", "0", "8", "little_endian", False, value, "0", "0", "1", "", "", ""]


def _yaml_formulas(path: Path) -> list[LTLFormula]:
    """Return the formula of each check the YAML loader reads from ``path``."""
    return [check.to_dict() for check in load_checks(path)]


def _excel_formulas(path: Path) -> list[LTLFormula]:
    """Return the formula of each check the Excel loader reads from ``path``."""
    return [check.to_dict() for check in load_checks_from_excel(path)]


def _excel_factors(path: Path) -> list[Fraction]:
    """Return the factor of each signal the Excel loader reads from ``path``."""
    dbc = load_dbc_from_excel(path)
    return [sig["factor"] for message in dbc["messages"] for sig in message["signals"]]


def _rational(expect: Reading) -> Fraction:
    """Return the rational ``expect`` states."""
    numerator, denominator = expect["rational"]
    return Fraction(numerator, denominator)


def _never_exceeds(expect: Reading) -> list[LTLFormula]:
    """Return the formula of the one check a scenario's document holds, at the rational read."""
    return [signal("Speed").never_exceeds(_rational(expect)).to_dict()]


def _factor(expect: Reading) -> list[Fraction]:
    """Return the factors of the one signal a scenario's DBC sheet holds, at the rational read."""
    return [_rational(expect)]


def _settles_within(expect: TimeReading) -> list[LTLFormula]:
    """Return the formula of the one check a ``within_ms`` document holds, at the bound read."""
    return [signal("Speed").settles_between(0, 100).within(expect["milliseconds"]).to_dict()]


def _refused(expect: Reading | TimeReading | Refusal) -> TypeIs[Refusal]:
    """Return whether ``expect`` states a refusal rather than a reading."""
    return "kind" in expect


def _assert_refusal(name: ScenarioName, expect: Refusal, exc: AletheiaError) -> None:
    """Assert that ``exc`` is the refusal ``expect`` states, member by member."""
    where = f"scenario {name}"
    error = ValidationError if expect["kind"] == "validation" else InputBoundExceededError
    raised = type(exc).__name__
    assert isinstance(exc, error), f"{where}: raised {raised}, not {error.__name__}: {exc}"
    assert exc.code == expect["code"], f"{where}: code {exc.code!r}"
    assert exc.location == expect["location"], f"{where}: location {exc.location!r}"
    assert exc.key == expect["key"], f"{where}: key {exc.key!r}"
    printed = str(exc)
    assert printed == expect["printed"], f"{where}: printed {printed!r}"
    if "bound" not in expect:
        assert expect["kind"] == "validation", f"{where}: the contract gives no bound"
        return
    bound = expect["bound"]
    assert isinstance(exc, InputBoundExceededError), f"{where}: raised {type(exc).__name__}"
    assert exc.kind == bound["kind"], f"{where}: bound kind {exc.kind!r}"
    assert exc.observed == bound["observed"], f"{where}: observed {exc.observed}"
    assert exc.limit == bound["limit"], f"{where}: limit {exc.limit}"
    assert exc.field == bound["field"], f"{where}: field {exc.field!r}"


def _hold[T](
    name: ScenarioName,
    expect: Reading | TimeReading | Refusal,
    path: Path,
    load: Callable[[Path], T],
    want: T | None,
) -> None:
    """Assert that ``load`` reads ``path`` as ``want``, or raises the refusal ``expect`` states."""
    where = f"scenario {name}"
    try:
        answer = load(path)
    except AletheiaError as exc:
        if _refused(expect):
            _assert_refusal(name, expect, exc)
        else:
            pytest.fail(f"{where}: refused with {exc!s}, not read as {expect}")
        return
    if _refused(expect):
        pytest.fail(f"{where}: read {answer!r}, not refused with {expect['printed']!r}")
    else:
        assert answer == want, f"{where}: read {answer!r}"


@pytest.mark.parametrize(
    "scenario", _CONTRACT["yaml"], ids=[row["name"] for row in _CONTRACT["yaml"]]
)
def test_yaml_loader_answers_the_contract(scenario: YamlScenario, tmp_path: Path) -> None:
    """The document's ``value`` reads as the scenario's rational, or is refused as it states."""
    path = tmp_path / "checks.yaml"
    path.write_text(_CHECK_DOCUMENT.format(value=scenario["value"]), encoding="utf-8")
    expect = scenario["expect"]
    want = _never_exceeds(expect) if "rational" in expect else None
    _hold(scenario["name"], expect, path, _yaml_formulas, want)


@pytest.mark.parametrize(
    "scenario",
    _CONTRACT["yaml_within_ms"],
    ids=[row["name"] for row in _CONTRACT["yaml_within_ms"]],
)
def test_yaml_within_ms_answers_the_contract(scenario: WithinScenario, tmp_path: Path) -> None:
    """The ``within_ms`` reads as the scenario's milliseconds, or is refused as it states."""
    path = tmp_path / "checks.yaml"
    path.write_text(_WITHIN_DOCUMENT.format(value=scenario["value"]), encoding="utf-8")
    expect = scenario["expect"]
    want = _settles_within(expect) if "milliseconds" in expect else None
    _hold(scenario["name"], expect, path, _yaml_formulas, want)


@pytest.mark.parametrize(
    "scenario", _CONTRACT["excel"], ids=[row["name"] for row in _CONTRACT["excel"]]
)
def test_excel_loader_answers_the_contract(scenario: ExcelScenario, tmp_path: Path) -> None:
    """The row's Value or Factor reads as the scenario's rational, or is refused as it states."""
    expect = scenario["expect"]
    sheet = scenario["sheet"]
    assert sheet in {"Checks", "DBC"}, (
        f"scenario {scenario['name']}: the contract names the sheet {sheet!r}"
    )
    if sheet == "Checks":
        path = make_checks_workbook(tmp_path, [_checks_row(scenario["value"])])
        formulas = _never_exceeds(expect) if "rational" in expect else None
        _hold(scenario["name"], expect, path, _excel_formulas, formulas)
    else:
        path = make_dbc_workbook(tmp_path, [_dbc_row(scenario["value"])])
        factors = _factor(expect) if "rational" in expect else None
        _hold(scenario["name"], expect, path, _excel_factors, factors)

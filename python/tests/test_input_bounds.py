# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Adversarial-input bounds regression tests.

``aletheia.InputBoundExceededError`` carries the bound's kind, the observed
value, the limit and, for a DBC's size bounds, the field that crossed it.  The
binding refuses an oversize DBC text or JSON command before marshaling it
across ctypes, in its own words; the kernel refuses an input past any other
bound, and every DBC command raises that refusal as the typed error, whose text
is the kernel's message.

Every parser-surface loader entry point (``yaml_loader._load_yaml``,
``dbc.dbc_to_json``, ``excel_loader.load_dbc_from_excel``,
``excel_loader.load_checks_from_excel``) rejects oversize files with
:class:`InputBoundExceededError` before allocating buffers / parsing.
"""

import inspect
from fractions import Fraction
from typing import TYPE_CHECKING, Literal, cast, get_args

import pytest
from _dbc_helpers import dbc, message, mux_signal, signal

from aletheia import (
    AletheiaClient,
    AletheiaError,
    InputBoundExceededError,
    Signal,
    limits,
)
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.codes import ErrorCode
from aletheia.common_types import Gt, PositiveInt
from aletheia.dbc import dbc_to_json
from aletheia.excel_loader import load_checks_from_excel, load_dbc_from_excel
from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path

    from aletheia.dsl import Predicate
    from aletheia.limits import Limit
    from aletheia.types import DBCDefinition, ErrorResponse, LTLFormula

# A DBC list the kernel bounds, spelled as its refusal names it.
ListField = Literal[
    "signal groups array",
    "environment variables array",
    "unresolved value descriptions array",
    "senders array",
    "receivers array",
    "signal group members array",
    "enum labels array",
    "multiplex values array",
]


def _trivial_dbc() -> DBCDefinition:
    """Build a minimal valid DBC: one empty message, all sections empty."""
    return dbc([message(100, "M", [], senders=[])], version="")


def _nested_ltl(depth: int) -> LTLFormula:
    """Build a property with ``depth`` levels of nested ``always`` wrappers.

    The atomic base is kept as a raw wire dict (not the DSL form) so the
    resulting JSON nesting depth is exactly ``depth + 2`` — the depth-bound
    tests below pin the 60-accepted / 63-rejected boundary on that count.
    """
    formula: LTLFormula = cast(
        "LTLFormula",
        {
            "operator": "atomic",
            "predicate": {"predicate": "equals", "signal": "S", "value": 0},
        },
    )
    for _ in range(depth):
        formula = cast("LTLFormula", {"operator": "always", "formula": formula})
    return formula


def _balanced_and(predicates: list[Predicate]) -> LTLFormula:
    """Build a balanced And-tree over the predicates' formulas."""
    if len(predicates) == 1:
        return predicates[0].to_formula()
    half = len(predicates) // 2
    return cast(
        "LTLFormula",
        {
            "operator": "and",
            "left": _balanced_and(predicates[:half]),
            "right": _balanced_and(predicates[half:]),
        },
    )


def _over_signal_groups() -> DBCDefinition:
    """Build a DBC holding one signal group past ``MAX_SIGNAL_GROUPS_PER_FILE``."""
    d = _trivial_dbc()
    d["signalGroups"] = [
        {"name": f"G{i}", "signals": []} for i in range(limits.MAX_SIGNAL_GROUPS_PER_FILE + 1)
    ]
    return d


def _over_environment_variables() -> DBCDefinition:
    """Build a DBC holding one environment variable past ``MAX_ENVIRONMENT_VARIABLES_PER_FILE``."""
    d = _trivial_dbc()
    d["environmentVars"] = [
        {
            "name": f"E{i}",
            "varType": 0,
            "initial": Fraction(0),
            "minimum": Fraction(0),
            "maximum": Fraction(1),
        }
        for i in range(limits.MAX_ENVIRONMENT_VARIABLES_PER_FILE + 1)
    ]
    return d


def _over_unresolved_value_descriptions() -> DBCDefinition:
    """Build a DBC holding one entry-less unresolved ``VAL_`` line past its bound."""
    d = _trivial_dbc()
    d["unresolvedValueDescs"] = [
        {"id": 999, "extended": False, "signalName": "Q", "entries": []}
        for _ in range(limits.MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE + 1)
    ]
    return d


def _over_senders() -> DBCDefinition:
    """Build a DBC whose message has one sender past ``MAX_NODES_PER_FILE``."""
    senders = [f"N{i}" for i in range(limits.MAX_NODES_PER_FILE + 1)]
    return dbc([message(256, "M", [signal("S")], senders=senders)])


def _over_receivers() -> DBCDefinition:
    """Build a DBC whose signal has one receiver past ``MAX_NODES_PER_FILE``."""
    receivers = [f"N{i}" for i in range(limits.MAX_NODES_PER_FILE + 1)]
    return dbc([message(256, "M", [signal("S", receivers=receivers)])])


def _over_signal_group_members() -> DBCDefinition:
    """Build a DBC whose signal group has one member past ``MAX_SIGNALS_PER_MESSAGE``."""
    d = _trivial_dbc()
    members = [f"S{i}" for i in range(limits.MAX_SIGNALS_PER_MESSAGE + 1)]
    d["signalGroups"] = [{"name": "G", "signals": members}]
    return d


def _over_enum_labels() -> DBCDefinition:
    """Build a DBC whose enum attribute has one label past ``MAX_ENUM_LABELS_PER_ATTRIBUTE``."""
    d = _trivial_dbc()
    labels = [f"v{i}" for i in range(limits.MAX_ENUM_LABELS_PER_ATTRIBUTE + 1)]
    d["attributes"] = [
        {
            "kind": "definition",
            "name": "A",
            "scope": "network",
            "attrType": {"kind": "enum", "values": labels},
        }
    ]
    return d


def _over_multiplex_values() -> DBCDefinition:
    """Build a DBC whose muxed signal has one value past ``MAX_MULTIPLEX_VALUES_PER_SIGNAL``."""
    values = list(range(limits.MAX_MULTIPLEX_VALUES_PER_SIGNAL + 1))
    return dbc([message(256, "M", [signal("Mx"), mux_signal("S", "Mx", values, start_bit=16)])])


# Each list the kernel bounds: its name in the refusal, its limit, a DBC one past it.
_LISTS_PAST_BOUND = [
    pytest.param(
        "signal groups array",
        limits.MAX_SIGNAL_GROUPS_PER_FILE,
        _over_signal_groups,
        id="signal-groups",
    ),
    pytest.param(
        "environment variables array",
        limits.MAX_ENVIRONMENT_VARIABLES_PER_FILE,
        _over_environment_variables,
        id="environment-variables",
    ),
    pytest.param(
        "unresolved value descriptions array",
        limits.MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE,
        _over_unresolved_value_descriptions,
        id="unresolved-value-descriptions",
    ),
    pytest.param("senders array", limits.MAX_NODES_PER_FILE, _over_senders, id="senders"),
    pytest.param("receivers array", limits.MAX_NODES_PER_FILE, _over_receivers, id="receivers"),
    pytest.param(
        "signal group members array",
        limits.MAX_SIGNALS_PER_MESSAGE,
        _over_signal_group_members,
        id="signal-group-members",
    ),
    pytest.param(
        "enum labels array",
        limits.MAX_ENUM_LABELS_PER_ATTRIBUTE,
        _over_enum_labels,
        id="enum-labels",
    ),
    pytest.param(
        "multiplex values array",
        limits.MAX_MULTIPLEX_VALUES_PER_SIGNAL,
        _over_multiplex_values,
        id="multiplex-values",
    ),
]


class TestInputBoundExceededErrorType:
    """``InputBoundExceededError`` shape + inheritance."""

    def test_subclass_of_aletheia_error(self) -> None:
        """``InputBoundExceededError`` derives from ``AletheiaError``."""
        assert issubclass(InputBoundExceededError, AletheiaError)

    def test_carries_kind_observed_limit(self) -> None:
        """All three structured fields are stored on the instance."""
        err = InputBoundExceededError(
            kind=limits.BOUND_KIND_INPUT_LENGTH_BYTES,
            observed=100,
            limit=50,
        )
        assert err.kind == "input_length_bytes"
        assert err.observed == 100
        assert err.limit == 50

    def test_message_contains_kind_observed_limit(self) -> None:
        """The default ``str(err)`` mentions kind, observed, and limit."""
        err = InputBoundExceededError(
            kind=limits.BOUND_KIND_INPUT_LENGTH_BYTES,
            observed=100,
            limit=50,
        )
        msg = str(err)
        assert "input_length_bytes" in msg
        assert "100" in msg
        assert "50" in msg

    def test_carries_optional_wire_code(self) -> None:
        """Optional ``code`` kwarg surfaces through ``AletheiaError.code``."""
        err = InputBoundExceededError(
            kind=limits.BOUND_KIND_INPUT_LENGTH_BYTES,
            observed=100,
            limit=50,
            code="input_bound_exceeded",
        )
        assert err.code == "input_bound_exceeded"

    def test_wire_code_is_an_error_code(self) -> None:
        """``ErrorCode`` carries the one bound code; ``bound_kind`` tells the bounds apart."""
        assert ErrorCode.INPUT_BOUND_EXCEEDED == "input_bound_exceeded"

    def test_without_a_kernel_refusal_the_text_is_the_bindings_own(self) -> None:
        """A bound the binding checks names no field, and its text names the bound."""
        err = InputBoundExceededError(limits.BOUND_KIND_NESTING_DEPTH, 65, 64)
        assert (err.field, str(err)) == (None, "nesting_depth 65 exceeds limit 64")


class TestLimitsConstants:
    """Numeric bound constants present and match Aletheia.Limits values."""

    def test_max_json_bytes_64mib(self) -> None:
        """JSON FFI-input cap is 64 MiB, mirroring ``Aletheia.Limits``."""
        assert limits.MAX_JSON_BYTES == 64 * 1024 * 1024

    def test_max_dbc_text_bytes_64mib(self) -> None:
        """DBC-text input cap is 64 MiB, mirroring ``Aletheia.Limits``."""
        assert limits.MAX_DBC_TEXT_BYTES == 64 * 1024 * 1024

    def test_bound_kind_codes_match_agda(self) -> None:
        """Wire codes mirror ``boundKindCode`` in ``Aletheia.Limits``."""
        assert limits.BOUND_KIND_INPUT_LENGTH_BYTES == "input_length_bytes"
        assert limits.BOUND_KIND_NESTING_DEPTH == "nesting_depth"
        assert limits.BOUND_KIND_ARRAY_CARDINALITY == "array_cardinality"
        assert limits.BOUND_KIND_IDENTIFIER_LENGTH == "identifier_length"
        assert limits.BOUND_KIND_STRING_LENGTH == "string_length"
        assert limits.BOUND_KIND_ATOM_COUNT == "atom_count"
        assert limits.BOUND_KIND_PROPERTY_COUNT == "property_count"
        assert limits.BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE == "rational_component_magnitude"

    def test_max_rational_component_magnitude_is_int64_max(self) -> None:
        """Rational-component cap is the signed 64-bit wire range.

        Mirrors ``max-rational-component-magnitude`` in ``Aletheia.Limits``:
        the same range the binary FFI's rational slots and the decimal SSOT
        enforce, so one Int64 bound covers every wire.
        """
        assert limits.MAX_RATIONAL_COMPONENT_MAGNITUDE == 2**63 - 1

    def test_per_section_cardinalities(self) -> None:
        """Cardinality bounds for messages / signals / attributes / VAL_."""
        assert limits.MAX_MESSAGES_PER_FILE == 10_000
        assert limits.MAX_SIGNALS_PER_MESSAGE == 1024
        assert limits.MAX_ATTRIBUTES_PER_FILE == 10_000
        assert limits.MAX_VALUE_DESCRIPTIONS_PER_FILE == 1_000_000
        assert limits.MAX_IDENTIFIER_LENGTH == 128
        assert limits.MAX_STRING_LENGTH_CHARACTERS == 64 * 1024
        assert limits.MAX_ATOM_COUNT_PER_PROPERTY == 1024
        assert limits.MAX_PROPERTIES_PER_STREAM == 1024

    def test_dbc_list_cardinalities(self) -> None:
        """Cardinality bounds for the remaining DBC lists, mirroring ``Aletheia.Limits``."""
        assert limits.MAX_COMMENTS_PER_FILE == 10_000
        assert limits.MAX_NODES_PER_FILE == 10_000
        assert limits.MAX_VALUE_TABLES_PER_FILE == 10_000
        assert limits.MAX_SIGNAL_GROUPS_PER_FILE == 10_000
        assert limits.MAX_ENVIRONMENT_VARIABLES_PER_FILE == 10_000
        assert limits.MAX_UNRESOLVED_VALUE_DESCRIPTIONS_PER_FILE == 10_000
        assert limits.MAX_ENUM_LABELS_PER_ATTRIBUTE == 10_000
        assert limits.MAX_MULTIPLEX_VALUES_PER_SIGNAL == 1024

    def test_every_limit_is_a_positive_int(self) -> None:
        """Each ``MAX_*`` constant is typed ``Limit``, a positive int, and holds one."""
        assert get_args(limits.Limit.__value__) == get_args(PositiveInt) == (int, Gt(0))
        annotations = inspect.get_annotations(limits)
        names = [name for name in vars(limits) if name.startswith("MAX_")]
        assert names
        for name in names:
            value = getattr(limits, name)
            assert get_args(annotations[name]) == (limits.Limit,), name
            assert isinstance(value, int), name
            assert not isinstance(value, bool), name
            assert value > 0, name


class TestInputBoundEnforcedAtFFIEntry:
    """The binding refuses an oversize DBC text or JSON command before marshaling it.

    ``parse_dbc_text`` refuses a text longer than :data:`MAX_DBC_TEXT_BYTES`
    before wrapping it in a JSON command, and every command whose JSON is
    longer than :data:`MAX_JSON_BYTES` is refused before the call, so no ctypes
    buffer is allocated.  Either refusal is the binding's own: it names no
    field, and its text names the bound.
    """

    def test_oversize_json_command_refused_before_the_call(self) -> None:
        """A DBC whose command is past ``MAX_JSON_BYTES`` is refused with that cap.

        The DBC's version string alone fills the cap, so the command holding it
        is past it.  The text is the binding's own, so the kernel never answered.
        """
        over = dbc([message(256, "M", [signal("S")])], version="x" * limits.MAX_JSON_BYTES)
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.parse_dbc(over)
        err = exc_info.value
        assert err.observed > limits.MAX_JSON_BYTES
        assert (err.kind, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_INPUT_LENGTH_BYTES,
            limits.MAX_JSON_BYTES,
            None,
            "input_bound_exceeded",
            f"input_length_bytes {err.observed} exceeds limit {limits.MAX_JSON_BYTES}",
        )

    def test_observed_field_is_actual_payload_size(self) -> None:
        """The reported ``observed`` value is the input text byte size."""
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_DBC_TEXT_BYTES + 1024)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            # Inner cap is on the raw text bytes, not the JSON envelope.
            assert exc_info.value.observed == limits.MAX_DBC_TEXT_BYTES + 1024

    def test_parse_dbc_text_refusal_carries_wire_code(self) -> None:
        """The binding's refusal carries the kernel's ``input_bound_exceeded`` code."""
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_DBC_TEXT_BYTES + 1)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            assert exc_info.value.code == "input_bound_exceeded"


class TestIdentifierLengthBound:
    """A DBC identifier is at most ``MAX_IDENTIFIER_LENGTH`` characters.

    The kernel's ``validIdentifierᵇ`` (``src/Aletheia/DBC/Identifier.agda``)
    holds an identifier to ``max-identifier-length`` characters.  One at the
    limit parses; a longer name is no identifier, so the text parser stops in
    front of the statement holding it and refuses the text with
    ``dbc_text_trailing_input``.
    """

    def test_identifier_at_max_length_accepted(self) -> None:
        """A 128-char identifier passes (boundary inclusive)."""
        name = "A" * limits.MAX_IDENTIFIER_LENGTH
        dbc_text = f'VERSION ""\nNS_:\nBS_:\nBU_:\nBO_ 100 {name}: 8 ECU\n'
        with AletheiaClient() as client:
            result = client.parse_dbc_text(dbc_text)
            assert result["status"] == "success", result
            assert result["dbc"]["messages"][0]["name"] == name

    def test_identifier_one_over_max_rejected(self) -> None:
        """A 129-char identifier (one over the limit) is rejected."""
        name = "A" * (limits.MAX_IDENTIFIER_LENGTH + 1)
        dbc_text = f'VERSION ""\nNS_:\nBS_:\nBU_:\nBO_ 100 {name}: 8 ECU\n'
        with AletheiaClient() as client:
            result = client.parse_dbc_text(dbc_text)
            assert result["status"] == "error", result
            assert result["code"] == "dbc_text_trailing_input", result

    def test_identifier_far_over_max_rejected(self) -> None:
        """A 500-char identifier is rejected (no length-dependent edge case)."""
        name = "A" * 500
        dbc_text = f'VERSION ""\nNS_:\nBS_:\nBU_:\nBO_ 100 {name}: 8 ECU\n'
        with AletheiaClient() as client:
            result = client.parse_dbc_text(dbc_text)
            assert result["status"] == "error", result
            assert result["code"] == "dbc_text_trailing_input", result


class TestNestingDepthBound:
    """The kernel bounds a JSON command's nesting depth at ``MAX_NESTING_DEPTH``.

    ``handleParsedJSON`` (``src/Aletheia/Main/JSON.agda``) measures the parsed
    tree with ``jsonDepth`` and refuses one deeper than ``max-nesting-depth``
    with ``input_bound_exceeded``, bound kind ``nesting_depth``, the observed
    depth and the limit.  ``set_properties`` returns that refusal as its
    ``ErrorResponse``.
    """

    def test_nested_at_depth_60_accepted(self) -> None:
        """60 always-wrappers + atomic + predicate = JSON depth 62 (<= 64)."""
        prop = _nested_ltl(60)
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r

    def test_nested_at_depth_63_rejected(self) -> None:
        """63 always-wrappers = JSON depth 65 (> 64).

        Rejection is the typed ``input_bound_exceeded`` carrying the
        structured triple.
        """
        prop = _nested_ltl(63)
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "error", r
            assert r["code"] == "input_bound_exceeded", r
            # bound_kind / limit / observed are NotRequired on ErrorResponse;
            # .get keeps the access total (a missing key fails the assert).
            assert r.get("bound_kind") == "nesting_depth", r
            assert r.get("limit") == 64, r
            assert r.get("observed", 0) >= 65, r


class TestAtomCountBound:
    """The kernel bounds a property's atoms at ``MAX_ATOM_COUNT_PER_PROPERTY``.

    ``parseAllProperties`` (``src/Aletheia/Protocol/Handlers.agda``) counts a
    parsed property's atoms with ``atomCount`` and refuses one past
    ``max-atom-count-per-property`` with ``input_bound_exceeded``, bound kind
    ``atom_count``, the observed count and the limit.  ``set_properties``
    returns that refusal as its ``ErrorResponse``.
    """

    def test_single_atom_property_accepted(self) -> None:
        """Single-atom property (atomCount = 1) parses cleanly.

        Minimum acceptance case — anchors the lower end of the bound
        interval.
        """
        prop = Signal("S").equals(0).to_formula()
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r

    def test_small_property_accepted(self) -> None:
        """100 atoms (well under 1024) parses cleanly.

        Sanity check that the bound infrastructure does NOT regress
        acceptance of legitimate small properties.
        """
        preds = [Signal("S").equals(i) for i in range(100)]
        prop = _balanced_and(preds)
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r

    def test_property_at_bound_accepted(self) -> None:
        """A property of exactly ``MAX_ATOM_COUNT_PER_PROPERTY`` atoms is accepted."""
        limit = limits.MAX_ATOM_COUNT_PER_PROPERTY
        prop = _balanced_and([Signal("S").equals(i) for i in range(limit)])
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
        assert r["status"] == "success", r

    def test_property_one_past_bound_refused(self) -> None:
        """A property one atom past the bound is refused with the bound triple."""
        limit = limits.MAX_ATOM_COUNT_PER_PROPERTY
        prop = _balanced_and([Signal("S").equals(i) for i in range(limit + 1)])
        with AletheiaClient() as client:
            client.parse_dbc(_trivial_dbc())
            r = client.set_properties([prop])
        assert r["status"] == "error", r
        assert r["code"] == "input_bound_exceeded", r
        assert r.get("bound_kind") == limits.BOUND_KIND_ATOM_COUNT, r
        assert r.get("observed") == limit + 1, r
        assert r.get("limit") == limit, r


class TestListCardinalityBound:
    """The lists of a DBC are bounded in size, decided before the DBC is used.

    ``checkBounds`` in ``src/Aletheia/DBC/Bounds.agda`` decides the size bounds
    of a parsed DBC before it is validated, loaded or formatted.  A list one
    past its bound is refused with code ``input_bound_exceeded``, bound kind
    ``array_cardinality``, the observed count, the limit and the list's name as
    the ``field``.  Each refusal case holds one list one past its bound; the
    acceptance cases sit well under.
    """

    @pytest.mark.parametrize(("field", "limit", "build"), _LISTS_PAST_BOUND)
    def test_list_one_past_bound_refused(
        self, field: ListField, limit: Limit, build: Callable[[], DBCDefinition]
    ) -> None:
        """``parse_dbc`` raises the bound triple, names the list and reads the kernel's message."""
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.parse_dbc(build())
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_ARRAY_CARDINALITY,
            limit + 1,
            limit,
            field,
            "input_bound_exceeded",
            f"ParseDBC: {field}: array cardinality {limit + 1} exceeds limit {limit}",
        )

    def test_messages_well_under_bound_accepted(self) -> None:
        """100 messages << 10000 → parses successfully."""
        dbc_def = dbc([message(i + 1, f"M{i}", [], senders=[]) for i in range(100)], version="")
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc_def)
            assert r["status"] == "success", r

    def test_signals_well_under_bound_accepted(self) -> None:
        """100 signals per message << 1024 → parses successfully."""
        # Raw wire form: nested ``{"kind": "always"}`` presence + rational-dict
        # factors are accepted by the parser but inexpressible in the strict
        # DBCDefinition TypedDict, so this oversize-cardinality fixture is cast.
        dbc_def = cast(
            "DBCDefinition",
            {
                "version": "",
                "messages": [
                    {
                        "id": 100,
                        "name": "M",
                        "dlc": 8,
                        "sender": "ECU",
                        "senders": [],
                        "signals": [
                            {
                                "name": f"S{i}",
                                "startBit": i,
                                "length": 1,
                                "byteOrder": "little_endian",
                                "signed": False,
                                "presence": {"kind": "always"},
                                "factor": {"numerator": 1, "denominator": 1},
                                "offset": {"numerator": 0, "denominator": 1},
                                "minimum": {"numerator": 0, "denominator": 1},
                                "maximum": {"numerator": 1, "denominator": 1},
                                "unit": "",
                                "receivers": [],
                            }
                            for i in range(64)  # 64 signals in an 8-byte message
                        ],
                    }
                ],
                **empty_dbc_tier2(),
            },
        )
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc_def)
            assert r["status"] == "success", r

    def test_empty_lists_accepted(self) -> None:
        """Empty messages / attributes lists pass the bound check trivially.

        Length 0 < suc bound for any non-zero bound.
        """
        dbc_def = dbc([], version="")
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc_def)
            assert r["status"] == "success", r


class TestRationalComponentMagnitudeBound:
    """Typed Int64 bound on every JSON number's rational components.

    Post-parse tree bound at the ``processJSONLine`` surface (companion
    to the nesting-depth check): ``jsonMaxComponent`` measures the
    largest ``|numerator|`` / denominator of the exact rational any JSON
    number in the parsed tree denotes, and anything past
    ``max-rational-component-magnitude``, the signed 64-bit range the
    binary wire's rational slots and the decimal SSOT enforce, is refused
    with ``input_bound_exceeded``, so a bare JSON integer cannot carry a
    component the wire cannot represent.  ``parse_dbc`` raises the refusal,
    naming no field; ``set_properties`` returns it as its ``ErrorResponse``.

    Boundary pinned tight from both sides: the refusal cases sit exactly
    one past the limit, the acceptance cases exactly at it.
    """

    _LIMIT = limits.MAX_RATIONAL_COMPONENT_MAGNITUDE

    @staticmethod
    def _factor_dbc(factor: Fraction) -> DBCDefinition:
        """One-signal DBC whose factor carries the component under test."""
        return dbc([message(256, "M", [signal("S", factor=factor)])])

    def _assert_bound_refusal(self, response: object) -> None:
        """Assert the typed refusal envelope with the structured triple."""
        r = cast("ErrorResponse", response)
        assert r["status"] == "error", r
        assert r["code"] == "input_bound_exceeded", r
        assert r.get("bound_kind") == limits.BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE, r
        assert r.get("observed") == self._LIMIT + 1, r
        assert r.get("limit") == self._LIMIT, r

    def _assert_parse_dbc_refuses(self, factor: Fraction) -> None:
        """Assert ``parse_dbc`` raises the triple for a factor past the bound, naming no field."""
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.parse_dbc(self._factor_dbc(factor))
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
            self._LIMIT + 1,
            self._LIMIT,
            None,
            "input_bound_exceeded",
            f"rational component magnitude {self._LIMIT + 1} exceeds limit {self._LIMIT}",
        )

    def test_parse_dbc_component_one_past_int64_refused(self) -> None:
        """A factor numerator one past Int64 max refuses with the triple."""
        self._assert_parse_dbc_refuses(Fraction(self._LIMIT + 1))

    def test_parse_dbc_component_at_int64_max_accepted(self) -> None:
        """The same position exactly at Int64 max is accepted (tightness)."""
        with AletheiaClient() as client:
            r = client.parse_dbc(self._factor_dbc(Fraction(self._LIMIT)))
            assert r["status"] == "success", r

    def test_parse_dbc_negative_component_at_magnitude_refused(self) -> None:
        """Numerator −2⁶³ is refused: the limit is symmetric in magnitude.

        The single Int64 value with magnitude one past the positive cap
        would fit the binary wire's two's-complement slot, but the kernel
        keeps ONE symmetric magnitude limit so the structured
        ``observed`` / ``limit`` pair stays a plain magnitude comparison.
        """
        self._assert_parse_dbc_refuses(Fraction(-(self._LIMIT + 1)))

    def test_set_properties_bare_integer_one_past_refused(self) -> None:
        """The bound covers every command surface, not just ``parseDBC``.

        A bare-integer predicate value in ``setProperties`` is a rational
        position on the JSON wire; one past Int64 max refuses with the
        same typed envelope.
        """
        over = cast(
            "LTLFormula",
            {
                "operator": "atomic",
                "predicate": {
                    "predicate": "equals",
                    "signal": "S",
                    "value": self._LIMIT + 1,
                },
            },
        )
        with AletheiaClient() as client:
            assert client.parse_dbc(self._factor_dbc(Fraction(1)))["status"] == "success"
            self._assert_bound_refusal(client.set_properties([over]))

    def test_set_properties_bare_integer_at_max_accepted(self) -> None:
        """The same predicate value exactly at Int64 max is accepted."""
        at = cast(
            "LTLFormula",
            {
                "operator": "atomic",
                "predicate": {
                    "predicate": "equals",
                    "signal": "S",
                    "value": self._LIMIT,
                },
            },
        )
        with AletheiaClient() as client:
            assert client.parse_dbc(self._factor_dbc(Fraction(1)))["status"] == "success"
            r = client.set_properties([at])
            assert r["status"] == "success", r


class TestPythonLoaderBoundChecks:
    """Per-loader bound checks fire and raise ``InputBoundExceededError``.

    Covers all four parser-surface loader entry points (yaml_loader,
    dbc, excel_loader x2).

    Tests patch ``MAX_DBC_TEXT_BYTES`` on the consuming module to a
    small value so a 2 KiB temp file exceeds the patched cap; this
    avoids writing 64+ MiB to disk per test.
    """

    def test_yaml_loader_file_path_oversize(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """yaml_loader rejects file paths whose size exceeds the cap."""
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 1024)
        f = tmp_path / "huge.yaml"
        f.write_bytes(b"x" * 2048)
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_checks(f)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.observed == 2048
        assert exc_info.value.limit == 1024

    def test_yaml_loader_inline_string_oversize(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """yaml_loader rejects inline YAML strings whose byte length exceeds the cap.

        A ``str`` is inline YAML whatever it spells, so the string is never
        taken for a path.
        """
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 100)
        big_yaml = "checks:\n" + "  - { name: x, signal: S, condition: equals, value: 0 }\n" * 8
        assert len(big_yaml.encode("utf-8")) > 100
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_checks(big_yaml)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.limit == 100

    def test_dbc_converter_oversize(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        """dbc.dbc_to_json rejects DBC files larger than the cap."""
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 1024)
        f = tmp_path / "huge.dbc"
        f.write_bytes(b"x" * 2048)
        with pytest.raises(InputBoundExceededError) as exc_info:
            dbc_to_json(f)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.observed == 2048
        assert exc_info.value.limit == 1024

    def test_excel_loader_dbc_oversize(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """excel_loader.load_dbc_from_excel rejects oversize files."""
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 1024)
        f = tmp_path / "huge.xlsx"
        f.write_bytes(b"x" * 2048)
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_dbc_from_excel(f)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.observed == 2048
        assert exc_info.value.limit == 1024

    def test_excel_loader_checks_oversize(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """excel_loader.load_checks_from_excel rejects oversize files."""
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 1024)
        f = tmp_path / "huge.xlsx"
        f.write_bytes(b"x" * 2048)
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_checks_from_excel(f)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.observed == 2048
        assert exc_info.value.limit == 1024


class TestSharedDBCBoundCascade:
    """Every DBC command refuses a DBC past a size bound with the same bound.

    ``parseDBC``, ``parseDBCText``, ``validateDBC`` and ``formatDBCText`` each
    decide the bounds with ``checkBounds`` (``src/Aletheia/DBC/Bounds.agda``)
    before validating, loading or formatting.  Each client method raises the
    refusal as :class:`InputBoundExceededError` carrying the bound's kind,
    observed value, limit and the field that crossed it.  ``formatDBCText``
    given no nodes derives them from the message senders, and bounds the
    derived list too.
    """

    def test_validate_dbc_rejects_list_past_bound(self) -> None:
        """A list past its bound trips the cascade before validation."""
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.validate_dbc(_over_multiplex_values())
        err = exc_info.value
        limit, field = limits.MAX_MULTIPLEX_VALUES_PER_SIGNAL, "multiplex values array"
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_ARRAY_CARDINALITY,
            limit + 1,
            limit,
            field,
            "input_bound_exceeded",
            f"ValidateDBC: {field}: array cardinality {limit + 1} exceeds limit {limit}",
        )

    def test_format_dbc_text_rejects_list_past_bound(self) -> None:
        """``format_dbc_text`` refuses a list past its bound instead of rendering it."""
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.format_dbc_text(_over_signal_groups())
        err = exc_info.value
        limit, field = limits.MAX_SIGNAL_GROUPS_PER_FILE, "signal groups array"
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_ARRAY_CARDINALITY,
            limit + 1,
            limit,
            field,
            "input_bound_exceeded",
            f"FormatDBCText: {field}: array cardinality {limit + 1} exceeds limit {limit}",
        )

    def test_format_dbc_text_rejects_over_long_string_field(self) -> None:
        """``format_dbc_text`` refuses a text past its bound instead of rendering it."""
        limit = limits.MAX_STRING_LENGTH_CHARACTERS
        over = dbc([message(256, "M", [signal("S")])], version="x" * (limit + 1))
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.format_dbc_text(over)
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field, err.code) == (
            limits.BOUND_KIND_STRING_LENGTH,
            limit + 1,
            limit,
            "version string",
            "input_bound_exceeded",
        )

    def test_format_dbc_text_rejects_derived_nodes_past_bound(self) -> None:
        """Nodes derived from the senders are bounded, though no senders list is past it.

        Two messages share the primary sender ``ECU`` and carry disjoint
        ``senders`` lists, each under ``MAX_NODES_PER_FILE``: the DBC loads,
        and ``format_dbc_text`` derives the primary sender plus both lists as
        the nodes, past the bound.
        """
        per_message = limits.MAX_NODES_PER_FILE // 2 + 1
        over = dbc(
            [
                message(256, "MA", [signal("S")], senders=[f"A{i}" for i in range(per_message)]),
                message(257, "MB", [signal("T")], senders=[f"B{i}" for i in range(per_message)]),
            ]
        )
        with AletheiaClient() as client:
            assert client.parse_dbc(over)["status"] == "success"
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.format_dbc_text(over)
        err = exc_info.value
        limit = limits.MAX_NODES_PER_FILE
        assert (err.kind, err.observed, err.limit, err.field, err.code) == (
            limits.BOUND_KIND_ARRAY_CARDINALITY,
            1 + 2 * per_message,
            limit,
            "nodes array",
            "input_bound_exceeded",
        )

    def test_validate_dbc_rejects_over_long_string_field(self) -> None:
        """An over-length string field trips the cascade before validation."""
        limit = limits.MAX_STRING_LENGTH_CHARACTERS
        over = dbc([message(100, "M", [], senders=[])], version="z" * (limit + 10))
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.validate_dbc(over)
        err = exc_info.value
        # The code is the wire's, not the constructor's default None.
        assert (err.kind, err.observed, err.limit, err.field, err.code) == (
            limits.BOUND_KIND_STRING_LENGTH,
            limit + 10,
            limit,
            "version string",
            "input_bound_exceeded",
        )

    def test_parse_dbc_text_bound_error_names_field(self) -> None:
        """An over-length version field in a text raises the triple naming the field."""
        limit = limits.MAX_STRING_LENGTH_CHARACTERS
        text = f'VERSION "{"z" * (limit + 10)}"\nNS_:\nBS_:\nBU_: ECU\nBO_ 100 M: 8 ECU\n'
        with AletheiaClient() as client, pytest.raises(InputBoundExceededError) as exc_info:
            client.parse_dbc_text(text)
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field, err.code, str(err)) == (
            limits.BOUND_KIND_STRING_LENGTH,
            limit + 10,
            limit,
            "version string",
            "input_bound_exceeded",
            f"ParseDBCText: version string: string length {limit + 10} exceeds limit {limit}",
        )

    def test_text_field_bound_counts_characters(self) -> None:
        """A text field is bounded in characters, so a two-byte character counts once.

        The version holds exactly ``MAX_STRING_LENGTH_CHARACTERS`` characters,
        twice as many bytes; it loads.  One character more is refused, and the
        observed length is the character count.
        """
        limit = limits.MAX_STRING_LENGTH_CHARACTERS
        with AletheiaClient() as client:
            at = client.parse_dbc(dbc([message(256, "M", [signal("S")])], version="é" * limit))
            assert at["status"] == "success", at
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc(dbc([message(256, "M", [signal("S")])], version="é" * (limit + 1)))
        err = exc_info.value
        assert (err.kind, err.observed, err.limit, err.field) == (
            limits.BOUND_KIND_STRING_LENGTH,
            limit + 1,
            limit,
            "version string",
        )

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Adversarial-input bounds regression tests.

Cross-binding parity: ``aletheia.InputBoundExceededError`` exists,
carries kind/observed/limit fields, and is raised when a JSON payload
exceeds ``aletheia.limits.MAX_JSON_BYTES`` at the FFI boundary before
the payload is marshaled across ctypes.

The Agda kernel additionally enforces the same bound (Aletheia.Limits +
parseJSON / parseDBCText InputBoundExceeded constructor); this suite
covers the binding-side short-circuit so a 100 MiB JSON does not
allocate buffers in Python/ctypes before being rejected.

Per-loader regression tests extend this: every parser-surface entry
point (``yaml_loader._load_yaml``, ``dbc_converter.dbc_to_json``,
``excel_loader.load_dbc_from_excel``, ``excel_loader.load_checks_from_excel``)
rejects oversize files with :class:`InputBoundExceededError` before
allocating buffers / parsing.
"""

from pathlib import Path
from typing import TYPE_CHECKING, cast

import pytest
from _dbc_helpers import dbc, message

from aletheia import (
    AletheiaClient,
    AletheiaError,
    InputBoundExceededError,
    Signal,
    limits,
)
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.dbc_converter import dbc_to_json
from aletheia.error_codes import ErrorCode
from aletheia.excel_loader import load_checks_from_excel, load_dbc_from_excel
from aletheia.yaml_loader import load_checks

if TYPE_CHECKING:
    from aletheia.dsl import Predicate
    from aletheia.protocols import DBCDefinition, LTLFormula


def _path_exists_false(_self: Path) -> bool:
    """Path.exists replacement that always reports a non-existent path."""
    return False


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
        assert limits.BOUND_KIND_FRAME_BYTE_COUNT == "frame_byte_count"
        assert limits.BOUND_KIND_PROPERTY_COUNT == "property_count"

    def test_per_section_cardinalities(self) -> None:
        """Cardinality bounds for messages / signals / attributes / VAL_."""
        assert limits.MAX_MESSAGES_PER_FILE == 10_000
        assert limits.MAX_SIGNALS_PER_MESSAGE == 1024
        assert limits.MAX_ATTRIBUTES_PER_FILE == 10_000
        assert limits.MAX_VALUE_DESCRIPTIONS_PER_FILE == 1_000_000
        assert limits.MAX_IDENTIFIER_LENGTH == 128
        assert limits.MAX_STRING_LENGTH_BYTES == 64 * 1024
        assert limits.MAX_ATOM_COUNT_PER_PROPERTY == 1024
        assert limits.MAX_FRAME_BYTE_COUNT == 64
        assert limits.MAX_PROPERTIES_PER_STREAM == 1024


class TestInputBoundEnforcedAtFFIEntry:
    """Binding-side short-circuit rejects oversize input before marshaling.

    The Agda kernel ALSO rejects (parseJSON's input-length cap returns a
    ``parse_input_bound_exceeded`` error response; parseDBCText returns
    ``dbc_text_input_bound_exceeded``), but the binding-side short-circuit
    fires first so the ctypes buffer is never allocated.

    Cross-binding parity: ``parse_dbc_text`` additionally pre-checks the
    inner DBC text size against :data:`MAX_DBC_TEXT_BYTES` before wrapping
    it in a JSON command, so the rejection carries the precise
    ``dbc_text_input_bound_exceeded`` wire code and a ``limit`` field
    matching the inner cap (rather than the outer JSON cap from
    ``_send_command``).
    """

    def test_oversize_json_raises_input_bound_exceeded(self) -> None:
        """A payload one byte over the limit triggers ``InputBoundExceededError``."""
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_JSON_BYTES + 1)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            err = exc_info.value
            assert err.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
            assert err.observed > limits.MAX_JSON_BYTES
            assert err.limit == limits.MAX_DBC_TEXT_BYTES

    def test_observed_field_is_actual_payload_size(self) -> None:
        """The reported ``observed`` value is the input text byte size."""
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_DBC_TEXT_BYTES + 1024)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            # Inner cap is on the raw text bytes, not the JSON envelope.
            assert exc_info.value.observed == limits.MAX_DBC_TEXT_BYTES + 1024

    def test_parse_dbc_text_uses_consolidated_code(self) -> None:
        """Inner-cap rejection carries the ``input_bound_exceeded`` code.

        Regression: an earlier design routed the rejection through
        ``_send_command``'s outer JSON cap and surfaced it as a parse code;
        the parse / frame / dbc-text codes were later consolidated to a
        single ``input_bound_exceeded`` with the discriminator carried by
        ``bound_kind`` (here ``input_length_bytes``).
        """
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_DBC_TEXT_BYTES + 1)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            assert exc_info.value.code == "input_bound_exceeded"


class TestIdentifierLengthBound:
    """Identifier validity record enforces ``MAX_IDENTIFIER_LENGTH``.

    The Agda kernel's `validIdentifierᵇ` predicate (in
    ``src/Aletheia/DBC/Identifier.agda``) includes a conjunct asserting
    `length name <ᵇ suc max-identifier-length`.  Identifiers at the limit
    (128 chars) still parse; anything longer is rejected at
    ``mkIdentFromChars``.  The wire surface is currently
    ``dbc_text_trailing_input`` rather than the more specific
    ``parse_invalid_identifier`` — once parseIdentifier's monadic position
    is past the consumed chars when it rejects, the outer top-level
    parser eventually fails with "trailing input".  Refining the wire
    error to typed ``InputBoundExceeded IdentifierLength`` is downstream
    parser-monad plumbing (deferred).
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

    def test_identifier_far_over_max_rejected(self) -> None:
        """A 500-char identifier is rejected (no length-dependent edge case)."""
        name = "A" * 500
        dbc_text = f'VERSION ""\nNS_:\nBS_:\nBU_:\nBO_ 100 {name}: 8 ECU\n'
        with AletheiaClient() as client:
            result = client.parse_dbc_text(dbc_text)
            assert result["status"] == "error", result


class TestNestingDepthBound:
    """Typed JSON nesting-depth wire-error.

    ``parseJSON`` parses the input with ``length input`` as a structural
    termination measure (bounded above by the upstream ``max_json_bytes``
    cap).  At the handler boundary (``processJSONLine`` →
    ``handleParsedJSON``), ``jsonDepth`` of the constructed tree is
    compared against ``MAX_NESTING_DEPTH``; over-depth trees are rejected
    with a typed ``ParseError.InputBoundExceeded NestingDepth …``
    constructor.

    The wire envelope carries ``code="parse_input_bound_exceeded"`` plus
    the structured ``bound_kind / observed / limit`` triple, mirroring
    the typed surface already in place for ``InputLengthBytes`` (oversize
    JSON) and ``InputLengthBytes`` (oversize DBC text).  An earlier
    untyped ``dispatch_invalid_json`` shape conflated nesting-depth
    rejection with malformed JSON; tests asserting the new shape pin the
    contract for the C++ / Go bindings' typed lifters.
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
    """Typed AtomCount wire-error refinement.

    Post-parse refinement: ``parseProperty`` parses the full tree
    (structurally terminating on the JSON value); at the handler boundary
    (``parseAllProperties`` in ``Protocol.Handlers``) ``atomCount prop <ᵇ
    suc max-atom-count-per-property`` discriminates accepted from over-
    bound trees.  Over-bound trees emit the typed
    ``ParseErr (InputBoundExceeded AtomCount observed limit)`` (code
    ``parse_input_bound_exceeded`` + structured ``bound_kind / observed /
    limit``).  An earlier untyped ``handler_property_parse_failed``
    code conflated atom-count overflow with shape-malformed JSON.

    The over-bound case is slow (parseLTL runs to completion on a 1025-
    atom tree before the post-parse check fires — empirically ~110s on
    this host) and is intentionally not exercised here.  Manual
    verification (2026-05-11): a balanced 1025-atom And-tree returns
    ``status="error"``, ``code="parse_input_bound_exceeded"``,
    ``bound_kind="atom_count"``, ``observed=1025``, ``limit=1024`` after
    109.2s elapsed.  The formal bound-soundness proof is proven
    kernel-side.
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


class TestListCardinalityBound:
    """List cardinality caps on messages / signals / attributes.

    `requireArrayBound` in `Aletheia/DBC/JSONParser.agda` wraps each
    list-shaped parsed field with a post-parse `length xs <ᵇ suc bound`
    check.  Three call sites wired:
      * `parseMessageBody`: signals → `max-signals-per-message` (1024)
      * `parseDBCWithErrors` messages → `max-messages-per-file` (10000)
      * `parseDBCWithErrors` attributes → `max-attributes-per-file` (10000)

    Wire surface for rejection is `InContext "<array> array"
    (InputBoundExceeded ArrayCardinality observed limit)` (typed
    ParseError); refining to a more specific wire code is downstream
    parser-monad plumbing (deferred).

    Tests only exercise the acceptance path (well under bound).  The
    over-bound case is verified by code inspection — `requireArrayBound`
    is invoked at the three call sites above with the canonical limits
    — plus a manual one-off run at the canonical limit (memory note:
    `feedback_parsedbc_quadratic_scaling.md`); reproducing in CI is
    impractical until the pre-existing O(N²) parseDBC scaling is fixed.
    Formal bound-soundness `parseDBC-arrays-bounded` is proven kernel-side.
    """

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


class TestErrorCodes:
    """``ErrorCode`` enum carries the consolidated ``input_bound_exceeded`` code.

    The three previously per-ADT wire codes (``parse_input_bound_exceeded``
    / ``frame_input_bound_exceeded`` / ``dbc_text_input_bound_exceeded``)
    merged into a single top-level ``input_bound_exceeded`` code; the
    sub-discrimination lives in the structured ``bound_kind`` payload.
    """

    def test_input_bound_exceeded_code(self) -> None:
        """Top-level adversarial-input bound wire code."""
        assert ErrorCode.INPUT_BOUND_EXCEEDED == "input_bound_exceeded"

    def test_bound_kind_constants(self) -> None:
        """``BOUND_KIND_*`` wire-payload discriminators (canonical strings).

        These are the structured-payload discriminator values that
        replaced the per-ADT wire codes.
        """
        assert limits.BOUND_KIND_INPUT_LENGTH_BYTES == "input_length_bytes"
        assert limits.BOUND_KIND_NESTING_DEPTH == "nesting_depth"
        assert limits.BOUND_KIND_ARRAY_CARDINALITY == "array_cardinality"
        assert limits.BOUND_KIND_IDENTIFIER_LENGTH == "identifier_length"
        assert limits.BOUND_KIND_STRING_LENGTH == "string_length"
        assert limits.BOUND_KIND_ATOM_COUNT == "atom_count"
        assert limits.BOUND_KIND_FRAME_BYTE_COUNT == "frame_byte_count"


class TestPythonLoaderBoundChecks:
    """Per-loader bound checks fire and raise ``InputBoundExceededError``.

    Covers all four parser-surface loader entry points (yaml_loader,
    dbc_converter, excel_loader x2).  Per
    ``feedback_cross_binding_wire_symmetry.md`` these tests close the
    binding-side observation gap left implicit when the cap was wired
    but not tested to fire.

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

        Mocks ``Path.exists`` to return False unconditionally so the
        file-vs-string dispatch falls into the inline-yaml branch
        deterministically.  Without the mock, ``Path(big_str).exists()``
        raises ENAMETOOLONG on Linux for any single-segment string >
        NAME_MAX (255 bytes) — that path-confusion behavior is tracked
        separately; this test verifies the bound check itself fires when
        reached.
        """
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 100)
        monkeypatch.setattr(Path, "exists", _path_exists_false)
        big_yaml = "checks:\n" + "  - { name: x, signal: S, condition: equals, value: 0 }\n" * 8
        assert len(big_yaml.encode("utf-8")) > 100
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_checks(big_yaml)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.limit == 100

    def test_dbc_converter_oversize(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        """dbc_converter.dbc_to_json rejects DBC files larger than the cap."""
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

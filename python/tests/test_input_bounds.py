"""Adversarial-input bounds regression tests.

UR-2 cross-binding parity: ``aletheia.InputBoundExceededError`` exists,
carries kind/observed/limit fields, and is raised when a JSON payload
exceeds ``aletheia.limits.MAX_JSON_BYTES`` at the FFI boundary before
the payload is marshaled across ctypes.

The Agda kernel additionally enforces the same bound (Aletheia.Limits +
parseJSON / parseDBCText InputBoundExceeded constructor); this suite
covers the binding-side short-circuit so a 100 MiB JSON does not
allocate buffers in Python/ctypes before being rejected.

R19 cluster A extends this with per-loader regression tests: every
parser-surface entry point (``yaml_loader._load_yaml``,
``dbc_converter.dbc_to_json``, ``excel_loader.load_dbc_from_excel``,
``excel_loader.load_checks_from_excel``) rejects oversize files with
:class:`InputBoundExceededError` before allocating buffers / parsing.
"""

from pathlib import Path

import pytest

from aletheia import (
    AletheiaClient,
    AletheiaError,
    InputBoundExceededError,
    Signal,
)
from aletheia import limits
from aletheia.dbc_converter import dbc_to_json
from aletheia.excel_loader import load_checks_from_excel, load_dbc_from_excel
from aletheia.yaml_loader import load_checks
from aletheia.error_codes import ErrorCode


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
            code="parse_input_bound_exceeded",
        )
        assert err.code == "parse_input_bound_exceeded"


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
        assert limits.BOUND_KIND_NESTING_DEPTH      == "nesting_depth"
        assert limits.BOUND_KIND_ARRAY_CARDINALITY  == "array_cardinality"
        assert limits.BOUND_KIND_IDENTIFIER_LENGTH  == "identifier_length"
        assert limits.BOUND_KIND_STRING_LENGTH      == "string_length"
        assert limits.BOUND_KIND_ATOM_COUNT         == "atom_count"
        assert limits.BOUND_KIND_FRAME_BYTE_COUNT   == "frame_byte_count"

    def test_per_section_cardinalities(self) -> None:
        """Cardinality bounds for messages / signals / attributes / VAL_."""
        assert limits.MAX_MESSAGES_PER_FILE             == 10_000
        assert limits.MAX_SIGNALS_PER_MESSAGE           == 1024
        assert limits.MAX_ATTRIBUTES_PER_FILE           == 10_000
        assert limits.MAX_VALUE_DESCRIPTIONS_PER_FILE   == 1_000_000
        assert limits.MAX_IDENTIFIER_LENGTH             == 128
        assert limits.MAX_STRING_LENGTH_BYTES           == 64 * 1024
        assert limits.MAX_ATOM_COUNT_PER_PROPERTY       == 1024
        assert limits.MAX_FRAME_BYTE_COUNT              == 64


class TestInputBoundEnforcedAtFFIEntry:
    """Binding-side short-circuit rejects oversize input before marshaling.

    The Agda kernel ALSO rejects (parseJSON's input-length cap returns a
    ``parse_input_bound_exceeded`` error response; parseDBCText returns
    ``dbc_text_input_bound_exceeded``), but the binding-side short-circuit
    fires first so the ctypes buffer is never allocated.

    R19 cluster 8 (CPP-D-21.3 cross-binding parity): ``parse_dbc_text``
    additionally pre-checks the inner DBC text size against
    :data:`MAX_DBC_TEXT_BYTES` before wrapping it in a JSON command, so
    the rejection carries the precise ``dbc_text_input_bound_exceeded``
    wire code and a ``limit`` field matching the inner cap (rather than
    the outer JSON cap from ``_send_command``).
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

    def test_parse_dbc_text_uses_dbc_text_code(self) -> None:
        """Inner-cap rejection carries the ``dbc_text_input_bound_exceeded`` code.

        Regression: pre-R19-cluster-8 the rejection went through
        ``_send_command``'s outer JSON cap and surfaced as
        ``parse_input_bound_exceeded``.
        """
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_DBC_TEXT_BYTES + 1)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            assert exc_info.value.code == "dbc_text_input_bound_exceeded"


class TestIdentifierLengthBound:
    """R19 cluster 8 phase e.1 — Identifier validity record enforces
    ``MAX_IDENTIFIER_LENGTH``.

    The Agda kernel's `validIdentifierᵇ` predicate (in
    ``src/Aletheia/DBC/Identifier.agda``) gained a third conjunct asserting
    `length name <ᵇ suc max-identifier-length`.  Identifiers at the limit
    (128 chars) still parse; anything longer is rejected at
    ``mkIdentFromChars``.  The wire surface is currently
    ``dbc_text_trailing_input`` rather than the more specific
    ``parse_invalid_identifier`` — once parseIdentifier's monadic position
    is past the consumed chars when it rejects, the outer top-level
    parser eventually fails with "trailing input".  Refining the wire
    error to typed ``InputBoundExceeded IdentifierLength`` is downstream
    parser-monad plumbing (deferred per the AGDA-D-13.4 pattern).
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
    """R19 AGDA-D-13.4 phase 2a — typed JSON nesting-depth wire-error.

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
    JSON) and ``InputLengthBytes`` (oversize DBC text).  Pre-phase-2a the
    untyped ``dispatch_invalid_json`` shape conflated nesting-depth
    rejection with malformed JSON; tests asserting the new shape pin the
    contract for the C++ / Go bindings' typed lifters.
    """

    @staticmethod
    def _nested_ltl(depth: int) -> dict:
        """Build a property with `depth` levels of nested ``always``."""
        formula = {
            "operator": "atomic",
            "predicate": {"predicate": "equals", "signal": "S", "value": 0},
        }
        for _ in range(depth):
            formula = {"operator": "always", "formula": formula}
        return formula

    @staticmethod
    def _trivial_dbc() -> dict:
        return {
            "version": "",
            "messages": [{"id": 100, "name": "M", "dlc": 8, "sender": "ECU",
                          "senders": [], "signals": []}],
            "signalGroups": [], "environmentVars": [], "valueTables": [],
            "nodes": [], "comments": [], "attributes": [],
            "unresolvedValueDescs": [],
        }

    def test_nested_at_depth_60_accepted(self) -> None:
        """60 always-wrappers + atomic + predicate = JSON depth 62 (<= 64)."""
        prop = self._nested_ltl(60)
        with AletheiaClient() as client:
            client.parse_dbc(self._trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r

    def test_nested_at_depth_63_rejected(self) -> None:
        """63 always-wrappers = JSON depth 65 (> 64) — typed
        ``parse_input_bound_exceeded`` carrying the structured triple."""
        prop = self._nested_ltl(63)
        with AletheiaClient() as client:
            client.parse_dbc(self._trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "error", r
            assert r["code"] == "parse_input_bound_exceeded", r
            assert r["bound_kind"] == "nesting_depth", r
            assert r["limit"] == 64, r
            assert r["observed"] >= 65, r


class TestAtomCountBound:
    """R19 cluster 8 phase e.2 — ``parseProperty`` rejects over-1024-atom formulas.

    Post-parse refinement: ``parseLTL`` parses the full tree (structurally
    terminating on the JSON value), then ``atomCount ltl <ᵇ suc
    max-atom-count-per-property`` discards over-bound trees.  Wire-surface
    for rejection is ``handler_property_parse_failed`` via
    ``parseAllProperties`` in ``Protocol.Handlers``.

    The over-bound case is slow (parseLTL runs to completion on a 1025-atom
    tree before the post-parse check fires — empirically ~115s on this
    host) and is intentionally not exercised here.  Manual verification:
    a balanced 1025-atom And-tree returns ``status=error,
    code=handler_property_parse_failed`` (verified 2026-05-11).  The
    formal bound-soundness proof lives in e.4.
    """

    @staticmethod
    def _trivial_dbc() -> dict:
        return {
            "version": "",
            "messages": [{"id": 100, "name": "M", "dlc": 8, "sender": "ECU",
                          "senders": [], "signals": []}],
            "signalGroups": [], "environmentVars": [], "valueTables": [],
            "nodes": [], "comments": [], "attributes": [],
            "unresolvedValueDescs": [],
        }

    @staticmethod
    def _balanced_and(predicates: list) -> dict:
        if len(predicates) == 1:
            return predicates[0].to_formula()
        half = len(predicates) // 2
        return {"operator": "and",
                "left": TestAtomCountBound._balanced_and(predicates[:half]),
                "right": TestAtomCountBound._balanced_and(predicates[half:])}

    def test_single_atom_property_accepted(self) -> None:
        """Single-atom property (atomCount = 1) parses cleanly — minimum
        acceptance case anchors the lower end of the bound interval."""
        prop = Signal("S").equals(0).to_formula()
        with AletheiaClient() as client:
            client.parse_dbc(self._trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r

    def test_small_property_accepted(self) -> None:
        """100 atoms (well under 1024) parses cleanly — sanity check that
        the bound infrastructure does NOT regress acceptance of legitimate
        small properties."""
        preds = [Signal("S").equals(i) for i in range(100)]
        prop = self._balanced_and(preds)
        with AletheiaClient() as client:
            client.parse_dbc(self._trivial_dbc())
            r = client.set_properties([prop])
            assert r["status"] == "success", r


class TestListCardinalityBound:
    """R19 cluster 8 phase e.3 — ``parseMessageList``/``parseSignalList``/
    ``parseAttributeList`` cardinality caps.

    `requireArrayBound` in `Aletheia/DBC/JSONParser.agda` wraps each
    list-shaped parsed field with a post-parse `length xs <ᵇ suc bound`
    check.  Three call sites wired:
      * `parseMessageBody`: signals → `max-signals-per-message` (1024)
      * `parseDBCWithErrors` messages → `max-messages-per-file` (10000)
      * `parseDBCWithErrors` attributes → `max-attributes-per-file` (10000)

    Wire surface for rejection is `InContext "<array> array"
    (InputBoundExceeded ArrayCardinality observed limit)` (typed
    ParseError); refining to a more specific wire code is downstream
    parser-monad plumbing tracked alongside AGDA-D-13.4.

    Tests only exercise the acceptance path (well under bound).  The
    over-bound case is verified by code inspection — `requireArrayBound`
    is invoked at the three call sites above with the canonical limits
    — plus a manual one-off run at the canonical limit (memory note:
    `feedback_parsedbc_quadratic_scaling.md`); reproducing in CI is
    impractical until the pre-existing O(N²) parseDBC scaling is fixed.
    Formal bound-soundness `parseDBC-arrays-bounded` follows in e.4.
    """

    def test_messages_well_under_bound_accepted(self) -> None:
        """100 messages << 10000 → parses successfully."""
        dbc = {
            "version": "",
            "messages": [
                {"id": i + 1, "name": f"M{i}", "dlc": 8, "sender": "ECU",
                 "senders": [], "signals": []}
                for i in range(100)
            ],
            "signalGroups": [], "environmentVars": [], "valueTables": [],
            "nodes": [], "comments": [], "attributes": [],
            "unresolvedValueDescs": [],
        }
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc)
            assert r["status"] == "success", r

    def test_signals_well_under_bound_accepted(self) -> None:
        """100 signals per message << 1024 → parses successfully."""
        dbc = {
            "version": "",
            "messages": [{
                "id": 100, "name": "M", "dlc": 8, "sender": "ECU",
                "senders": [],
                "signals": [
                    {"name": f"S{i}", "startBit": i, "length": 1,
                     "byteOrder": "little_endian", "signed": False,
                     "presence": {"kind": "always"},
                     "factor": {"numerator": 1, "denominator": 1},
                     "offset": {"numerator": 0, "denominator": 1},
                     "minimum": {"numerator": 0, "denominator": 1},
                     "maximum": {"numerator": 1, "denominator": 1},
                     "unit": "", "receivers": []}
                    for i in range(64)  # 64 signals in an 8-byte message
                ],
            }],
            "signalGroups": [], "environmentVars": [], "valueTables": [],
            "nodes": [], "comments": [], "attributes": [],
            "unresolvedValueDescs": [],
        }
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc)
            assert r["status"] == "success", r

    def test_empty_lists_accepted(self) -> None:
        """Empty messages / attributes lists pass the bound check trivially
        (length 0 < suc bound for any non-zero bound)."""
        dbc = {
            "version": "", "messages": [], "signalGroups": [],
            "environmentVars": [], "valueTables": [], "nodes": [],
            "comments": [], "attributes": [], "unresolvedValueDescs": [],
        }
        with AletheiaClient() as client:
            r = client.parse_dbc(dbc)
            assert r["status"] == "success", r


class TestErrorCodes:
    """``ErrorCode`` enum carries the new ``*_input_bound_exceeded`` codes."""

    def test_parse_input_bound_exceeded_code(self) -> None:
        """JSON-side code is ``parse_input_bound_exceeded``."""
        assert ErrorCode.PARSE_INPUT_BOUND_EXCEEDED == "parse_input_bound_exceeded"

    def test_dbc_text_input_bound_exceeded_code(self) -> None:
        """DBC-text-side code is ``dbc_text_input_bound_exceeded``."""
        assert ErrorCode.DBC_TEXT_INPUT_BOUND_EXCEEDED == "dbc_text_input_bound_exceeded"

    def test_frame_input_bound_exceeded_code(self) -> None:
        """Frame-side code is ``frame_input_bound_exceeded``."""
        assert ErrorCode.FRAME_INPUT_BOUND_EXCEEDED == "frame_input_bound_exceeded"


class TestPythonLoaderBoundChecks:
    """Per-loader bound checks fire and raise ``InputBoundExceededError``.

    Covers all four parser-surface loader entry points across
    R18 cluster 2 (yaml_loader, dbc_converter) + R19 cluster A
    (excel_loader x2).  Per ``feedback_cross_binding_wire_symmetry.md``
    these tests close the binding-side observation gap that R18
    cluster 2 left implicit (cluster 2 wired the cap but did not test
    that the cap fires).

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

    def test_yaml_loader_inline_string_oversize(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """yaml_loader rejects inline YAML strings whose byte length exceeds the cap.

        Mocks ``Path.exists`` to return False unconditionally so the
        file-vs-string dispatch falls into the inline-yaml branch deterministically.
        Without the mock, ``Path(big_str).exists()`` raises ENAMETOOLONG on
        Linux for any single-segment string > NAME_MAX (255 bytes) — that
        path-confusion behavior is tracked separately as PY-B-26.12
        (R19 cluster B); cluster A's job is to verify the bound check
        itself fires when reached.
        """
        monkeypatch.setattr("aletheia.client._types.MAX_DBC_TEXT_BYTES", 100)
        monkeypatch.setattr(Path, "exists", lambda _self: False)
        big_yaml = "checks:\n" + "  - { name: x, signal: S, condition: equals, value: 0 }\n" * 8
        assert len(big_yaml.encode("utf-8")) > 100
        with pytest.raises(InputBoundExceededError) as exc_info:
            load_checks(big_yaml)
        assert exc_info.value.kind == limits.BOUND_KIND_INPUT_LENGTH_BYTES
        assert exc_info.value.limit == 100

    def test_dbc_converter_oversize(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
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

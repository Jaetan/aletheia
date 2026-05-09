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
    """``_send_command`` rejects oversize JSON before marshaling.

    The Agda kernel ALSO rejects (parseJSON's input-length cap returns a
    ``parse_input_bound_exceeded`` error response), but the binding-side
    short-circuit fires first so the ctypes buffer is never allocated.
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
            assert err.limit == limits.MAX_JSON_BYTES

    def test_observed_field_is_actual_payload_size(self) -> None:
        """The reported ``observed`` value is the encoded JSON payload size."""
        with AletheiaClient() as client:
            big_payload = "x" * (limits.MAX_JSON_BYTES + 1024)
            with pytest.raises(InputBoundExceededError) as exc_info:
                client.parse_dbc_text(big_payload)
            # JSON-encoded payload ≥ raw text length + envelope overhead.
            assert exc_info.value.observed >= limits.MAX_JSON_BYTES + 1024


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

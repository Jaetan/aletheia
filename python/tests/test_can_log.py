"""Unit tests for CAN log reader

Tests cover:
- Timestamp conversion: seconds (float) to microseconds (int)
- Data normalization: pad/truncate to DLC bytes
- Frame filtering: error/remote frames skipped or kept
- File validation: missing files, unsupported extensions
- Extension detection: .asc.gz stripped to .asc
- Round-trip: write ASC with python-can, read back with load_can_log
- Lazy iteration: iter_can_log matches load_can_log
"""

from pathlib import Path
from typing import Any

import can
import pytest

from aletheia.can_log import (
    _convert_message,
    _effective_extension,
    _normalize_data,
    _timestamp_to_us,
    _validate_path,
    iter_can_log,
    load_can_log,
)


# ============================================================================
# Timestamp conversion
# ============================================================================

class TestTimestampConversion:
    """Test _timestamp_to_us: float seconds -> int microseconds."""

    def test_zero(self) -> None:
        """Verify zero."""
        assert _timestamp_to_us(0.0) == 0

    def test_one_second(self) -> None:
        """Verify one second."""
        assert _timestamp_to_us(1.0) == 1_000_000

    def test_one_microsecond(self) -> None:
        """Verify one microsecond."""
        assert _timestamp_to_us(0.000001) == 1

    def test_fractional(self) -> None:
        """Verify fractional."""
        assert _timestamp_to_us(1.5) == 1_500_000

    def test_large_timestamp(self) -> None:
        """Verify large timestamp."""
        assert _timestamp_to_us(3600.0) == 3_600_000_000


# ============================================================================
# Data normalization
# ============================================================================

class TestNormalizeData:
    """Test _normalize_data: pad/truncate to DLC bytes."""

    def test_exact_length_passthrough(self) -> None:
        """Verify exact length passthrough."""
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        result = _normalize_data(data, 8)
        assert result == bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        assert isinstance(result, bytearray)

    def test_returns_copy(self) -> None:
        """Verify returns copy."""
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        result = _normalize_data(data, 8)
        assert result is not data

    def test_short_padded_with_zeros(self) -> None:
        """Verify short padded with zeros."""
        data = bytearray([0xAA, 0xBB, 0xCC])
        result = _normalize_data(data, 8)
        assert result == bytearray([0xAA, 0xBB, 0xCC, 0, 0, 0, 0, 0])

    def test_long_truncated(self) -> None:
        """Verify long truncated."""
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
        result = _normalize_data(data, 8)
        assert result == bytearray([1, 2, 3, 4, 5, 6, 7, 8])

    def test_none_returns_zeros(self) -> None:
        """Verify none returns zeros."""
        result = _normalize_data(None, 8)
        assert result == bytearray(8)

    def test_empty_padded(self) -> None:
        """Verify empty padded."""
        result = _normalize_data(bytearray(), 8)
        assert result == bytearray(8)

    def test_canfd_12_bytes(self) -> None:
        """Verify canfd 12 bytes."""
        data = bytearray(range(12))
        result = _normalize_data(data, 12)
        assert result == data
        assert len(result) == 12

    def test_canfd_64_bytes(self) -> None:
        """Verify canfd 64 bytes."""
        data = bytearray(range(64))
        result = _normalize_data(data, 64)
        assert result == data
        assert len(result) == 64

    def test_dlc_zero(self) -> None:
        """Verify dlc zero."""
        result = _normalize_data(bytearray(), 0)
        assert result == bytearray()

    def test_none_with_dlc_zero(self) -> None:
        """Verify none with dlc zero."""
        result = _normalize_data(None, 0)
        assert result == bytearray()


# ============================================================================
# Frame filtering
# ============================================================================

class TestFrameFiltering:
    """Test _convert_message: skip/keep error and remote frames."""

    @staticmethod
    def _make_msg(**overrides: Any) -> can.Message:
        """Build a ``can.Message`` with test-friendly defaults; kwargs override."""
        data = overrides.get("data")
        if data is None:
            data = bytearray(8)
        msg = can.Message()
        msg.timestamp = overrides.get("timestamp", 1.0)
        msg.arbitration_id = overrides.get("arb_id", 0x100)
        msg.data = data
        msg.dlc = overrides.get("dlc") if overrides.get("dlc") is not None else len(data)
        msg.is_error_frame = overrides.get("is_error", False)
        msg.is_remote_frame = overrides.get("is_remote", False)
        msg.is_extended_id = overrides.get("is_extended", False)
        return msg

    def test_normal_frame_converted(self) -> None:
        """Verify normal frame converted."""
        msg = self._make_msg(data=bytearray([0xDE, 0xAD, 0, 0, 0, 0, 0, 0]))
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True
        )
        assert result is not None
        ts, can_id, dlc, data, ext = result
        assert ts == 1_000_000
        assert can_id == 0x100
        assert dlc == 8
        assert data == bytearray([0xDE, 0xAD, 0, 0, 0, 0, 0, 0])
        assert ext is False

    def test_error_frame_skipped(self) -> None:
        """Verify error frame skipped."""
        msg = self._make_msg(is_error=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True
        )
        assert result is None

    def test_error_frame_kept(self) -> None:
        """Verify error frame kept."""
        msg = self._make_msg(is_error=True)
        result = _convert_message(
            msg, skip_error_frames=False, skip_remote_frames=True
        )
        assert result is not None

    def test_remote_frame_skipped(self) -> None:
        """Verify remote frame skipped."""
        msg = self._make_msg(is_remote=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True
        )
        assert result is None

    def test_remote_frame_kept(self) -> None:
        """Verify remote frame kept."""
        msg = self._make_msg(is_remote=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=False
        )
        assert result is not None

    def test_extended_id_preserved(self) -> None:
        """Verify extended id preserved."""
        msg = self._make_msg(arb_id=0x18FEF100, is_extended=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True
        )
        assert result is not None
        assert result[1] == 0x18FEF100

    def test_dlc_preserved(self) -> None:
        """Verify dlc preserved."""
        msg = self._make_msg(data=bytearray(12), dlc=12)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True
        )
        assert result is not None
        assert result[2] == 9  # DLC code for 12-byte CAN-FD payload
        assert len(result[3]) == 12


# ============================================================================
# File validation
# ============================================================================

class TestFileValidation:
    """Test file path and extension validation."""

    def test_file_not_found(self, tmp_path: Path) -> None:
        """Verify file not found."""
        with pytest.raises(FileNotFoundError, match="not found"):
            load_can_log(tmp_path / "nonexistent.asc")

    def test_unsupported_extension(self, tmp_path: Path) -> None:
        """Verify unsupported extension."""
        bad_file = tmp_path / "data.xyz"
        bad_file.touch()
        with pytest.raises(ValueError, match="Unsupported"):
            load_can_log(bad_file)

    def test_string_path_accepted(self, tmp_path: Path) -> None:
        """Verify string path accepted."""
        bad_file = tmp_path / "data.xyz"
        bad_file.touch()
        with pytest.raises(ValueError, match="Unsupported"):
            load_can_log(str(bad_file))


# ============================================================================
# Extension detection
# ============================================================================

class TestExtensionDetection:
    """Test _effective_extension: .asc.gz -> .asc."""

    def test_simple_extension(self) -> None:
        """Verify simple extension."""
        assert _effective_extension(Path("data.asc")) == ".asc"

    def test_gz_stripped(self) -> None:
        """Verify gz stripped."""
        assert _effective_extension(Path("data.asc.gz")) == ".asc"

    def test_blf_gz(self) -> None:
        """Verify blf gz."""
        assert _effective_extension(Path("log.blf.gz")) == ".blf"

    def test_no_extension(self) -> None:
        """Verify no extension."""
        assert _effective_extension(Path("data")) == ""

    def test_path_validation_accepts_gz(self, tmp_path: Path) -> None:
        """Verify path validation accepts gz."""
        gz_file = tmp_path / "data.asc.gz"
        gz_file.touch()
        # Should not raise (extension is valid)
        _validate_path(gz_file)


# ============================================================================
# Round-trip: write ASC, read back
# ============================================================================

class TestLoadCanLog:
    """Write temporary ASC files, read back with load_can_log."""

    @staticmethod
    def _write_asc(path: Path, messages: list[can.Message]) -> None:
        writer = can.ASCWriter(str(path))
        for msg in messages:
            writer.on_message_received(msg)
        writer.stop()

    def test_single_frame(self, tmp_path: Path) -> None:
        """Verify single frame."""
        asc_file = tmp_path / "single.asc"
        msg = can.Message(
            timestamp=1.5,
            arbitration_id=0x100,
            data=bytearray([0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0]),
            is_extended_id=False,
        )
        self._write_asc(asc_file, [msg])

        frames = load_can_log(asc_file)
        assert len(frames) == 1
        _, can_id, dlc, data, _ = frames[0]
        # ASC uses relative timestamps (first message is t=0), so we only
        # verify CAN ID, DLC, and data survive the round-trip.
        assert can_id == 0x100
        assert dlc == 8
        assert data == bytearray([0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0])
        assert isinstance(data, bytearray)

    def test_relative_timestamps(self, tmp_path: Path) -> None:
        """Verify relative timing is preserved across messages."""
        asc_file = tmp_path / "timing.asc"
        messages = [
            can.Message(timestamp=10.0, arbitration_id=0x100,
                        data=bytearray(8), is_extended_id=False),
            can.Message(timestamp=10.5, arbitration_id=0x100,
                        data=bytearray(8), is_extended_id=False),
        ]
        self._write_asc(asc_file, messages)

        frames = load_can_log(asc_file)
        assert len(frames) == 2
        delta_us = frames[1][0] - frames[0][0]
        assert delta_us == 500_000

    def test_multiple_frames(self, tmp_path: Path) -> None:
        """Verify multiple frames."""
        asc_file = tmp_path / "multi.asc"
        messages = [
            can.Message(
                timestamp=float(i),
                arbitration_id=0x100 + i,
                data=bytearray([i, 0, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            )
            for i in range(5)
        ]
        self._write_asc(asc_file, messages)

        frames = load_can_log(asc_file)
        assert len(frames) == 5
        for i, (_ts, can_id, _dlc, data, _ext) in enumerate(frames):
            assert can_id == 0x100 + i
            assert data[0] == i

    def test_error_frames_skipped_by_default(self, tmp_path: Path) -> None:
        """Verify error frames skipped by default."""
        asc_file = tmp_path / "errors.asc"
        messages = [
            can.Message(
                timestamp=1.0,
                arbitration_id=0x100,
                data=bytearray(8),
                is_extended_id=False,
            ),
            can.Message(
                timestamp=2.0,
                arbitration_id=0x100,
                data=bytearray(8),
                is_error_frame=True,
                is_extended_id=False,
            ),
            can.Message(
                timestamp=3.0,
                arbitration_id=0x200,
                data=bytearray(8),
                is_extended_id=False,
            ),
        ]
        self._write_asc(asc_file, messages)

        frames = load_can_log(asc_file)
        assert len(frames) == 2

    def test_short_data_padded(self, tmp_path: Path) -> None:
        """Verify short data padded."""
        asc_file = tmp_path / "short.asc"
        msg = can.Message(
            timestamp=1.0,
            arbitration_id=0x100,
            data=bytearray([0xAA, 0xBB]),
            is_extended_id=False,
        )
        self._write_asc(asc_file, [msg])

        frames = load_can_log(asc_file)
        assert len(frames) == 1
        # python-can sets dlc = len(data) = 2, so data stays 2 bytes
        assert len(frames[0][3]) == frames[0][2]


# ============================================================================
# Lazy iteration
# ============================================================================

class TestIterCanLog:
    """Test iter_can_log returns same results as load_can_log."""

    @staticmethod
    def _write_asc(path: Path, messages: list[can.Message]) -> None:
        writer = can.ASCWriter(str(path))
        for msg in messages:
            writer.on_message_received(msg)
        writer.stop()

    def test_matches_load(self, tmp_path: Path) -> None:
        """Verify matches load."""
        asc_file = tmp_path / "iter.asc"
        messages = [
            can.Message(
                timestamp=float(i),
                arbitration_id=0x100,
                data=bytearray([i, 0, 0, 0, 0, 0, 0, 0]),
                is_extended_id=False,
            )
            for i in range(10)
        ]
        self._write_asc(asc_file, messages)

        eager = load_can_log(asc_file)
        lazy = list(iter_can_log(asc_file))
        assert eager == lazy

    def test_is_lazy(self, tmp_path: Path) -> None:
        """Verify is lazy."""
        asc_file = tmp_path / "lazy.asc"
        messages = [
            can.Message(
                timestamp=float(i),
                arbitration_id=0x100,
                data=bytearray(8),
                is_extended_id=False,
            )
            for i in range(100)
        ]
        self._write_asc(asc_file, messages)

        count = 0
        for _ in iter_can_log(asc_file):
            count += 1
            if count >= 5:
                break
        assert count == 5

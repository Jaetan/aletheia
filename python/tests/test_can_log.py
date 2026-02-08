"""Unit tests for CAN log reader

Tests cover:
- Timestamp conversion: seconds (float) to microseconds (int)
- Data normalization: pad/truncate to 8 bytes, strict_dlc mode
- Frame filtering: error/remote frames skipped or kept
- File validation: missing files, unsupported extensions
- Extension detection: .asc.gz stripped to .asc
- Round-trip: write ASC with python-can, read back with load_can_log
- Lazy iteration: iter_can_log matches load_can_log
"""

from pathlib import Path

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
        assert _timestamp_to_us(0.0) == 0

    def test_one_second(self) -> None:
        assert _timestamp_to_us(1.0) == 1_000_000

    def test_one_microsecond(self) -> None:
        assert _timestamp_to_us(0.000001) == 1

    def test_fractional(self) -> None:
        assert _timestamp_to_us(1.5) == 1_500_000

    def test_large_timestamp(self) -> None:
        assert _timestamp_to_us(3600.0) == 3_600_000_000


# ============================================================================
# Data normalization
# ============================================================================

class TestNormalizeData:
    """Test _normalize_data: pad/truncate to 8 bytes."""

    def test_eight_bytes_passthrough(self) -> None:
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        result = _normalize_data(data, strict_dlc=False)
        assert result == bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        assert isinstance(result, bytearray)

    def test_returns_copy(self) -> None:
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8])
        result = _normalize_data(data, strict_dlc=False)
        assert result is not data

    def test_short_padded_with_zeros(self) -> None:
        data = bytearray([0xAA, 0xBB, 0xCC])
        result = _normalize_data(data, strict_dlc=False)
        assert result == bytearray([0xAA, 0xBB, 0xCC, 0, 0, 0, 0, 0])

    def test_long_truncated(self) -> None:
        data = bytearray([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
        result = _normalize_data(data, strict_dlc=False)
        assert result == bytearray([1, 2, 3, 4, 5, 6, 7, 8])

    def test_none_returns_zeros(self) -> None:
        result = _normalize_data(None, strict_dlc=False)
        assert result == bytearray(8)

    def test_empty_padded(self) -> None:
        result = _normalize_data(bytearray(), strict_dlc=False)
        assert result == bytearray(8)

    def test_strict_dlc_rejects_short(self) -> None:
        with pytest.raises(ValueError, match="3 bytes"):
            _normalize_data(bytearray([1, 2, 3]), strict_dlc=True)

    def test_strict_dlc_rejects_long(self) -> None:
        with pytest.raises(ValueError, match="10 bytes"):
            _normalize_data(bytearray(10), strict_dlc=True)

    def test_strict_dlc_accepts_eight(self) -> None:
        data = bytearray(8)
        result = _normalize_data(data, strict_dlc=True)
        assert len(result) == 8

    def test_strict_dlc_rejects_none(self) -> None:
        with pytest.raises(ValueError, match="no data"):
            _normalize_data(None, strict_dlc=True)


# ============================================================================
# Frame filtering
# ============================================================================

class TestFrameFiltering:
    """Test _convert_message: skip/keep error and remote frames."""

    @staticmethod
    def _make_msg(
        *,
        timestamp: float = 1.0,
        arb_id: int = 0x100,
        data: bytearray | None = None,
        is_error: bool = False,
        is_remote: bool = False,
        is_extended: bool = False,
    ) -> can.Message:
        msg = can.Message()
        msg.timestamp = timestamp
        msg.arbitration_id = arb_id
        msg.data = data if data is not None else bytearray(8)
        msg.dlc = len(msg.data) if msg.data is not None else 0
        msg.is_error_frame = is_error
        msg.is_remote_frame = is_remote
        msg.is_extended_id = is_extended
        return msg

    def test_normal_frame_converted(self) -> None:
        msg = self._make_msg(data=bytearray([0xDE, 0xAD, 0, 0, 0, 0, 0, 0]))
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True, strict_dlc=False
        )
        assert result is not None
        ts, can_id, data = result
        assert ts == 1_000_000
        assert can_id == 0x100
        assert data == bytearray([0xDE, 0xAD, 0, 0, 0, 0, 0, 0])

    def test_error_frame_skipped(self) -> None:
        msg = self._make_msg(is_error=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True, strict_dlc=False
        )
        assert result is None

    def test_error_frame_kept(self) -> None:
        msg = self._make_msg(is_error=True)
        result = _convert_message(
            msg, skip_error_frames=False, skip_remote_frames=True, strict_dlc=False
        )
        assert result is not None

    def test_remote_frame_skipped(self) -> None:
        msg = self._make_msg(is_remote=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True, strict_dlc=False
        )
        assert result is None

    def test_remote_frame_kept(self) -> None:
        msg = self._make_msg(is_remote=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=False, strict_dlc=False
        )
        assert result is not None

    def test_extended_id_preserved(self) -> None:
        msg = self._make_msg(arb_id=0x18FEF100, is_extended=True)
        result = _convert_message(
            msg, skip_error_frames=True, skip_remote_frames=True, strict_dlc=False
        )
        assert result is not None
        assert result[1] == 0x18FEF100


# ============================================================================
# File validation
# ============================================================================

class TestFileValidation:
    """Test file path and extension validation."""

    def test_file_not_found(self, tmp_path: Path) -> None:
        with pytest.raises(FileNotFoundError, match="not found"):
            load_can_log(tmp_path / "nonexistent.asc")

    def test_unsupported_extension(self, tmp_path: Path) -> None:
        bad_file = tmp_path / "data.xyz"
        bad_file.touch()
        with pytest.raises(ValueError, match="Unsupported"):
            load_can_log(bad_file)

    def test_string_path_accepted(self, tmp_path: Path) -> None:
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
        assert _effective_extension(Path("data.asc")) == ".asc"

    def test_gz_stripped(self) -> None:
        assert _effective_extension(Path("data.asc.gz")) == ".asc"

    def test_blf_gz(self) -> None:
        assert _effective_extension(Path("log.blf.gz")) == ".blf"

    def test_no_extension(self) -> None:
        assert _effective_extension(Path("data")) == ""

    def test_path_validation_accepts_gz(self, tmp_path: Path) -> None:
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
        _, can_id, data = frames[0]
        # ASC uses relative timestamps (first message is t=0), so we only
        # verify CAN ID and data survive the round-trip.
        assert can_id == 0x100
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
        for i, (ts, can_id, data) in enumerate(frames):
            assert can_id == 0x100 + i
            assert data[0] == i

    def test_error_frames_skipped_by_default(self, tmp_path: Path) -> None:
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
        assert frames[0][2] == bytearray([0xAA, 0xBB, 0, 0, 0, 0, 0, 0])


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

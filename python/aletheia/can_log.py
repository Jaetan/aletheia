"""CAN log file reader

Read industry-standard CAN log files and convert frames for Aletheia analysis.
Supports ASC, BLF, CSV, candump .log, MF4, and TRC formats via python-can.

Example:
    from aletheia import load_can_log, iter_can_log

    # Eager: load entire file
    frames = load_can_log("drive.blf")
    responses = client.send_frames_batch(frames)

    # Lazy: iterate one frame at a time
    for ts, can_id, data in iter_can_log("highway.asc"):
        response = client.send_frame(ts, can_id, data)
"""

from __future__ import annotations

from collections.abc import Iterator
from pathlib import Path
from typing import Literal

import can

CANFrameTuple = tuple[int, int, bytearray]
"""(timestamp_us, arbitration_id, data) — matches send_frame() signature."""

_SUPPORTED_EXTENSIONS: frozenset[str] = frozenset({
    ".asc", ".blf", ".csv", ".db", ".log", ".mf4", ".trc",
})

_DLC_STANDARD: int = 8


def load_can_log(
    path: str | Path,
    *,
    skip_error_frames: bool = True,
    skip_remote_frames: bool = True,
    strict_dlc: bool = False,
    on_error: Literal["skip", "raise"] = "skip",
) -> list[CANFrameTuple]:
    """Load all CAN frames from a log file into memory.

    Args:
        path: Path to a CAN log file (.asc, .blf, .csv, .log, .mf4, .trc)
        skip_error_frames: Skip CAN error frames (default True)
        skip_remote_frames: Skip remote transmission request frames (default True)
        strict_dlc: Raise ValueError if DLC != 8 (default False; pads/truncates)
        on_error: "skip" to silently skip corrupt frames, "raise" to propagate

    Returns:
        List of (timestamp_us, arbitration_id, data) tuples
    """
    return list(iter_can_log(
        path,
        skip_error_frames=skip_error_frames,
        skip_remote_frames=skip_remote_frames,
        strict_dlc=strict_dlc,
        on_error=on_error,
    ))


def iter_can_log(
    path: str | Path,
    *,
    skip_error_frames: bool = True,
    skip_remote_frames: bool = True,
    strict_dlc: bool = False,
    on_error: Literal["skip", "raise"] = "skip",
) -> Iterator[CANFrameTuple]:
    """Lazily iterate CAN frames from a log file.

    Args:
        path: Path to a CAN log file (.asc, .blf, .csv, .log, .mf4, .trc)
        skip_error_frames: Skip CAN error frames (default True)
        skip_remote_frames: Skip remote transmission request frames (default True)
        strict_dlc: Raise ValueError if DLC != 8 (default False; pads/truncates)
        on_error: "skip" to silently skip corrupt frames, "raise" to propagate

    Yields:
        (timestamp_us, arbitration_id, data) tuples
    """
    resolved = Path(path)
    _validate_path(resolved)

    reader = can.LogReader(str(resolved))
    try:
        for msg in reader:
            try:
                result = _convert_message(
                    msg,
                    skip_error_frames=skip_error_frames,
                    skip_remote_frames=skip_remote_frames,
                    strict_dlc=strict_dlc,
                )
            except (ValueError, TypeError, AttributeError):
                if on_error == "raise":
                    raise
                continue

            if result is not None:
                yield result
    finally:
        reader.stop()


def _validate_path(path: Path) -> None:
    """Validate that the file exists and has a supported extension."""
    if not path.exists():
        raise FileNotFoundError(f"CAN log file not found: {path}")

    ext = _effective_extension(path)
    if ext not in _SUPPORTED_EXTENSIONS:
        raise ValueError(
            f"Unsupported CAN log format '{ext}'. " +
            f"Supported: {', '.join(sorted(_SUPPORTED_EXTENSIONS))}"
        )


def _effective_extension(path: Path) -> str:
    """Get the effective file extension, stripping .gz if present."""
    suffixes = path.suffixes
    if len(suffixes) >= 2 and suffixes[-1] == ".gz":
        return suffixes[-2]
    return path.suffix


def _convert_message(
    msg: can.Message,
    *,
    skip_error_frames: bool,
    skip_remote_frames: bool,
    strict_dlc: bool,
) -> CANFrameTuple | None:
    """Convert a python-can Message to an Aletheia frame tuple.

    Returns None if the message should be skipped.
    """
    if skip_error_frames and msg.is_error_frame:
        return None
    if skip_remote_frames and msg.is_remote_frame:
        return None

    timestamp_us = _timestamp_to_us(msg.timestamp)
    data = _normalize_data(msg.data, strict_dlc=strict_dlc)

    return (timestamp_us, msg.arbitration_id, data)


def _timestamp_to_us(timestamp: float) -> int:
    """Convert seconds (float) to microseconds (int)."""
    return int(timestamp * 1_000_000)


def _normalize_data(data: bytearray | None, *, strict_dlc: bool) -> bytearray:
    """Normalize CAN frame data to exactly 8 bytes.

    - If data is None (remote frames), return 8 zero bytes
    - If strict_dlc is True, raise ValueError for non-8-byte data
    - Otherwise, pad with zeros or truncate to 8 bytes
    """
    if data is None:
        if strict_dlc:
            raise ValueError("Frame has no data (remote frame or error)")
        return bytearray(_DLC_STANDARD)

    if len(data) == _DLC_STANDARD:
        return bytearray(data)

    if strict_dlc:
        raise ValueError(
            f"Frame has {len(data)} bytes, expected {_DLC_STANDARD}"
        )

    if len(data) < _DLC_STANDARD:
        padded = bytearray(_DLC_STANDARD)
        padded[:len(data)] = data
        return padded

    return bytearray(data[:_DLC_STANDARD])

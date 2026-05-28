"""CAN log file reader.

Read industry-standard CAN log files and convert frames for Aletheia analysis.
Supports ASC, BLF, CSV, DB, candump .log, MF4, and TRC formats via python-can.

Example:
    from aletheia import load_can_log, iter_can_log

    # Eager: load entire file
    frames = load_can_log("drive.blf")
    responses = client.send_frames(frames)

    # Lazy: iterate one frame at a time
    for ts, can_id, dlc, data, ext, brs, esi in iter_can_log("highway.asc"):
        response = client.send_frame(ts, can_id, dlc, data, extended=ext, brs=brs, esi=esi)

"""

from collections.abc import Iterator
from pathlib import Path
from typing import Literal

from aletheia.client import CANFrameTuple, ValidationError, bytes_to_dlc
from aletheia.protocols import DLCByteCount, DLCCode

# python-can is an optional extra (`pip install aletheia[can]`).  Surface a
# clear, narrow ImportError naming the optional install rather than letting
# a bare `ModuleNotFoundError: No module named 'can'` bubble up.  Mirrors
# the narrow-swallow pattern in aletheia.__init__ for openpyxl / yaml.
_CAN_IMPORT_ERROR_MSG = (
    "aletheia.can_log requires python-can.  Install via 'pip install aletheia[can]'."
)

try:
    import can
except ImportError as exc:
    raise ImportError(_CAN_IMPORT_ERROR_MSG) from exc

_SUPPORTED_EXTENSIONS: frozenset[str] = frozenset(
    {
        ".asc",
        ".blf",
        ".csv",
        ".db",
        ".log",
        ".mf4",
        ".trc",
    }
)


def load_can_log(
    path: str | Path,
    *,
    skip_error_frames: bool = True,
    skip_remote_frames: bool = True,
    on_error: Literal["skip", "raise"] = "skip",
) -> list[CANFrameTuple]:
    """Load all CAN frames from a log file into memory.

    Args:
        path: Path to a CAN log file (.asc, .blf, .csv, .db, .log, .mf4, .trc)
        skip_error_frames: Skip CAN error frames (default True)
        skip_remote_frames: Skip remote transmission request frames (default True)
        on_error: "skip" to silently skip corrupt frames, "raise" to propagate

    Returns:
        List of (timestamp_us, arbitration_id, dlc, data, extended) tuples

    """
    return list(
        iter_can_log(
            path,
            skip_error_frames=skip_error_frames,
            skip_remote_frames=skip_remote_frames,
            on_error=on_error,
        )
    )


def iter_can_log(
    path: str | Path,
    *,
    skip_error_frames: bool = True,
    skip_remote_frames: bool = True,
    on_error: Literal["skip", "raise"] = "skip",
) -> Iterator[CANFrameTuple]:
    """Lazily iterate CAN frames from a log file.

    Args:
        path: Path to a CAN log file (.asc, .blf, .csv, .db, .log, .mf4, .trc)
        skip_error_frames: Skip CAN error frames (default True)
        skip_remote_frames: Skip remote transmission request frames (default True)
        on_error: "skip" to silently skip corrupt frames, "raise" to propagate

    Yields:
        (timestamp_us, arbitration_id, dlc, data, extended) tuples

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
                )
            except (ValueError, TypeError):
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
        msg = f"CAN log file not found: {path}"
        raise FileNotFoundError(msg)

    ext = _effective_extension(path)
    if ext not in _SUPPORTED_EXTENSIONS:
        raise ValidationError(
            f"Unsupported CAN log format '{ext}'. "
            + f"Supported: {', '.join(sorted(_SUPPORTED_EXTENSIONS))}"
        )


def _effective_extension(path: Path) -> str:
    """Get the effective file extension, stripping .gz if present."""
    suffixes = path.suffixes
    if len(suffixes) > 1 and suffixes[-1] == ".gz":
        return suffixes[-2]
    return path.suffix


def _convert_message(
    msg: can.Message,
    *,
    skip_error_frames: bool,
    skip_remote_frames: bool,
) -> CANFrameTuple | None:
    """Convert a python-can Message to an Aletheia frame tuple.

    Returns None if the message should be skipped.
    """
    if skip_error_frames and msg.is_error_frame:
        return None
    if skip_remote_frames and msg.is_remote_frame:
        return None

    timestamp_us = _timestamp_to_us(msg.timestamp)
    # ``msg.dlc`` from python-can is the byte count (cantools convention);
    # ``bytes_to_dlc`` converts to the 4-bit DLC code that ``CANFrameTuple``
    # carries (CAN wire convention).
    dlc: DLCCode = bytes_to_dlc(DLCByteCount(msg.dlc))
    data = _normalize_data(msg.data, msg.dlc)
    # python-can carries CAN-FD BRS / ESI as ``bitrate_switch`` /
    # ``error_state_indicator`` on every ``Message``; both default to
    # ``False`` for CAN 2.0B logs.  Surface them only when the frame is
    # actually CAN-FD (``is_fd``), per ISO 11898-1:2015 — the bits do not
    # exist on a CAN 2.0B frame and ``None`` is the correct lift.
    brs: bool | None = msg.bitrate_switch if msg.is_fd else None
    esi: bool | None = msg.error_state_indicator if msg.is_fd else None

    return CANFrameTuple(
        timestamp_us,
        msg.arbitration_id,
        dlc,
        data,
        msg.is_extended_id,
        brs,
        esi,
    )


def _timestamp_to_us(timestamp: float) -> int:
    """Convert seconds (float) to microseconds (int)."""
    return int(timestamp * 1_000_000)


def _normalize_data(data: bytearray | None, dlc: int) -> bytearray:
    """Normalize CAN frame data to match the DLC byte count.

    - If data is None (remote frames), return dlc zero bytes
    - If data length matches dlc, return a copy
    - Otherwise, pad with zeros or truncate to dlc bytes
    """
    if data is None:
        return bytearray(dlc)

    if len(data) == dlc:
        return bytearray(data)

    if len(data) < dlc:
        padded = bytearray(dlc)
        padded[: len(data)] = data
        return padded

    return bytearray(data[:dlc])

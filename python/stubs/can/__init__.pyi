"""Type stubs for python-can library.

Only covers the subset of python-can API used by Aletheia's can_log module.
python-can is a third-party library with incomplete type annotations.
"""

from collections.abc import Iterator
from os import PathLike


class Message:
    """CAN message from a log file."""
    timestamp: float
    arbitration_id: int
    data: bytearray
    dlc: int
    is_error_frame: bool
    is_remote_frame: bool
    is_extended_id: bool
    channel: int | str | None


class LogReader(Iterator[Message]):
    """Read CAN messages from a log file.

    Auto-detects format from file extension (.asc, .blf, .csv, .log, .mf4, .trc).
    """
    def __init__(self, filename: str | PathLike[str]) -> None: ...
    def __iter__(self) -> Iterator[Message]: ...
    def __next__(self) -> Message: ...
    def stop(self) -> None: ...


class ASCWriter:
    """Write CAN messages to an ASC file."""
    def __init__(self, filename: str | PathLike[str], channel: int = 1) -> None: ...
    def on_message_received(self, msg: Message) -> None: ...
    def stop(self) -> None: ...

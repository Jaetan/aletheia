"""Type stubs for cantools.database module."""

from cantools.database import can as can

class Database:
    """CAN database loaded from a DBC file."""
    version: str | None
    messages: list[can.Message]

def load_file(path: str) -> Database:
    """Load a DBC file and return a Database object."""
    ...

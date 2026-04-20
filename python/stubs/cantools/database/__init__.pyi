"""Type stubs for cantools.database module."""

from cantools.database import can as can
from cantools.database.can import Database as Database


def load_file(path: str) -> Database:
    """Load a DBC file and return a Database object."""
    ...

"""Type stubs for cantools.database.namedsignalvalue.

``NamedSignalValue`` is the proxy cantools uses when building DBC value-table
entries (see ``dbc._load_value_tables``).  It is not JSON-serialisable, but
``str()`` returns the human-readable name — which is what the Aletheia wire
format consumes.
"""


class NamedSignalValue:
    """Enum-like proxy wrapping a (value, name) pair from a DBC ``VAL_TABLE_``."""
    name: str
    value: int

    def __init__(self, value: int, name: str) -> None: ...
    def __str__(self) -> str: ...

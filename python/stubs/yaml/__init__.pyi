"""Type stubs for PyYAML library.

Only covers the subset of PyYAML API used by Aletheia's yaml_loader module.
PyYAML is a third-party library that does not ship inline types.
"""

from typing import IO


def safe_load(stream: str | bytes | IO[str] | IO[bytes]) -> object: ...

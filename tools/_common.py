"""Shared helpers for the Aletheia developer tooling (the tools/ package).

Centralises the small boilerplate that several gate scripts would otherwise
duplicate -- stdout emission, content hashing -- so each lives in exactly one
place.  Imported as ``from tools._common import ...``; the tools are invoked as
``python -m tools.X`` (see ``tools/__init__.py``).
"""

from __future__ import annotations

import hashlib
import sys
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pathlib import Path


def emit(message: str = "") -> None:
    """Write one line to stdout, the gate scripts' human-readable result channel.

    A single chokepoint for tool output: keeps bare ``print`` out of the package
    (ruff ``T201``) while still sending results to stdout exactly as ``print``
    would.  Use this for normal output; diagnostics go to ``sys.stderr``.
    """
    _ = sys.stdout.write(message + "\n")


def sha256_file(path: Path) -> str:
    """Return the hex SHA-256 of ``path``, read in fixed-size chunks."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()

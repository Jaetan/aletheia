# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The ctypes structures lay out as ``haskell-shim/include/aletheia.h`` fixes them.

The expected sizes and offsets are read from the header's own
``static_assert`` lines, which the C compiler holds to the real layout, so a
field moved on either side fails here rather than misreading across the ABI.
"""

import ctypes
import re
from pathlib import Path

import pytest

from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaDecimal,
    AletheiaFrame,
    AletheiaRational,
    AletheiaSignalValues,
)

_HEADER = Path(__file__).resolve().parents[2] / "haskell-shim" / "include" / "aletheia.h"

_MIRRORS: dict[str, type[ctypes.Structure]] = {
    "aletheia_frame": AletheiaFrame,
    "aletheia_signal_values": AletheiaSignalValues,
    "aletheia_buffer": AletheiaBuffer,
    "aletheia_rational": AletheiaRational,
    "aletheia_decimal": AletheiaDecimal,
}


def _header_layout() -> tuple[dict[str, int], dict[str, dict[str, int]]]:
    """Sizes and field offsets per structure, as the header asserts them."""
    text = _HEADER.read_text(encoding="utf-8")
    sizes = {
        m[1]: int(m[2])
        for m in re.finditer(r"static_assert\(sizeof\(struct (\w+)\) == (\d+),", text)
    }
    offsets: dict[str, dict[str, int]] = {}
    for m in re.finditer(r"static_assert\(offsetof\(struct (\w+), (\w+)\) == (\d+),", text):
        offsets.setdefault(m[1], {})[m[2]] = int(m[3])
    return sizes, offsets


def test_header_asserts_every_mirrored_structure() -> None:
    """The header asserts a size and offsets for exactly the mirrored structures."""
    sizes, offsets = _header_layout()
    assert set(sizes) == set(_MIRRORS)
    assert set(offsets) == set(_MIRRORS)


@pytest.mark.parametrize("name", sorted(_MIRRORS))
def test_mirror_matches_header(name: str) -> None:
    """The mirror has the header's size, fields in its order, and its offsets."""
    sizes, offsets = _header_layout()
    mirror = _MIRRORS[name]
    assert ctypes.sizeof(mirror) == sizes[name]
    actual: dict[str, int] = {
        key: int(value.offset)
        for key, value in vars(mirror).items()
        if isinstance(value, ctypes.CField)
    }
    assert list(actual) == list(offsets[name])
    assert actual == offsets[name]

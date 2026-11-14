# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The ctypes structures lay out as ``haskell-shim/include/aletheia.h`` fixes them.

The expected sizes, alignments and offsets are read from the header's own
``static_assert`` lines, which the C compiler holds to the real layout, so a
field moved on either side fails here rather than misreading across the ABI.
"""

import ctypes
import re
from typing import NewType

import pytest
from _repo_root import REPO_ROOT

from aletheia.client._ffi import (
    AletheiaBuffer,
    AletheiaDecimal,
    AletheiaFrame,
    AletheiaPropertyCheck,
    AletheiaRational,
    AletheiaSignalValues,
    AletheiaText,
    AletheiaTimeBound,
    AletheiaUint128,
)

# A structure's alignment in bytes.
Alignment = NewType("Alignment", int)

# A C structure's tag, as the header spells it after ``struct``.
StructTag = NewType("StructTag", str)

_HEADER = REPO_ROOT / "haskell-shim" / "include" / "aletheia.h"

_MIRRORS: dict[str, type[ctypes.Structure]] = {
    "aletheia_text": AletheiaText,
    "aletheia_frame": AletheiaFrame,
    "aletheia_signal_values": AletheiaSignalValues,
    "aletheia_buffer": AletheiaBuffer,
    "aletheia_uint128": AletheiaUint128,
    "aletheia_rational": AletheiaRational,
    "aletheia_decimal": AletheiaDecimal,
    "aletheia_time_bound": AletheiaTimeBound,
    "aletheia_property_check": AletheiaPropertyCheck,
}


def _header_alignments() -> dict[StructTag, Alignment]:
    """Alignment per structure, as the header asserts it."""
    text = _HEADER.read_text(encoding="utf-8")
    return {
        StructTag(m[1]): Alignment(int(m[2]))
        for m in re.finditer(r"static_assert\(alignof\(struct (\w+)\) == (\d+),", text)
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
    """The header asserts a size, an alignment and offsets for exactly the mirrored structures."""
    sizes, offsets = _header_layout()
    assert set(sizes) == set(_MIRRORS)
    assert set(_header_alignments()) == set(_MIRRORS)
    assert set(offsets) == set(_MIRRORS)


@pytest.mark.parametrize("name", sorted(_MIRRORS))
def test_mirror_matches_header(name: str) -> None:
    """The mirror has the header's size and alignment, fields in its order, and its offsets."""
    sizes, offsets = _header_layout()
    mirror = _MIRRORS[name]
    assert ctypes.sizeof(mirror) == sizes[name]
    assert ctypes.alignment(mirror) == _header_alignments()[StructTag(name)]
    actual: dict[str, int] = {
        key: int(value.offset)
        for key, value in vars(mirror).items()
        if isinstance(value, ctypes.CField)
    }
    assert list(actual) == list(offsets[name])
    assert actual == offsets[name]

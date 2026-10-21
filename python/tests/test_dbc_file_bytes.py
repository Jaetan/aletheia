# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A ``.dbc`` file is read byte for byte, and the kernel decides its characters.

The reader maps every byte to the character of the same number, so a cp1252 file holding a
degree sign is refused by the kernel with ``dbc_invalid_character`` at the byte's line and
column, where it raised the decoder's own error before.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from aletheia import ValidationError
from aletheia.dbc import dbc_to_json

if TYPE_CHECKING:
    from pathlib import Path

_TEXT = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: N\n\nBO_ 1 M: 8 N\n SG_ T : 0|8@1+ (1,0) [0|1] "°C" N\n'
)


def test_a_cp1252_file_is_refused_by_the_kernel_at_the_byte(tmp_path: Path) -> None:
    """The degree sign's byte, 0xB0, reaches the kernel as U+00B0 and is refused at its position."""
    path = tmp_path / "degrees.dbc"
    path.write_bytes(_TEXT.encode("cp1252"))
    with pytest.raises(ValidationError) as caught:
        dbc_to_json(path)
    assert caught.value.code == "dbc_invalid_character"
    line = _TEXT.count("\n", 0, _TEXT.index("°")) + 1
    column = _TEXT.index("°") - _TEXT.rfind("\n", 0, _TEXT.index("°"))
    assert str(caught.value).endswith(
        f"ParseDBCText: character at line {line}, column {column} (code point 176) "
        + "is outside the DBC character set"
    )


def test_a_carriage_return_reaches_the_kernel(tmp_path: Path) -> None:
    """A CRLF file loads: the reader translates no newline, and the kernel reads CR LF as one."""
    path = tmp_path / "crlf.dbc"
    path.write_bytes(_TEXT.replace("°C", "u").replace("\n", "\r\n").encode("ascii"))
    assert dbc_to_json(path)["messages"][0]["signals"][0]["unit"] == "u"

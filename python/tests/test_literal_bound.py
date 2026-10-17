# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A command or a DBC text holding one long number is refused, and the process lives.

The kernel refuses a number whose rational components pass the signed 64-bit
range, and its refusal reports the measured magnitude up to 2^64 - 1 and that
ceiling past it, with "at least" before the ceiling in the message. A command of
about 100 KB whose one number has 100,001 digits gets that refusal, and so does a
DBC text whose one VAL_ key has 100,000 digits, naming the field. Each is sent
from a child process: a kernel that echoes or folds the number whole ends the
process that called it, so the parent reads the child's reply and exit status
rather than sharing its end.
"""

from __future__ import annotations

import os
import subprocess
import sys
from typing import TYPE_CHECKING, cast

import pytest

from aletheia import InputBoundExceededError, limits
from aletheia.client._ffi import (
    RTS_OVERRIDE_ENV,
    KernelResponse,
    find_ffi_library,
    parse_json_object,
)
from aletheia.client._response_parsers import raise_if_input_bound_exceeded

if TYPE_CHECKING:
    from aletheia.types import Response

# The largest `observed` a refusal reports, `observed-ceiling` in Aletheia.Limits.
_OBSERVED_CEILING = 2**64 - 1

# The digits after the leading 1 of the command's one number.
_ZEROS = 100_000

# The child: send the command through the raw entry and write the reply to stdout.
_CHILD = r"""
import sys
from aletheia import FFIBackend

command = b'{"type": "command", "command": "startStream", "x": 1' + b"0" * int(sys.argv[1]) + b"}"
backend = FFIBackend()
state = backend.init()
try:
    sys.stdout.buffer.write(backend.process(state, command))
finally:
    backend.close(state)
"""


@pytest.mark.process(
    "a kernel that echoes this literal whole ends its process, so the call runs in a child"
    + " and the parent reads the refusal the child received"
)
def test_a_long_literal_is_refused_at_the_ceiling() -> None:
    """The 100,001-digit number is refused, its magnitude reported as at least the ceiling."""
    try:
        find_ffi_library()
    except FileNotFoundError:
        pytest.skip("libaletheia-ffi.so not found — run 'cabal run shake -- build'")
    # Removed so a shell that set the runtime's flags does not decide what the
    # child runs under.
    env = {name: value for name, value in os.environ.items() if name != RTS_OVERRIDE_ENV}
    done = subprocess.run(
        [sys.executable, "-c", _CHILD, str(_ZEROS)],
        env=env,
        capture_output=True,
        check=False,
    )
    assert done.returncode == 0, done.stderr.decode(errors="replace")
    reply = cast("Response", parse_json_object(KernelResponse(done.stdout)))
    with pytest.raises(InputBoundExceededError) as exc_info:
        raise_if_input_bound_exceeded(reply)
    err = exc_info.value
    assert (err.kind, err.observed, err.limit, err.field, str(err)) == (
        limits.BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
        _OBSERVED_CEILING,
        limits.MAX_RATIONAL_COMPONENT_MAGNITUDE,
        None,
        f"rational component magnitude at least {_OBSERVED_CEILING}"
        + f" exceeds limit {limits.MAX_RATIONAL_COMPONENT_MAGNITUDE}",
    )


# The digits of the DBC text's one VAL_ key.
_KEY_DIGITS = 100_000

# The child: load the text through the raw entry and write the reply to stdout.
_TEXT_CHILD = r"""
import json
import sys
from aletheia import FFIBackend

text = (
    'VERSION ""\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n'
    'BO_ 200 Msg: 8 ECU\n SG_ Sel : 0|8@1+ (1,0) [0|255] "" ECU\n\n'
    + "VAL_ 200 Sel " + "9" * int(sys.argv[1]) + ' "Big" 1 "On" ;\n'
)
command = json.dumps({"type": "command", "command": "parseDBCText", "text": text}).encode()
backend = FFIBackend()
state = backend.init()
try:
    sys.stdout.buffer.write(backend.process(state, command))
finally:
    backend.close(state)
"""


@pytest.mark.process(
    "a kernel that folds this key whole ends its process, so the call runs in a child"
    + " and the parent reads the refusal the child received"
)
def test_a_long_dbc_text_key_is_refused_at_the_ceiling() -> None:
    """The 100,000-digit VAL_ key is refused naming its field, at the ceiling."""
    try:
        find_ffi_library()
    except FileNotFoundError:
        pytest.skip("libaletheia-ffi.so not found — run 'cabal run shake -- build'")
    env = {name: value for name, value in os.environ.items() if name != RTS_OVERRIDE_ENV}
    done = subprocess.run(
        [sys.executable, "-c", _TEXT_CHILD, str(_KEY_DIGITS)],
        env=env,
        capture_output=True,
        check=False,
    )
    assert done.returncode == 0, done.stderr.decode(errors="replace")
    reply = cast("Response", parse_json_object(KernelResponse(done.stdout)))
    with pytest.raises(InputBoundExceededError) as exc_info:
        raise_if_input_bound_exceeded(reply)
    err = exc_info.value
    assert (err.kind, err.observed, err.limit, err.field, str(err)) == (
        limits.BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE,
        _OBSERVED_CEILING,
        limits.MAX_RATIONAL_COMPONENT_MAGNITUDE,
        "value description key",
        "ParseDBCText: value description key: rational component magnitude at least"
        + f" {_OBSERVED_CEILING} exceeds limit {limits.MAX_RATIONAL_COMPONENT_MAGNITUDE}",
    )

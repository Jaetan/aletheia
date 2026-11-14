# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What ``send_frame`` refuses outside a session and what it hands its backend.

A client not entered refuses a frame with the guard ``StateError``. An entered
client hands the backend's frame entry every field of the frame: the recording
stand-in kernel quotes what its entry was handed in the error envelope it
answers, read as the backend answered it, since its code is no error code and
the client refuses it. The stand-in is the one ``cabal run shake -- build``
makes beside the library.
"""

from __future__ import annotations

import pytest
from _stand_in import StandInName, keeping, stand_in_kernel
from _stream_helpers import refused_outside_a_session

from aletheia import AletheiaClient, FFIBackend, ProtocolError
from aletheia.types import DLCCode

# A 29-bit identifier past the 11-bit range, which only an extended frame carries.
_EXTENDED_ID = 0x18FEF100


def test_a_frame_outside_a_session_is_refused_with_the_guard_message() -> None:
    """A client not entered refuses a frame with the guard StateError and calls no backend."""
    refused, backend = refused_outside_a_session(
        lambda client: client.send_frame(0, 0x100, DLCCode(8), bytes(8))
    )
    assert str(refused) == "Client not initialized \N{EM DASH} use 'with' statement"
    assert not backend.inputs


@pytest.mark.usefixtures("unstarted")
def test_an_extended_frame_reaches_the_entry_whole(monkeypatch: pytest.MonkeyPatch) -> None:
    """The entry is handed the frame's timestamp, 29-bit identifier, extended bit, DLC and bus bits.

    Each bus bit crosses as a byte pair, present then value.
    """
    backend = FFIBackend(lib_path=stand_in_kernel(StandInName("recording_kernel")))
    send, answers = keeping(backend.send_frame_binary)
    monkeypatch.setattr(backend, "send_frame_binary", send)
    with AletheiaClient(backend=backend) as client, pytest.raises(ProtocolError) as refused:
        client.send_frame(
            1000, _EXTENDED_ID, DLCCode(8), bytes(8), extended=True, brs=True, esi=True
        )
    assert str(refused.value) == 'reply code: expected an error code, got "recording_kernel"'
    quote = f"send_frame ts=1000 id={_EXTENDED_ID} extended=1 dlc=8 len=8 brs=1/1 esi=1/1"
    assert answers == [
        f'{{"status":"error","code":"recording_kernel","message":"{quote}"}}'.encode()
    ]

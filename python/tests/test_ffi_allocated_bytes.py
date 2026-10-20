# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""``aletheia.allocated_bytes`` reads the kernel runtime's allocation, whole and at each call.

It reads the library ``RTSState`` latched when a backend started the runtime,
and answers no count before one has.  On the real library a DBC load between
two reads makes the second larger.  The recording stand-in answers 2^63 plus
the reads the process made of it before, so two reads answer exactly that and
one more only if each reached the stand-in and kept the whole unsigned 64-bit
count: a narrower or signed read answers another number.  The null stand-in
answers 0.  A test that reads a stand-in gives the process a latch no backend
has set, so the stand-in's backend latches its own library (its runtime entry a
no-op) and registers it as the renderer in a cell of the test's own, both
restored after the test.  The stand-ins are the ones
``cabal run shake -- build`` makes beside the library.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final

import pytest
from _stand_in import StandInName, stand_in_kernel

from aletheia import AletheiaClient, FFIBackend, RTSState, allocated_bytes

if TYPE_CHECKING:
    from aletheia.types import DBCDefinition

# The recording stand-in's first answer, its high bit set: a 32-bit or signed
# result reads another number.
_RECORDING_BASE: Final = 1 << 63

# The reads this process has made of the recording stand-in, which its next
# answer counts; only this module reads it.
_RECORDING_READS: Final = [0]


@pytest.fixture
def unstarted(monkeypatch: pytest.MonkeyPatch) -> None:
    """Give the test a runtime latch no backend has set, and a renderer cell of its own."""
    monkeypatch.setattr(RTSState, "lib", None)
    monkeypatch.setattr(RTSState, "initialized", False)
    monkeypatch.setattr(RTSState, "refcount", 0)
    monkeypatch.setattr(RTSState, "cores", 0)
    monkeypatch.setattr("aletheia.client._enrichment._RENDERER_LIB", [None])


@pytest.mark.usefixtures("unstarted")
def test_no_count_before_a_backend_starts_the_runtime() -> None:
    """With no backend having started the runtime, the read answers no count."""
    assert allocated_bytes() is None


def test_a_dbc_load_allocates(simple_dbc: DBCDefinition) -> None:
    """The count read after a DBC load is larger than the one read before it."""
    with AletheiaClient() as client:
        before = allocated_bytes()
        loaded = client.parse_dbc(simple_dbc)
        after = allocated_bytes()
    assert loaded["status"] == "success"
    assert before is not None
    assert after is not None
    assert after > before


@pytest.mark.usefixtures("unstarted")
def test_each_read_reaches_the_stand_in_and_keeps_the_whole_64_bit_count() -> None:
    """Two reads of the recording stand-in answer 2^63 + k and 2^63 + k + 1, k its reads before."""
    _ = FFIBackend(lib_path=stand_in_kernel(StandInName("recording_kernel")))
    expected = _RECORDING_BASE + _RECORDING_READS[0]
    first = allocated_bytes()
    second = allocated_bytes()
    _RECORDING_READS[0] += 2
    assert (first, second) == (expected, expected + 1)


@pytest.mark.usefixtures("unstarted")
def test_the_null_kernel_answers_no_allocation() -> None:
    """The null stand-in's answer, 0, is what the read answers."""
    _ = FFIBackend(lib_path=stand_in_kernel(StandInName("null_kernel")))
    assert allocated_bytes() == 0

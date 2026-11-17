# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Freeing a string the library allocated: one pointer declared, and the address crossing whole.

An address crosses an entry declared without argument types as a C ``int``,
its high half dropped, so the library would free a pointer it never handed
out; whether that crashes rests on where the heap was placed.  The free
entry's declaration and the wrapping of every address are each held here,
by reading them, with no call that could reach such a free.
"""

from __future__ import annotations

import ctypes
from types import SimpleNamespace
from typing import cast

import pytest
from _stand_in import StandInName, stand_in_kernel

from aletheia.client._ffi import KernelString, configure_ffi_signatures, free_kernel_string


def test_the_free_entry_takes_one_pointer_and_answers_nothing() -> None:
    """The configured free entry declares one pointer argument and no result."""
    lib = ctypes.CDLL(str(stand_in_kernel(StandInName("null_kernel"))))
    configure_ffi_signatures(lib)
    assert lib.aletheia_free_str.argtypes == [ctypes.c_void_p]
    assert lib.aletheia_free_str.restype is None


@pytest.mark.parametrize("address", [KernelString(2**40 + 5), KernelString(7), None])
def test_an_address_is_freed_whole_as_a_pointer(address: KernelString | None) -> None:
    """Each address, one past 32 bits too, reaches the free entry once, as a pointer, unchanged."""
    freed: list[ctypes.c_void_p] = []
    lib = SimpleNamespace(aletheia_free_str=freed.append)
    free_kernel_string(cast("ctypes.CDLL", lib), address)
    assert len(freed) == 1
    assert isinstance(freed[0], ctypes.c_void_p)
    assert freed[0].value == address

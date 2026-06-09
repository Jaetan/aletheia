# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
r"""Atheris fuzz harness for ``dbc_to_json``.

The Python binding owns ``aletheia.dbc.dbc_to_json`` which converts DBC
text to the wire-format JSON.  This harness drives that converter with
arbitrary byte inputs to surface UB / silent corruption in the loader.

Run:
    python -m atheris fuzz_dbc_to_json.py -- -max_total_time=60 \
        python/tests/fuzz/seed/dbc_to_json/
"""
# pylint: disable=import-error  # atheris is an opt-in fuzz extra.

from __future__ import annotations

import contextlib

import atheris
from _atheris_runner import run

with atheris.instrument_imports():
    from aletheia import AletheiaError, InputBoundExceededError
    from aletheia.dbc import dbc_to_json


def fuzz_one_input(data: bytes) -> None:
    """Atheris harness body — feeds raw DBC text to the converter."""
    fdp = atheris.FuzzedDataProvider(data)
    text = fdp.ConsumeUnicodeNoSurrogates(min(len(data), 4096))
    # Documented error paths.  No assertion needed; the contract is
    # "no panic, no UB, no exception escape past these classes".
    with contextlib.suppress(InputBoundExceededError, AletheiaError, ValueError, TypeError):
        dbc_to_json(text)


if __name__ == "__main__":
    run(fuzz_one_input)

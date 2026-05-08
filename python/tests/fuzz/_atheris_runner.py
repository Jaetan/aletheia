"""Shared atheris setup / Fuzz invocation boilerplate (R18 cluster 5).

Three fuzz harnesses (``fuzz_parse_response``, ``fuzz_dbc_to_json``,
``fuzz_iter_can_log``) share the same Setup → Fuzz pattern.  Extract it
here so each harness file is just the per-target ``TestOneInput`` body
and a single ``run(TestOneInput)`` call.  Eliminates pylint cat 6 R0801
findings on the boilerplate.

Atheris is an opt-in fuzz extra (``aletheia[fuzz]``); this module
imports it lazily from each harness's ``with atheris.instrument_imports():``
block — never imported at the test-collection level.
"""
# pylint: disable=import-error  # atheris is an opt-in fuzz extra.
from __future__ import annotations

import sys
from collections.abc import Callable

import atheris  # type: ignore[import-not-found]


def run(test_one_input: Callable[[bytes], None]) -> None:
    """Wire the fuzz harness into atheris's run loop.

    Each harness defines a ``TestOneInput(data: bytes) -> None`` and
    calls ``run(TestOneInput)``; this hides the Setup/Fuzz pair behind
    a single import.
    """
    atheris.Setup(sys.argv, test_one_input)
    atheris.Fuzz()

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The kernel's check of a formula as a builder makes it.

A builder that carries a checked field (a comparison's value, a range's order,
a tolerance's sign, a time bound, a signal name) hands the formula it made to
``aletheia_check_property``, which reads it as set_properties reads a property
and refuses it with set_properties' reason, so a check is refused where it is
built.  The check is vocal, as the rational renderer and the decimal parser
are: it never starts the GHC runtime, since a start fixes the core count for
the process, and raises while the runtime is down.
"""

from __future__ import annotations

import ctypes
from typing import TYPE_CHECKING

from aletheia.client._ffi import (
    AletheiaPropertyCheck,
    AletheiaText,
    started_library,
    take_error_envelope,
)
from aletheia.client._refusal import raise_entry_refusal
from aletheia.client._types import ValidationError
from aletheia.common_types import Prose
from aletheia.types import dump_json

if TYPE_CHECKING:
    from aletheia.types import LTLFormula


def check_formula(formula: LTLFormula) -> None:
    """Refuse *formula* as the kernel's property parse refuses it, or return.

    Every field, ordering, denominator and time bound is decided, and each
    signal name as an identifier; whether a DBC carries the signal is left to
    set_properties.  The refusal's text is the reason set_properties gives
    after ``SetProperties: property N: ``.

    Raises:
        FFIError: the GHC runtime is not started (no
            :func:`~aletheia.start_runtime` and no client).
        InputBoundExceededError: a number of the formula is past its bound,
            such as a time bound past 2^64-1 microseconds (the kernel's
            ``input_bound_exceeded`` refusal).
        ValidationError: the kernel refused the formula, its ``code`` saying
            how (``handler_property_parse_failed``, ``parse_invalid_identifier``)
            and its text the kernel's reason verbatim.

    """
    lib = started_library(Prose("building a check"))
    raw = dump_json(formula).encode()
    text = AletheiaText(raw, len(raw))
    out = AletheiaPropertyCheck()
    if lib.aletheia_check_property(ctypes.byref(text), ctypes.byref(out)) != 0:
        missing = Prose("aletheia_check_property refused without an error")
        raise_entry_refusal(take_error_envelope(lib, out, missing), error=ValidationError)

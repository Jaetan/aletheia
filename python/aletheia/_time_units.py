# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared time-unit conversion constants.

Cross-binding parity with the Go binding's ``usPerMillisecond``
(``go/aletheia/enrich.go``).  The kernel-binding wire contract is
uniformly *microseconds* for the metric LTL window parameter (see
``src/Aletheia/LTL/Syntax.agda::MetricEventually`` unit-tag inventory);
these constants name the binding-side conversion factors so every ms↔µs
hop is documented at the call site rather than buried in a bare
``* 1000``.

Not in :mod:`aletheia.limits` because those constants mirror Agda
``Aletheia.Limits`` adversarial-input bounds; time-unit factors are
pure UI ergonomics with no Agda counterpart.
"""

from typing import Final

MICROSECONDS_PER_MILLISECOND: Final[int] = 1_000
MICROSECONDS_PER_SECOND: Final[int] = 1_000_000

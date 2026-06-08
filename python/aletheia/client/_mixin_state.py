# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Shared private-state base for the :class:`aletheia.AletheiaClient` mixins.

``StreamingMixin`` and ``SignalOpsMixin`` both call ``self._ffi_lock`` to
serialise FFI calls on the ``StreamState`` against ``close()``.  Declaring it
once here — rather than in each mixin's class-level stub block — keeps those
two already-similar stub blocks from tripping pylint's duplicate-code gate
(R0801) when the lock attribute is added to both.
"""

from __future__ import annotations

from abc import ABC
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import threading


class ClientHostState(ABC):  # pylint: disable=too-few-public-methods
    """Type-checking shim for the ``_ffi_lock`` the host class provides.

    Declares the one attribute both client mixins read; the real value is
    constructed in :meth:`aletheia.AletheiaClient.__init__`.  Centralised here
    (rather than re-declared in each mixin's stub block) so the two
    already-similar stub blocks do not trip pylint R0801.  An ``ABC`` (not a
    ``Protocol``) so the host's ``__init__`` need not chain a non-trivial base
    initialiser.  Naturally has no public methods (a pure type shim), hence the
    ``too-few-public-methods`` waiver — matching the small-class precedents in
    ``aletheia/checks.py``.
    """

    _ffi_lock: threading.Lock

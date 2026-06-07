# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Internal implementation of the Aletheia client — **not** public API.

``aletheia`` is the single canonical public package; import the client
surface from there::

    from aletheia import AletheiaClient, AletheiaError, Signal, dlc_to_bytes

This sub-package holds the FFI loader, the streaming protocol, response
parsers, and the strong-typed exception/result hierarchy as ``_``-prefixed
modules. The public names live in:

* ``_client`` — :class:`AletheiaClient`
* ``_backend`` — :class:`Backend`, :class:`FFIBackend`, :class:`MockBackend`,
  :class:`BinaryPathUnsupportedError`
* ``_ffi`` — :class:`RTSState`
* ``_types`` — the exception hierarchy, the response TypedDicts, and the
  byte/DLC converters

There is intentionally no public re-export surface here: importing a name
straight from ``aletheia.client`` (rather than ``aletheia``) is unsupported
and may break between releases.
"""

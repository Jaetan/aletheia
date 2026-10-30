# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Pure helper functions for response parsing and type conversion.

Split into sub-modules by concern:

* ``rational`` — exact rationals: the kernel's decimal and time-bound entries,
  the outbound float guard and the build values' wire bound.
* ``dbc_normalize`` — outbound (Python TypedDict → wire JSON, ``NotRequired``
  padding) and inbound (a DBC reply → ``DBCDefinition``) normalisation.
* ``json_codec`` — the extraction reply's lists: signal values, errors and
  absent names.
* ``property_check`` — a check's property handed to the kernel's parse at build.
* ``reply_shape`` — the one form every reply reader's refusal is written in.

No backward-compat re-export shim — callers import directly from the
relevant submodule.
"""

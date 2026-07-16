# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Pure helper functions for response parsing and type conversion.

Split into three sub-modules by concern:

* ``rational`` — ℚ arithmetic + parsing + validation (decimal-string via the
  kernel ``from_decimal`` SSOT / Fraction / int / rational-dict wire shapes).
* ``dbc_normalize`` — outbound (Python TypedDict → wire JSON, ``NotRequired``
  padding) and inbound (Agda formatDBC JSON → ``DBCDefinition``) normalisation.
* ``json_codec`` — protocol-level list parsers (signal values / errors /
  absent names) used by the streaming response shape.

No backward-compat re-export shim — callers import directly from the
relevant submodule.
"""

# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""DBC tooling — conversion and structural queries.

The public ``aletheia.dbc`` namespace unifies two concerns over DBC
definitions:

* **Conversion** (``_converter``) — ``dbc_to_json`` / ``dbc_to_text`` /
  ``convert_dbc_file``: parse a ``.dbc`` file to the Agda wire format and
  render it back, via the verified Agda parser/formatter.
* **Queries** (``_queries``) — multiplexing helpers and definition lookups
  (``message_by_id``, ``signal_by_name``, ``is_multiplexed``, …) over the
  ``DBCDefinition`` / ``DBCMessage`` TypedDicts.

Every name here is also re-exported from the top-level ``aletheia`` package
for convenience; ``from aletheia.dbc import dbc_to_json`` and
``from aletheia import dbc_to_json`` are equivalent.
"""

from aletheia.dbc._converter import convert_dbc_file, dbc_to_json, dbc_to_text
from aletheia.dbc._queries import (
    always_present_signals,
    is_multiplexed,
    message_by_id,
    message_by_name,
    multiplexed_signals,
    multiplexor_names,
    mux_values,
    signal_by_name,
    signals_for_mux_value,
)

__all__ = [
    "always_present_signals",
    "convert_dbc_file",
    "dbc_to_json",
    "dbc_to_text",
    "is_multiplexed",
    "message_by_id",
    "message_by_name",
    "multiplexed_signals",
    "multiplexor_names",
    "mux_values",
    "signal_by_name",
    "signals_for_mux_value",
]

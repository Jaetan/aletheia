"""Pure helper functions for response parsing and type conversion.

PY-D-16.1 (R23): split into three sub-modules by concern:

* ``rational`` — ℚ arithmetic + parsing + validation (float / Fraction /
  rational-dict / rational-string).
* ``dbc_normalize`` — outbound (Python TypedDict → wire JSON, ``NotRequired``
  padding) and inbound (Agda formatDBC JSON → ``DBCDefinition``) normalisation.
* ``json_codec`` — protocol-level list parsers (signal values / errors /
  absent names) used by the streaming response shape.

No backward-compat re-export shim per ``feedback_no_backward_compat`` —
callers import directly from the relevant submodule.
"""

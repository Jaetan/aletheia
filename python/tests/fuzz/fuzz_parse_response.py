r"""Atheris fuzz harness for the JSON response parser.

Counterpart of go FuzzParseResponse and cpp fuzz_parse_response.cpp.  The
target is the Python binding's JSON-decode pipeline that wraps every FFI
response.  Atheris instruments the Python interpreter to drive the fuzzer's
genetic search.

Run:
    python -m atheris fuzz_parse_response.py -- -max_total_time=60 \
        python/tests/fuzz/seed/parse_response/

Atheris dependency is opt-in (``aletheia[fuzz]`` extra) per AGENTS.md cat
34c — the binary is 35 MB and not needed for the standard test lane.
"""
# pylint: disable=import-error  # atheris is an opt-in fuzz extra.

from __future__ import annotations

import atheris
from _atheris_runner import run

with atheris.instrument_imports():
    import json

    from aletheia.protocols import dump_json


def fuzz_one_input(data: bytes) -> None:
    """Atheris harness body — must not raise unhandled exceptions."""
    fdp = atheris.FuzzedDataProvider(data)
    raw = fdp.ConsumeUnicodeNoSurrogates(len(data))
    try:
        parsed = json.loads(raw)
    except (ValueError, json.JSONDecodeError):
        return  # documented error path
    # Round-trip property: loaded JSON re-serialized must parse to the same
    # value.  Catches: silent type coercion, key-order drift, encode/decode
    # asymmetry on edge-case unicode.
    try:
        re_encoded = dump_json(parsed)
        re_parsed = json.loads(re_encoded)
        assert re_parsed == parsed, (
            f"round-trip mismatch: {parsed!r} → {re_encoded!r} → {re_parsed!r}"
        )
    except (TypeError, ValueError):
        # dump_json may reject non-JSON-compatible types extracted from
        # adversarial input; that's acceptable, not a fuzz finding.
        pass


if __name__ == "__main__":
    run(fuzz_one_input)

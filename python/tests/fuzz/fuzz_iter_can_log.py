"""Atheris fuzz harness for ``iter_can_log`` (R18 cluster 5 — Cat 34c).

``iter_can_log`` parses CAN log files (asc, blf, mf4) into ``CANFrameTuple``
streams.  This harness drives it with arbitrary byte inputs via an
in-memory file path to surface parser UB / silent corruption.

Run:
    python -m atheris fuzz_iter_can_log.py -- -max_total_time=60 \\
        python/tests/fuzz/seed/iter_can_log/
"""
# pylint: disable=import-error  # atheris is an opt-in fuzz extra.

from __future__ import annotations

import tempfile
from pathlib import Path

import atheris  # type: ignore[import-not-found]

from _atheris_runner import run

with atheris.instrument_imports():
    from aletheia import ValidationError
    from aletheia.can_log import iter_can_log


def fuzz_one_input(data: bytes) -> None:
    """Atheris harness body — feeds bytes to the log iterator via a temp file."""
    fdp = atheris.FuzzedDataProvider(data)
    payload = fdp.ConsumeBytes(min(len(data), 4096))
    with tempfile.NamedTemporaryFile(suffix=".asc", delete=False) as tmp:
        tmp.write(payload)
        tmp_path = Path(tmp.name)
    try:
        # Drain the iterator to completion; iter_can_log is lazy so the
        # parser's invariant must hold over every frame yielded.
        for _frame in iter_can_log(tmp_path, on_error="skip"):
            pass
    except (ValidationError, ValueError, RuntimeError, OSError):
        # Documented error paths; not a fuzz finding.
        pass
    finally:
        tmp_path.unlink(missing_ok=True)


if __name__ == "__main__":
    run(fuzz_one_input)

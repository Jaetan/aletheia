# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Asynchronous mirror of :mod:`aletheia.client` for asyncio code.

Exposes the same set of operation methods as the sync ``AletheiaClient``,
each as ``async def``, implemented as ``asyncio.to_thread`` wrappers
around the verified FFI core. Cancellation works through the standard
``asyncio.CancelledError`` mechanism — see
``docs/architecture/CANCELLATION.md`` for the full contract.

Example:
```python runner:ProgramRunner
import asyncio
from pathlib import Path

from aletheia import load_checks
from aletheia.asyncio import AletheiaClient
from aletheia.can_log import iter_can_log

dbc_text = Path("vehicle.dbc").read_text(encoding="utf-8")

def live_frames():
    yield from iter_can_log("drive.log")  # a live producer stands here

def handle(violation):
    print("violation at", violation["timestamp"], "us")

async def watch(timeout_s: float) -> None:
    async with AletheiaClient() as client:
        await client.parse_dbc_text(dbc_text)
        # The kernel reads every number of the checks, so they load once the client is open.
        await client.add_checks(load_checks(Path("vehicle_checks.yaml")))
        await client.start_stream()
        try:
            async with asyncio.timeout(timeout_s):
                async for r in client.send_frames_iter(live_frames()):
                    if r.violation is not None:
                        handle(r.violation)
        except TimeoutError:
            pass
        await client.end_stream()

asyncio.run(watch(timeout_s=5.0))
```

The two clients are siblings, not interchangeable: a process picks the
sync ``aletheia.AletheiaClient`` *or* this async ``AletheiaClient`` per
underlying ``StablePtr``. Mirrors the ``httpx.Client`` /
``httpx.AsyncClient`` and ``redis.Redis`` / ``redis.asyncio.Redis``
patterns Python users already know.

"""

from aletheia.asyncio._client import AletheiaClient

__all__ = ["AletheiaClient"]

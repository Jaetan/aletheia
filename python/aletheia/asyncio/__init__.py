"""Asynchronous mirror of :mod:`aletheia.client` for asyncio code.

Exposes the same set of operation methods as the sync ``AletheiaClient``,
each as ``async def``, implemented as ``asyncio.to_thread`` wrappers
around the verified FFI core. Cancellation works through the standard
``asyncio.CancelledError`` mechanism — see
``docs/architecture/CANCELLATION.md`` for the full contract.

Example::

    import asyncio
    from aletheia.asyncio import AletheiaClient

    async def watch(timeout_s: float) -> None:
        async with AletheiaClient(dbc=dbc_path) as client:
            await client.set_properties(properties)
            await client.start_stream()
            try:
                async with asyncio.timeout(timeout_s):
                    async for r in client.send_frames_iter(live_frames()):
                        if r.violation is not None:
                            handle(r.violation)
            except TimeoutError:
                pass
            await client.end_stream()

The two clients are siblings, not interchangeable: a process picks the
sync ``aletheia.AletheiaClient`` *or* this async ``AletheiaClient`` per
underlying ``StablePtr``. Mirrors the ``httpx.Client`` /
``httpx.AsyncClient`` and ``redis.Redis`` / ``redis.asyncio.Redis``
patterns Python users already know.
"""

from ._client import AletheiaClient

__all__ = ["AletheiaClient"]

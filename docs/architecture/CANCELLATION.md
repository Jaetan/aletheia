# Cancellation in Aletheia

This document defines how cancellation works in Aletheia across the Python, Go, and C++ bindings. It is the single source of truth for the cancellation contract — siblings of this doc (binding-specific READMEs, API references) must not contradict it; if they do, this doc wins.

The three bindings expose cancellation through different language-native primitives — `asyncio.CancelledError` and generator `.close()` in Python, `context.Context` in Go, `std::stop_token` in C++ — but the *behavior* a caller can rely on is identical across the three. The contract below defines that behavior.

---

## 1. The Contract

Aletheia's cancellation contract has two rules. Both are load-bearing; reading one without the other will mislead you.

### 1.1 Rule 1 (hard) — Cancellation is cooperative at FFI boundaries

A request to cancel an in-flight operation will only be honored at the *next* point where Aletheia code is between FFI calls. An FFI call that has already entered the Haskell runtime will run to completion and return its real result; the cancellation takes effect on the *next* call.

This is not a bug or a limitation we plan to remove. It is a structural property of the architecture: Aletheia's verified core compiles to Haskell via the GHC runtime, which is initialized once per process and runs in a single thread. There is no mechanism, in any of the three bindings, to preempt an FFI call that is already executing inside the runtime. Forcing one would mean killing the runtime, which would invalidate every `StreamState` the process holds.

In practice, individual FFI calls are short — `send_frame` is on the order of microseconds — so the cooperative model is rarely visible to callers. The case where it matters is `send_frames(N)` (and the per-frame iter equivalents): the loop checks for cancellation between each per-frame FFI call, but never inside one.

### 1.2 Rule 2 (soft) — Partial work is committed, not rolled back

When cancellation fires mid-batch or mid-stream, the frames Aletheia has already processed remain processed. The caller is told what was committed; they decide whether to recover (resume from the next frame), restart (clear state, start over), or abort (close the client).

There is no transactional rollback. The streaming model itself does not support it: each frame mutates `StreamState` (advances LTL coalgebras, updates signal caches, registers timestamps), and reverting that mutation would require snapshotting and restoring the state on every batch — at significant cost in memory and complexity. More fundamentally, the streaming abstraction is *about* committing frames as they arrive; rolling them back would contradict the semantics callers rely on.

So cancellation is honest about what it is: a "stop processing further frames" signal, not a "pretend you never saw those frames" signal.

### 1.3 Why a unified contract exists

Aletheia's three bindings target three communities (Python data-science, Go infrastructure, C++ systems) that have different cancellation idioms. Without a contract, the easiest path is for each binding to follow only its own idiom — and over time the bindings would diverge on what gets cancelled, what partial work means, and what the caller can do about it.

The unified contract prevents that. Bindings remain idiomatic *in shape* (an asyncio caller does not see Go-style `ctx`; a Go caller does not see Python-style `async`), but they are identical *in observable behavior*: the same operations are cancellable, the same partial-work guarantees hold, the same caller responsibilities apply. A team writing a Go service that calls Aletheia and a Python data-science notebook that also calls Aletheia can rely on the cancellation behavior matching across the two.

This is the scope discipline:

| Layer | Per-binding | Contract-bound |
|---|---|---|
| Cancellation primitive | Yes — each binding uses its native primitive | — |
| API spelling | Yes — `await`, `ctx`, `std::stop_token` differ | — |
| Cancellable operation set | Per-binding, scoped by *where the language's native primitive applies*. Python sync `AletheiaClient`: none (no native sync-method cancellation). Python async, Go, C++: every operation method. | — |
| Partial-work semantics on cancellable ops | — | Yes — commit-prefix, no rollback |
| Behavior on in-flight FFI for cancellable ops | — | Yes — cooperative at boundaries |
| Caller's recovery options | — | Yes — same surface for resume / restart / abort |

---

## 2. Per-Binding Mechanics

Each binding implements the contract above using its language's native cancellation primitive. The shapes differ; the semantics do not.

### 2.1 Python

Python provides cancellation through two distinct primitives — `asyncio.CancelledError` for async code and generator `.close()` for sync iterators — and Aletheia exposes both through two distinct client classes.

**`aletheia.AletheiaClient`** is the synchronous client. Its individual methods (`send_frame`, `send_frames`, `start_stream`, etc.) are *uncancellable* by design: Python has no native way to cancel a sync method mid-call without process-level signals or thread killing, both of which would break the FFI semantics. The one cancellable surface on the sync client is `send_frames_iter`, where cancellation is observed at frame boundaries (the specific cancellation mechanism — generator `.close()`, `StopIteration`, an explicit cancel flag — is implementation-defined and not part of the contract).

**`aletheia.asyncio.AletheiaClient`** is the asynchronous mirror. It exposes the same set of methods as the sync client, each as `async def`, implemented as `asyncio.to_thread` wrappers around the sync FFI call. Cancellation works through the standard `asyncio.CancelledError` mechanism: cancelling the awaiting task raises `CancelledError` at the next `await` point. For batch and iter operations, that next `await` is between frames, so cancellation fires at frame boundaries.

The two clients share the same underlying `StablePtr` to the Agda `StreamState`, so they cannot be used together on the same client instance — a process picks sync OR async per client. This mirrors the `httpx.Client` / `httpx.AsyncClient` and `redis.Redis` / `redis.asyncio.Redis` patterns that Python users already know.

### 2.2 Go

Go's cancellation idiom is `context.Context`, and Aletheia threads it through every operation method on the `Client`. The convention follows the standard library: `ctx context.Context` is the first parameter of every method that does work.

```go
func (c *Client) SendFrame(ctx context.Context,
                            ts Timestamp, id CanID, dlc DLC, data FramePayload,
                          ) (FrameResponse, error)
```

Two methods deliberately *do not* take ctx: `Close()` (teardown is best-effort, idempotent, double-close safe — matches `db.Close()`) and `NewClient(...)` (construction is sync CGO + RTS initialization with no I/O — matches `sql.Open(...)`).

Behavior on in-flight FFI follows the `database/sql` / `os/exec` pattern: if `ctx` is already cancelled when the method is called, it returns `ctx.Err()` immediately without making the FFI call. If `ctx` fires *during* an in-flight FFI call, the call runs to completion and returns its real result with `nil` error — the cancellation takes effect on the *next* call.

Concurrent goroutines calling methods on the same `Client` are serialized through a ctx-aware lock. (The implementation replaces `sync.Mutex` with a 1-deep `chan struct{}` semaphore so that a goroutine waiting on the lock can be cancelled by ctx without ever acquiring it.) This means: cancelling a goroutine that is blocked waiting for another goroutine's FFI call to finish takes effect immediately, not after the in-flight call returns.

Errors from cancellation are wrapped with caller context: `fmt.Errorf("send_frame: %w", ctx.Err())`. The `%w` verb preserves `errors.Is(err, context.Canceled)` checks for callers that care about the underlying error class.

### 2.3 C++

C++'s cancellation idiom is `std::stop_token` (paired with `std::stop_source` and, when threading is in play, `std::jthread`). Aletheia threads `std::stop_token` through every operation method on `AletheiaClient`, as the first parameter:

```cpp
auto send_frame(std::stop_token stop,
                Timestamp ts, CanId id, Dlc dlc,
                std::span<const std::byte> data) -> Result<FrameResponse>;
```

Callers who do not care about cancellation pass a default-constructed `std::stop_token{}`, which never reports `stop_requested()` — equivalent to Go's `context.Background()`.

Two surfaces deliberately do *not* take `std::stop_token`: the destructor `~AletheiaClient()` (destructors are noexcept-by-convention; teardown is best-effort) and the factory `make_ffi_backend(path, rts_cores)` (construction is sync CGO + RTS initialization).

Behavior on in-flight FFI mirrors Go's: pre-FFI check at function entry, post-FFI honor. If the token already reports stop_requested at the call site, the method returns `std::unexpected{cancellation_error}` without making the FFI call. If the token fires during an in-flight FFI call, the call runs to completion and returns its real `Result<T>`; the next call fails fast.

Cancellation surfaces in the existing error type as a new `ErrorKind::Cancellation` value alongside the existing `ErrorKind` variants (`Protocol`, `Validation`, `State`, `Ffi`, `BinaryUnsupported`). Callers do `if (err.kind() == ErrorKind::Cancellation) { … }` to recognize cancellation.

Unlike the Go binding, the C++ Client is single-client-per-thread by design — there is no shared-state-across-threads concern, so no semaphore or ctx-aware lock primitive is needed.

---

## 3. Partial-Work Semantics: Commit-Prefix-and-Report

When cancellation fires mid-batch or mid-stream, the contract guarantees: every frame Aletheia *acknowledged* (returned an `Ack` or `Violation` response for) is committed and visible in subsequent operations on the same client. No frame is silently re-processed; no frame is silently dropped.

The shape of the report differs by binding, but the substance is identical: the caller knows how many frames were committed, where the cancellation happened, and what (if any) per-frame results came back before the cancellation took effect.

### 3.1 Python

For batch ops: `send_frames(...)` returns the list of per-frame responses for the committed prefix; cancellation surfaces as `BatchError` (an exception) with a `partial_results` attribute carrying the prefix and a `frame_index` pointing at the first uncommitted frame.

For iter ops: `send_frames_iter(...)` yields per-frame `FrameResult` objects up to the cancellation point; cancellation fires at a frame boundary, and the committed prefix is durable. The behavior of the source iterable at the cancellation boundary (whether the not-yet-sent frame at the head of the source is consumed by the iter or stays in the source) is implementation-defined and not part of the contract; if your recovery strategy depends on resuming the source iterable, code defensively (e.g., wrap the source in a peekable / pushback adapter). The async variant on `aletheia.asyncio.AletheiaClient` behaves identically; the cancellation mechanism is `asyncio.CancelledError` raised on the awaiting task.

### 3.2 Go

For batch ops: `SendFrames(ctx, frames)` returns `(committedResponses, ctx.Err())` — the `[]FrameResponse` slice contains the responses for the committed prefix; the error is the wrapped `ctx.Err()`. The length of the slice is the committed count.

For single-call ops (`SendFrame`, `SendError`, etc.): there is no batch-level partial work; either the call committed (returns its real result) or it didn't (returns `ctx.Err()` without side effect).

### 3.3 C++

For batch ops: `send_frames(stop, frames)` returns `BatchResult` with the existing `responses: std::vector<FrameResponse>` field carrying the committed prefix and the `error: std::optional<AletheiaError>` field set to `ErrorKind::Cancellation`. The size of `responses` is the committed count.

For single-call ops: same as Go — either the call committed or it didn't.

### 3.4 Caller responsibility on cancellation

The contract delivers what was committed; the caller decides what to do next. Three patterns the contract supports cleanly:

- **Resume**: re-call the cancelled batch operation with the *uncommitted suffix* of the input. The streaming state is consistent with the committed prefix, so the resumed call picks up where the previous left off.
- **Restart**: call `end_stream()` to clear LTL state, then `start_stream()` to begin a fresh trace. Cancellation does not corrupt state, so restart is always safe.
- **Abort**: call `Close()` / `close()` / let the destructor run. The committed work is durable in any external sink the caller wired up; the in-process state is discarded.

---

## 4. Examples

Each example below is a realistic small scenario showing how a caller cancels work in one binding. The contract guarantees that equivalent code in another binding has equivalent observable behavior.

### 4.1 Python — live bus monitoring with `asyncio.timeout`

A monitoring task watches a CAN bus for property violations and gives up if no violation is detected within a timeout window.

```python
import asyncio
from aletheia.asyncio import AletheiaClient

async def watch_for_violation(dbc_path: str, timeout_s: float) -> bool:
    """Return True if a property violation occurs within `timeout_s`, else False."""
    async with AletheiaClient(dbc=dbc_path, checks=load_checks()) as client:
        await client.start_stream()
        try:
            async with asyncio.timeout(timeout_s):
                async for result in client.send_frames_iter(live_bus_frames()):
                    if result.violation is not None:
                        # Violation found — exit early; the timeout context unwinds cleanly.
                        return True
                return False
        except TimeoutError:
            # asyncio.timeout converts the deadline to TimeoutError on the awaiter.
            # The contract guarantees: every frame that came back through the iter
            # before the timeout is committed; the next frame the live bus produces
            # was NOT pulled (still in the source iter) and will not be silently
            # missed if the caller resumes streaming.
            return False
        finally:
            await client.end_stream()
```

What the contract guarantees here:

- The `asyncio.timeout` deadline raises `CancelledError` at the next `await` boundary inside the `async for`. That boundary is between frames (`send_frames_iter` does not buffer; it pulls and yields one frame at a time).
- The most recent `send_frame` FFI call — if one was in flight when the timeout fired — runs to completion. Its result was already yielded to the `async for` loop body, and the loop body decides whether to look at it before unwinding.
- Every frame yielded through the loop body before the timeout fired is committed and durable in the client's `StreamState`.

What the contract does *not* guarantee here: whether the next frame in `live_bus_frames()` was already consumed from the source at the cancellation boundary. If you need to resume watching from exactly where this loop left off, wrap `live_bus_frames()` in a peekable adapter or apply a per-frame ack on the producer side.

### 4.2 Go — batch send under `context.WithDeadline`

A pipeline that processes a finite batch of frames and gives up on the *batch* if it doesn't complete within a deadline.

```go
import (
    "context"
    "errors"
    "fmt"
    "time"

    "github.com/aletheia/go/aletheia"
)

func processBatch(ctx context.Context, client *aletheia.Client,
                  frames []aletheia.Frame, deadline time.Duration,
                 ) (committed int, err error) {
    bctx, cancel := context.WithTimeout(ctx, deadline)
    defer cancel()

    responses, err := client.SendFrames(bctx, frames)
    committed = len(responses)

    if errors.Is(err, context.DeadlineExceeded) {
        // The contract guarantees: `responses` contains the per-frame outcomes
        // for the first `committed` frames in `frames`. The Aletheia state
        // reflects exactly those frames having been processed. The remaining
        // frames `frames[committed:]` were NOT sent to the FFI.
        return committed, fmt.Errorf("batch deadline exceeded after %d/%d frames: %w",
                                      committed, len(frames), err)
    }
    if err != nil {
        // Non-cancellation error (e.g., non-monotonic timestamp). Same partial-
        // commit semantics: `committed` frames are durable.
        return committed, err
    }
    return committed, nil
}
```

What the contract guarantees here:

- The `bctx` deadline fires at the boundary between two `sendFrameLocked` calls inside `SendFrames`'s loop. The FFI call for the most recent frame — if one was in flight — runs to completion and its response is appended to the returned slice.
- The lock acquired by `SendFrames` is the channel-based semaphore, so even if another goroutine were holding it, the deadline would still fire on the waiting goroutine without it acquiring the lock.
- The caller can call `processBatch` again with `frames[committed:]` to resume — the `Client` state is consistent with the committed prefix.

### 4.3 C++ — streaming session via `std::jthread` + `stop_token`

A worker thread that streams frames from a producer queue, cancellable from outside via the `std::jthread` interface.

```cpp
#include <stop_token>
#include <thread>
#include <queue>

#include "aletheia/client.hpp"

void streaming_worker(std::stop_token stop,
                      aletheia::AletheiaClient& client,
                      FrameProducer& producer) {
    auto start_result = client.start_stream(stop, properties_path);
    if (!start_result) { handle_error(start_result.error()); return; }

    std::size_t committed = 0;
    while (!stop.stop_requested()) {
        auto frame = producer.next(stop);  // blocks until a frame or stop
        if (!frame) break;                 // producer signalled stop

        auto result = client.send_frame(stop, frame->ts, frame->id,
                                        frame->dlc, frame->data);

        if (!result) {
            const auto& err = result.error();
            if (err.kind() == aletheia::ErrorKind::Cancellation) {
                // Contract: the call did NOT execute the FFI (pre-FFI check
                // tripped on stop_requested). `committed` is accurate.
                break;
            }
            // Real error — handle and exit (or continue, depending on policy).
            handle_error(err);
            break;
        }
        ++committed;
    }

    auto end_result = client.end_stream(stop);  // best-effort if cancelled mid-batch
    log_committed_count(committed);
}

// Caller side:
std::jthread worker(streaming_worker, std::ref(client), std::ref(producer));
// ...later, to cancel:
worker.request_stop();    // sets the stop_token; thread cleans up at next checkpoint
worker.join();
```

What the contract guarantees here:

- `worker.request_stop()` flips the `stop_token` to `stop_requested`. The next `client.send_frame(stop, ...)` invocation sees the request at its pre-FFI check and returns `ErrorKind::Cancellation` without making the FFI call.
- A `send_frame` that was already in flight when `request_stop` was called runs to completion and returns its real `Result<FrameResponse>`. The `committed` counter advances for that frame.
- `end_stream(stop)` is the teardown call. If it sees stop_requested at its own pre-FFI check, it returns the same cancellation error — but the streaming state is left in a consistent terminal position either way (the caller can construct a new client to resume from a fresh state).

---

## 5. Edge Cases

### 5.1 Construction and teardown are not cancellable

`AletheiaClient(...)` (Python), `NewClient(...)` (Go), and `make_ffi_backend(...)` (C++) take no cancellation primitive. Construction is synchronous CGO + GHC RTS initialization — there is no I/O to wait on, so cancellation has no meaningful effect.

Wrapping construction in a language-native timeout (`asyncio.wait_for(asyncio.to_thread(AletheiaClient, …), timeout=…)`, `context.WithTimeout` around a goroutine that calls `NewClient`, etc.) does *not* cancel the underlying CGO call — it only stops the caller from *waiting* on the result. The constructor thread or goroutine continues running until `hs_init` and the FFI library load complete. Treat construction as a fixed-cost operation; if you need a hard upper bound on its wallclock time, isolate it in a subprocess that you can SIGKILL.

`close()` / `Close()` / `~AletheiaClient()` similarly take no cancellation primitive. Teardown is best-effort, idempotent, and double-close safe in all three bindings; it always runs to completion. A teardown that fails (e.g., the FFI returns an error during state finalization) reports the failure but does not surface a cancellation case.

### 5.2 Mid-batch error vs cancellation

A batch operation can stop for two reasons: a real error (e.g., non-monotonic timestamp) or a cancellation. If both happen — e.g., an error fires on frame 17 of 100, and the caller had already cancelled the context at frame 50 — the *error* wins. The batch reports the error with the committed prefix `[0..16]`; the cancellation never gets a chance to fire because the loop terminated first.

This is intentional: errors are primary signals about data integrity, and burying them under a cancellation report would make debugging harder. If the caller wants to distinguish "cancelled while processing" from "errored", they check the returned error (or exception type in Python) — cancellation produces `ctx.Err()` / `CancelledError` / `ErrorKind::Cancellation`; errors produce binding-specific error types.

### 5.3 Concurrent cancellation in Go

Go's `Client` is goroutine-safe via the channel-based ctx-aware lock. This produces a behavior worth highlighting: a goroutine cancelled while *waiting* for the lock returns `ctx.Err()` immediately, without ever acquiring the lock or reaching the FFI. This is structurally cleaner than `sync.Mutex.Lock()` would be — `sync.Mutex` has no native ctx-aware variant and would force the waiter to acquire the lock, then return `ctx.Err()` only at the post-lock check.

The Python and C++ bindings do not have this consideration: Python's `AsyncAletheiaClient` is not concurrent-safe across asyncio tasks (each task should hold its own client instance, the same as the sync client), and C++ is single-client-per-thread by design.

### 5.4 What "committed" means for Aletheia state

When a frame is committed, three categories of state are updated:

1. **LTL coalgebras** — every property's incremental coalgebra advances by one step.
2. **Signal caches** — last-observed values for each signal in the frame are recorded.
3. **Timestamp registry** — the last-frame-timestamp advances (this is what enforces monotonicity on subsequent frames).

A cancelled batch leaves all three categories in the state they reached at the committed prefix. Resuming the batch with the uncommitted suffix advances them further; restarting with `end_stream()` + `start_stream()` resets them.

### 5.5 What cancellation does *not* do

It does not invalidate any external state the caller has built up alongside Aletheia (e.g., a database of violations the caller persisted from earlier `Violation` responses). It does not signal anything to the CAN bus — Aletheia is read-only with respect to the bus; nothing is sent. It does not affect other client instances in the same process — each `AletheiaClient` has its own `StablePtr` and is independent.

---

## 6. References

- `docs/architecture/DESIGN.md` — Aletheia's three-layer architecture (the GHC RTS constraint that drives Rule 1 lives there).
- `docs/architecture/PROTOCOL.md` — JSON command / binary frame protocols. Cancellation is *not* part of the wire protocol; it is a binding-side concern.
- `docs/FEATURE_MATRIX.yaml` — cross-binding capability matrix. Rows touched by this contract: `lazy_frame_iter` (Python-only by language constraint), `cancellation` (per-binding mechanic), and the operation rows that gain a cancellation primitive (Python `AsyncAletheiaClient`, Go `ctx`, C++ `std::stop_token`).

---

## 7. Versioning

This contract is stable. Changes to the contract — adding cancellable operations, changing partial-work semantics, adding new bindings — must update this document and the corresponding `FEATURE_MATRIX.yaml` rows in the same change. Drift between this document and the bindings is a defect; report it as a bug.

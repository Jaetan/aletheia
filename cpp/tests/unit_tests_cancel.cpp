// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Cancellation regression tests for AletheiaClient's std::stop_token surface.
// Mirrors the Go binding's cancel_test.go semantics:
//   - pre-FFI guard with already-cancelled stop_source rejects without FFI;
//   - commit-prefix-and-report on mid-batch cancellation (CANCELLATION.md §3.3);
//   - in-flight FFI runs to completion when stop fires mid-call (§1.1).
//
// C++ has no analog of Go's "cancel-while-waiting-on-lock" scenario: the
// AletheiaClient is single-client-per-thread by design (no shared lock to
// queue on), so cancellation is observed only at method-entry checks.

#include <aletheia/aletheia.hpp>

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <functional>
#include <memory>
#include <optional>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <thread>
#include <utility>
#include <vector>

namespace {

using namespace aletheia;

// Shared base for the cancellation-test doubles. The binary streaming/event
// endpoints are never exercised by these tests (they drive process() /
// set_properties / send_frame), so the base satisfies the mandatory IBackend
// streaming surface by routing every endpoint through process().
// Subclasses implement init/close/process with the behaviour under test.
class StubStreamingBackend : public IBackend {
public:
    auto send_frame_binary(const BackendState& state, Timestamp /*ts*/, const CanId& /*id*/,
                           Dlc /*dlc*/, std::span<const std::byte> /*data*/,
                           std::optional<bool> /*brs*/, std::optional<bool> /*esi*/)
        -> std::string override {
        return process(state, "");
    }
    auto send_error_binary(const BackendState& state, Timestamp /*ts*/) -> std::string override {
        return process(state, "");
    }
    auto send_remote_binary(const BackendState& state, Timestamp /*ts*/, const CanId& /*id*/)
        -> std::string override {
        return process(state, "");
    }
    auto start_stream_binary(const BackendState& state) -> std::string override {
        return process(state, "");
    }
    auto end_stream_binary(const BackendState& state) -> std::string override {
        return process(state, "");
    }
    auto format_dbc_binary(const BackendState& state) -> std::string override {
        return process(state, "");
    }
    auto extract_signals_binary(const BackendState& state, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/) -> std::string override {
        return process(state, "");
    }

protected:
    // Every stub below hands out a static sentinel, so there is nothing to
    // release and one definition serves them all.
    void close(void* /*state*/) override {}
};

// CancelTriggerBackend deterministically fires the supplied stop_source
// callback on the Nth process() call so tests can force a mid-batch
// cancellation without sleeping. Anything before N runs to completion;
// anything after sees stop_requested at the next pre-FFI guard.
class CancelTriggerBackend : public StubStreamingBackend {
    static inline char sentinel = 0;
    std::size_t calls_ = 0;
    std::size_t cancel_after_ = 0;
    std::stop_source* source_ = nullptr;

public:
    CancelTriggerBackend(std::size_t cancel_after, std::stop_source* source)
        : cancel_after_(cancel_after)
        , source_(source) {}

    [[nodiscard]] auto call_count() const -> std::size_t { return calls_; }

    auto init() -> BackendState override { return BackendState{*this, &sentinel}; }

    auto process(const BackendState& /*state*/, std::string_view /*input*/)
        -> std::string override {
        ++calls_;
        if (calls_ == cancel_after_ && source_ != nullptr)
            source_->request_stop();
        return R"({"status":"ack"})";
    }
};

// HoldingBackend simulates an in-flight FFI call. process() signals the
// test that it has entered the FFI (entered_), then blocks until the test
// releases it (proceed_). This is a rendezvous — fully deterministic, no
// sleeps or polling — mirroring Go's gateBackend (entered/release channels)
// and Python's gated_backend (started/proceed events). Two std::atomic_flag
// give idempotent set/wait (like a threading.Event): set/notify and wait are
// safe to call repeatedly, so even a set_properties that issued multiple
// process() calls could never violate a semaphore's release-past-max
// precondition. The release/acquire memory ordering establishes happens-before,
// so the main thread reading call_count() after wait_until_entered() is race-free.
class HoldingBackend : public StubStreamingBackend {
    static inline char sentinel = 0;
    std::size_t calls_ = 0;
    std::atomic_flag entered_; // set when process() enters the FFI
    std::atomic_flag proceed_; // set by the test to release the in-flight call

public:
    [[nodiscard]] auto call_count() const -> std::size_t { return calls_; }

    auto init() -> BackendState override { return BackendState{*this, &sentinel}; }

    // Blocks until process() has entered the FFI (deterministic rendezvous).
    void wait_until_entered() { entered_.wait(false, std::memory_order_acquire); }
    // Unblocks the in-flight process() call.
    void release() {
        proceed_.test_and_set(std::memory_order_release);
        proceed_.notify_one();
    }

    auto process(const BackendState& /*state*/, std::string_view /*input*/)
        -> std::string override {
        ++calls_;
        entered_.test_and_set(std::memory_order_release);
        entered_.notify_one();
        proceed_.wait(false, std::memory_order_acquire);
        return R"({"status":"success"})";
    }
};

} // namespace

TEST_CASE("Client cancellation: pre-FFI guard rejects already-cancelled stop_token",
          "[cancellation]") {
    auto backend_owned = std::make_unique<CancelTriggerBackend>(0, nullptr);
    auto const* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    const std::stop_source source;
    source.request_stop(); // cancel BEFORE the call

    auto result = client.set_properties(source.get_token(), std::span<const LtlFormula>{});
    REQUIRE_FALSE(result.has_value());
    REQUIRE(result.error().kind() == ErrorKind::Cancellation);
    REQUIRE(std::string_view{result.error().message()}.contains("set_properties"));
    REQUIRE(backend->call_count() == 0); // FFI never reached
}

TEST_CASE("Client cancellation: mid-batch commit-prefix-and-report", "[cancellation]") {
    constexpr std::size_t total = 10;
    constexpr std::size_t cancel_after = 3;

    std::stop_source source;
    auto backend_owned = std::make_unique<CancelTriggerBackend>(cancel_after, &source);
    auto const* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    std::vector<Frame> frames;
    frames.reserve(total);
    auto sid = StandardId::create(0x123).value();
    auto const dlc = Dlc::create(8).value();
    std::vector<std::byte> payload(8, std::byte{0});
    for (std::size_t i = 0; i < total; ++i) {
        frames.push_back(Frame{
            .timestamp = Timestamp{static_cast<std::int64_t>((i + 1) * 1000)},
            .id = CanId{sid},
            .dlc = dlc,
            .data = FramePayload(payload.begin(), payload.end()),
        });
    }

    auto batch = client.send_frames(source.get_token(), frames);
    REQUIRE(batch.error.has_value());
    REQUIRE(batch.error->kind() == ErrorKind::Cancellation);
    REQUIRE(batch.responses.size() == cancel_after);
    REQUIRE(backend->call_count() == cancel_after);
}

TEST_CASE("Client cancellation: in-flight FFI runs to completion", "[cancellation]") {
    auto backend_owned = std::make_unique<HoldingBackend>();
    auto* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    const std::stop_source cancel_source;
    auto cancel_token = cancel_source.get_token();

    // Run set_properties on a worker thread; HoldingBackend blocks inside
    // process() until the test releases it. While it's blocked, fire
    // cancel_source — the in-flight call must NOT abort. The worker's outcome
    // is captured into worker_ok and asserted by the MAIN thread after join
    // (Catch2 macros are not thread-safe, so we never assert inside the worker).
    bool worker_ok = false;
    std::thread worker([&] {
        auto const r = client.set_properties(cancel_token, std::span<const LtlFormula>{});
        worker_ok = r.has_value();
    });

    // RAII safety net for the window between spawning `worker` and joining it
    // below: if any REQUIRE here throws while the worker is parked inside
    // HoldingBackend::process() (blocked on proceed_), the worker stays joinable
    // and `worker`'s std::thread destructor would call std::terminate during the
    // unwind. This guard releases the backend (so process() returns) and joins the
    // worker before that destructor runs, turning an assertion failure into a fast,
    // clean failure instead of a terminate. A shared_ptr<void> holding a null
    // pointer with a deleter is a dependency-free scope guard whose deleter runs
    // on scope exit, an exception unwind included. Declared after `worker` so it
    // destructs first; on the happy path the explicit release and join below run
    // first and leave it a no-op, release being idempotent and join skipped once
    // the worker has been joined.
    auto const worker_guard = std::shared_ptr<void>(nullptr, [backend, &worker](void*) {
        backend->release();
        if (worker.joinable())
            worker.join();
    });

    // Deterministically wait until process() has entered the FFI. The entered_
    // flag's release and acquire establish happens-before, so reading
    // call_count() here is race-free.
    backend->wait_until_entered();
    REQUIRE(backend->call_count() == 1);

    // Fire cancellation while the FFI is in flight, then release it. Releasing
    // through the proceed_ flag is sufficient: the cancel cannot have aborted
    // an already-entered call, and the assertion after the join proves the
    // call returned success.
    cancel_source.request_stop();
    backend->release();
    worker.join();
    REQUIRE(worker_ok); // in-flight call succeeded despite mid-flight cancel

    // Subsequent call honors the now-cancelled token (sticky).
    auto r2 = client.set_properties(cancel_token, std::span<const LtlFormula>{});
    REQUIRE_FALSE(r2.has_value());
    REQUIRE(r2.error().kind() == ErrorKind::Cancellation);
}

// Every method that takes a stop_token has its own pre-FFI guard, and each
// guard is observable only through its own method: a guard that never fires
// lets the call reach the backend, which the counter below sees, or fall
// through to a later refusal (build_frame with no DBC loaded answers State,
// not Cancellation). One row per method keeps every guard on the suite.
TEST_CASE("Client cancellation: every method's pre-FFI guard rejects a cancelled stop_token",
          "[cancellation]") {
    auto backend_owned = std::make_unique<CancelTriggerBackend>(0, nullptr);
    auto const* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    const std::stop_source source;
    source.request_stop();
    auto const token = source.get_token();

    auto const id = CanId{StandardId::create(0x123).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload payload(8, std::byte{0});
    const std::vector<Frame> frames{
        Frame{.timestamp = Timestamp{1000}, .id = id, .dlc = dlc, .data = payload}};

    struct Row {
        std::string_view method;
        std::function<std::optional<AletheiaError>()> call;
    };
    auto const error_of = [](auto const& r) -> std::optional<AletheiaError> {
        if (r.has_value())
            return std::nullopt;
        return r.error();
    };
    const std::vector<Row> rows{
        {.method = "parse_dbc",
         .call = [&] { return error_of(client.parse_dbc(token, DbcDefinition{})); }},
        {.method = "parse_dbc_text",
         .call = [&] { return error_of(client.parse_dbc_text(token, "VERSION \"\"")); }},
        {.method = "validate_dbc",
         .call = [&] { return error_of(client.validate_dbc(token, DbcDefinition{})); }},
        {.method = "format_dbc", .call = [&] { return error_of(client.format_dbc(token)); }},
        {.method = "format_dbc_text",
         .call = [&] { return error_of(client.format_dbc_text(token, DbcDefinition{})); }},
        {.method = "extract_signals",
         .call = [&] { return error_of(client.extract_signals(token, id, dlc, payload)); }},
        {.method = "build_frame",
         .call =
             [&] {
                 return error_of(
                     client.build_frame(token, id, dlc, std::span<const SignalValue>{}));
             }},
        {.method = "update_frame",
         .call =
             [&] {
                 return error_of(
                     client.update_frame(token, id, dlc, payload, std::span<const SignalValue>{}));
             }},
        {.method = "set_properties",
         .call =
             [&] { return error_of(client.set_properties(token, std::span<const LtlFormula>{})); }},
        {.method = "add_checks", .call = [&] { return error_of(client.add_checks(token, {})); }},
        {.method = "start_stream", .call = [&] { return error_of(client.start_stream(token)); }},
        {.method = "send_frame",
         .call =
             [&] { return error_of(client.send_frame(token, Timestamp{1000}, id, dlc, payload)); }},
        {.method = "send_frames",
         .call =
             [&] {
                 auto const batch = client.send_frames(token, frames);
                 return batch.error;
             }},
        {.method = "send_error",
         .call = [&] { return error_of(client.send_error(token, Timestamp{1000})); }},
        {.method = "send_remote",
         .call = [&] { return error_of(client.send_remote(token, Timestamp{1000}, id)); }},
        {.method = "end_stream", .call = [&] { return error_of(client.end_stream(token)); }},
    };
    for (auto const& row : rows) {
        INFO(row.method);
        auto const err = row.call();
        REQUIRE(err.has_value());
        CHECK(err->kind() == ErrorKind::Cancellation);
        CHECK(std::string_view{err->message()}.contains(row.method));
        CHECK(backend->call_count() == 0);
    }
}

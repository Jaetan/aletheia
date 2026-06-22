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

#include <catch2/catch_test_macros.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <memory>
#include <semaphore>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

using namespace aletheia;

// Shared base for the cancellation-test doubles. The binary streaming/event
// endpoints are never exercised by these tests (they drive process() /
// set_properties / send_frame), so the base satisfies the now-mandatory
// IBackend streaming surface by routing every endpoint through process().
// Subclasses implement init/close/process with the behaviour under test.
class StubStreamingBackend : public IBackend {
public:
    auto send_frame_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/, Dlc /*dlc*/,
                           std::span<const std::byte> /*data*/, std::optional<bool> /*brs*/,
                           std::optional<bool> /*esi*/) -> std::string override {
        return process(state, "");
    }
    auto send_error_binary(void* state, Timestamp /*ts*/) -> std::string override {
        return process(state, "");
    }
    auto send_remote_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/)
        -> std::string override {
        return process(state, "");
    }
    auto start_stream_binary(void* state) -> std::string override { return process(state, ""); }
    auto end_stream_binary(void* state) -> std::string override { return process(state, ""); }
    auto format_dbc_binary(void* state) -> std::string override { return process(state, ""); }
    auto extract_signals_binary(void* state, const CanId& /*id*/, Dlc /*dlc*/,
                                std::span<const std::byte> /*data*/) -> std::string override {
        return process(state, "");
    }
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

    auto init() -> void* override { return &sentinel; }
    void close(void* /*state*/) override {}

    auto process(void* /*state*/, std::string_view /*input*/) -> std::string override {
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
// and Python's gated_backend (started/proceed events). The release/acquire
// pair establishes happens-before, so the main thread reading call_count()
// after wait_until_entered() is race-free.
class HoldingBackend : public StubStreamingBackend {
    static inline char sentinel = 0;
    std::size_t calls_ = 0;
    std::binary_semaphore entered_{0}; // released when process() enters
    std::binary_semaphore proceed_{0}; // acquired before process() returns

public:
    [[nodiscard]] auto call_count() const -> std::size_t { return calls_; }

    auto init() -> void* override { return &sentinel; }
    void close(void* /*state*/) override {}

    // Blocks until process() has entered the FFI (deterministic rendezvous).
    void wait_until_entered() { entered_.acquire(); }
    // Unblocks the in-flight process() call.
    void release() { proceed_.release(); }

    auto process(void* /*state*/, std::string_view /*input*/) -> std::string override {
        ++calls_;
        entered_.release();
        proceed_.acquire();
        return R"({"status":"success"})";
    }
};

} // namespace

#include <thread>

TEST_CASE("Client cancellation: pre-FFI guard rejects already-cancelled stop_token",
          "[cancellation]") {
    auto backend_owned = std::make_unique<CancelTriggerBackend>(0, nullptr);
    auto* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    std::stop_source source;
    source.request_stop(); // cancel BEFORE the call

    auto result = client.set_properties(source.get_token(), std::span<const LtlFormula>{});
    REQUIRE_FALSE(result.has_value());
    REQUIRE(result.error().kind() == ErrorKind::Cancellation);
    REQUIRE(std::string_view{result.error().message()}.find("set_properties") !=
            std::string_view::npos);
    REQUIRE(backend->call_count() == 0); // FFI never reached
}

TEST_CASE("Client cancellation: mid-batch commit-prefix-and-report", "[cancellation]") {
    constexpr std::size_t total = 10;
    constexpr std::size_t cancel_after = 3;

    std::stop_source source;
    auto backend_owned = std::make_unique<CancelTriggerBackend>(cancel_after, &source);
    auto* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    std::vector<Frame> frames;
    frames.reserve(total);
    auto sid = StandardId::create(0x123).value();
    auto dlc = Dlc::create(8).value();
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

    std::stop_source cancel_source;
    auto cancel_token = cancel_source.get_token();

    // Run set_properties on a worker thread; HoldingBackend blocks inside
    // process() until the test releases it. While it's blocked, fire
    // cancel_source — the in-flight call must NOT abort. The worker's outcome
    // is captured into worker_ok and asserted by the MAIN thread after join
    // (Catch2 macros are not thread-safe, so we never assert inside the worker).
    bool worker_ok = false;
    std::thread worker([&] {
        auto r = client.set_properties(cancel_token, std::span<const LtlFormula>{});
        worker_ok = r.has_value();
    });

    // Deterministically wait until process() has entered the FFI (replaces the
    // 2s steady_clock deadline poll). The entered_ semaphore release/acquire
    // establishes happens-before, so reading call_count() here is race-free.
    backend->wait_until_entered();
    REQUIRE(backend->call_count() == 1);

    // Fire cancellation while the FFI is in flight, then release the FFI.
    // Releasing via the proceed_ semaphore (replaces the sleep_for(20ms)) is
    // sufficient: the cancel cannot have aborted an already-entered call, and
    // the worker_ok assertion after join proves the call returned success.
    cancel_source.request_stop();
    backend->release();
    worker.join();
    REQUIRE(worker_ok); // in-flight call succeeded despite mid-flight cancel

    // Subsequent call honors the now-cancelled token (sticky).
    auto r2 = client.set_properties(cancel_token, std::span<const LtlFormula>{});
    REQUIRE_FALSE(r2.has_value());
    REQUIRE(r2.error().kind() == ErrorKind::Cancellation);
}

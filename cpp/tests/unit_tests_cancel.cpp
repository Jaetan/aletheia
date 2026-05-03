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
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

using namespace aletheia;

// CancelTriggerBackend deterministically fires the supplied stop_source
// callback on the Nth process() call so tests can force a mid-batch
// cancellation without sleeping. Anything before N runs to completion;
// anything after sees stop_requested at the next pre-FFI guard.
class CancelTriggerBackend : public IBackend {
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

    auto send_frame_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/, Dlc /*dlc*/,
                           std::span<const std::byte> /*data*/) -> std::string override {
        return process(state, "");
    }
};

// HoldingBackend simulates an in-flight FFI call: process() blocks until the
// test releases it via release(). Pairs with TestClient_NoCancelOnInFlightFFI
// to verify the in-flight call runs to completion even after stop fires.
class HoldingBackend : public IBackend {
    static inline char sentinel = 0;
    std::size_t calls_ = 0;
    std::stop_token release_token_;

public:
    explicit HoldingBackend(std::stop_token release_token)
        : release_token_(std::move(release_token)) {}

    [[nodiscard]] auto call_count() const -> std::size_t { return calls_; }

    auto init() -> void* override { return &sentinel; }
    void close(void* /*state*/) override {}

    auto process(void* /*state*/, std::string_view /*input*/) -> std::string override {
        ++calls_;
        // Block until release_token fires. We deliberately use the same
        // primitive (stop_token) the test exercises against the client; the
        // release_token is independent of any client-facing stop_source.
        std::stop_callback cb(release_token_, [] {});
        // Spin-wait via stop_requested() — fine for tests; production code
        // would use std::condition_variable_any with a stop_token.
        while (!release_token_.stop_requested())
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
        return R"({"status":"success"})";
    }

    auto send_frame_binary(void* state, Timestamp /*ts*/, const CanId& /*id*/, Dlc /*dlc*/,
                           std::span<const std::byte> /*data*/) -> std::string override {
        return process(state, "");
    }
};

} // namespace

#include <chrono>
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
    std::stop_source release_source;
    auto backend_owned = std::make_unique<HoldingBackend>(release_source.get_token());
    auto* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));

    std::stop_source cancel_source;
    auto cancel_token = cancel_source.get_token();

    // Run set_properties on a worker thread; HoldingBackend blocks inside
    // process() until release_source fires. While it's blocked, fire
    // cancel_source — the in-flight call must NOT abort.
    std::thread worker([&] {
        auto r = client.set_properties(cancel_token, std::span<const LtlFormula>{});
        // Must succeed: pre-FFI guard saw stop_requested == false at call entry,
        // the FFI call ran to completion, and the result is the real success.
        REQUIRE(r.has_value());
    });

    // Wait until the FFI is entered.
    auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(2);
    while (backend->call_count() == 0 && std::chrono::steady_clock::now() < deadline)
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    REQUIRE(backend->call_count() == 1);

    // Fire cancellation while the FFI is in flight.
    cancel_source.request_stop();
    std::this_thread::sleep_for(
        std::chrono::milliseconds(20)); // give cancellation time to "do nothing"

    // Release the FFI. The worker's call returns a successful result.
    release_source.request_stop();
    worker.join();

    // Subsequent call honors the now-cancelled token (sticky).
    auto r2 = client.set_properties(cancel_token, std::span<const LtlFormula>{});
    REQUIRE_FALSE(r2.has_value());
    REQUIRE(r2.error().kind() == ErrorKind::Cancellation);
}

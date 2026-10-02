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

#include <cstddef>
#include <cstdint>
#include <expected>
#include <functional>
#include <memory>
#include <optional>
#include <ranges>
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
// anything after sees stop_requested at the next pre-FFI guard. The Nth call
// itself is in flight when the stop fires, and still answers `reply`.
class CancelTriggerBackend : public StubStreamingBackend {
    static inline char sentinel = 0;
    std::size_t calls_ = 0;
    std::size_t cancel_after_ = 0;
    std::stop_source* source_ = nullptr;
    std::string_view reply_;

public:
    CancelTriggerBackend(std::size_t cancel_after, std::stop_source* source,
                         std::string_view reply = R"({"status":"ack"})")
        : cancel_after_(cancel_after)
        , source_(source)
        , reply_(reply) {}

    [[nodiscard]] auto call_count() const -> std::size_t { return calls_; }

    auto init() -> BackendState override { return BackendState{*this, &sentinel}; }

    auto process(const BackendState& /*state*/, std::string_view /*input*/)
        -> std::string override {
        ++calls_;
        if (calls_ == cancel_after_ && source_ != nullptr)
            source_->request_stop();
        return std::string{reply_};
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
    for (auto const i : std::views::iota(std::size_t{0}, total)) {
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
    // The stop fires from inside the backend's process(), while the call is in
    // flight: the call must still return its result. Driven from inside the
    // call, as Go's cancel test is, so no thread races it.
    std::stop_source cancel_source;
    auto backend_owned =
        std::make_unique<CancelTriggerBackend>(1, &cancel_source, R"({"status":"success"})");
    auto const* backend = backend_owned.get();
    AletheiaClient client(std::move(backend_owned));
    auto const cancel_token = cancel_source.get_token();

    auto const r1 = client.set_properties(cancel_token, std::span<const LtlFormula>{});
    REQUIRE(r1.has_value()); // in-flight call succeeded despite mid-flight cancel
    REQUIRE(backend->call_count() == 1);
    REQUIRE(cancel_token.stop_requested());

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

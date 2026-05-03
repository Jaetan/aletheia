// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: Logger wiring (stream events, null logger, rts.cores_mismatch).
//
// The rts.cores_mismatch test asserts field-name + integer parity with the Go
// binding (slog.Int("active_cores", ...)) and Python binding (%d formatting):
// all three emit std::int64_t-typed `active_cores` and `requested_cores`.
#include <catch2/catch_test_macros.hpp>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;

TEST_CASE("logger captures streaming events", "[client][log]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // Queue: set_properties, start_stream, send_frame (ack), end_stream (holds)
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "ack"})");
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0}
        ]
    })");

    // Collect log events
    std::vector<std::pair<LogLevel, std::string>> events;
    Logger logger([&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });

    AletheiaClient client(std::move(mock), logger);

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    // Verify event sequence
    REQUIRE(events.size() >= 4);

    // First four are the lifecycle events
    CHECK(events[0].first == LogLevel::Info);
    CHECK(events[0].second == "properties.set");
    CHECK(events[1].first == LogLevel::Info);
    CHECK(events[1].second == "stream.started");
    // frame.processed may be preceded by cache.miss
    bool found_frame = false;
    bool found_ended = false;
    for (const auto& [level, event] : events) {
        if (event == "frame.processed") {
            CHECK(level == LogLevel::Debug);
            found_frame = true;
        }
        if (event == "stream.ended") {
            CHECK(level == LogLevel::Info);
            found_ended = true;
        }
    }
    CHECK(found_frame);
    CHECK(found_ended);
}

TEST_CASE("null logger has zero overhead", "[client][log]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");

    // Default-constructed logger — no callback
    AletheiaClient client(std::move(mock));

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    // Should not crash or produce output
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
}

// Backend subclass that reports a synthetic RTS mismatch so the Client's
// log-emission path can be exercised from the unit tests (no real FFI).
namespace {

class MockBackendWithRtsMismatch : public MockBackend {
public:
    [[nodiscard]] auto rts_mismatch_info() const -> std::optional<std::pair<int, int>> override {
        return std::make_pair(1, 4);
    }
};

} // namespace

TEST_CASE("rts.cores_mismatch logs active/requested core integer fields", "[client][log][rts]") {
    // Capture full LogRecord so field names and integer types are verifiable
    // (std::int64_t branch of LogValue is load-bearing for Go/Python parity).
    struct CapturedField {
        std::string key;
        LogValue value;
    };
    struct CapturedEvent {
        LogLevel level;
        std::string event;
        std::vector<CapturedField> fields;
    };
    std::vector<CapturedEvent> events;

    Logger logger([&](const LogRecord& r) {
        CapturedEvent evt{r.level, std::string{r.event}, {}};
        for (const auto& [k, v] : r.fields)
            evt.fields.push_back(CapturedField{std::string{k}, v});
        events.push_back(std::move(evt));
    });

    auto mock = std::make_unique<MockBackendWithRtsMismatch>();
    AletheiaClient client(std::move(mock), logger);

    REQUIRE_FALSE(events.empty());
    CHECK(events[0].level == LogLevel::Warn);
    CHECK(events[0].event == "rts.cores_mismatch");
    REQUIRE(events[0].fields.size() == 2);
    CHECK(events[0].fields[0].key == "active_cores");
    CHECK(events[0].fields[1].key == "requested_cores");
    // Field values must be int64 (parity with Go's slog.Int and Python's
    // `%d` formatting — both emit integers, not strings).
    REQUIRE(std::holds_alternative<std::int64_t>(events[0].fields[0].value));
    REQUIRE(std::holds_alternative<std::int64_t>(events[0].fields[1].value));
    CHECK(std::get<std::int64_t>(events[0].fields[0].value) == 1);
    CHECK(std::get<std::int64_t>(events[0].fields[1].value) == 4);
}

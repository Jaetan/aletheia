// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: Logger wiring (stream events, null logger, rts.cores_mismatch).
//
// The rts.cores_mismatch test asserts field-name + integer parity with the Go
// binding (slog.Int("active_cores", ...)) and Python binding (%d formatting):
// all three emit std::int64_t-typed `active_cores` and `requested_cores`.
#include <catch2/catch_test_macros.hpp>

#include "test_helpers.hpp"

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <map>
#include <memory>
#include <optional>
#include <ranges>
#include <stop_token>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using aletheia::test::BinExtractMockBackend;
using aletheia::test::make_test_dbc;
using aletheia::test::one_value_at_index_zero;
using aletheia::test::parsed_dbc_response_for;
using aletheia::test::took_json_extraction;

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
    const Logger logger(
        [&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });

    AletheiaClient client(std::move(mock), logger);

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
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
    for (auto const& [level, event] : events) {
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

TEST_CASE("a client with no logger runs every emit site", "[client][log]") {
    // The title claim is what this asserts: a default-constructed logger has no
    // sink, so every emit site the call passes through short-circuits and the
    // call succeeds. Whether that short-circuit costs anything is a question
    // for the benchmarks, not for this case.
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");

    AletheiaClient client(std::move(mock));

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

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

    const Logger logger([&](const LogRecord& r) {
        CapturedEvent evt{.level = r.level, .event = std::string{r.event}, .fields = {}};
        for (auto const& [k, v] : r.fields)
            evt.fields.push_back(CapturedField{.key = std::string{k}, .value = v});
        events.push_back(std::move(evt));
    });

    auto mock = std::make_unique<MockBackendWithRtsMismatch>();
    const AletheiaClient client(std::move(mock), logger);

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

// The fast-path `enabled(LogLevel)` predicate lets hot-path callers
// short-circuit before constructing `initializer_list<LogField>`.
// Three cases guard against `>` vs `>=` direction regressions and silent
// "debug-never-fires" / "debug-always-fires" failures.
TEST_CASE("Logger::enabled() reflects sink + min-level state", "[log][enabled]") {
    SECTION("no sinks → false at every level") {
        const Logger logger;
        CHECK_FALSE(logger.enabled(LogLevel::Debug));
        CHECK_FALSE(logger.enabled(LogLevel::Info));
        CHECK_FALSE(logger.enabled(LogLevel::Warn));
        CHECK_FALSE(logger.enabled(LogLevel::Error));
    }
    SECTION("sink registered, level below min → false") {
        const Logger logger([](const LogRecord&) {}, LogLevel::Warn);
        CHECK_FALSE(logger.enabled(LogLevel::Debug));
        CHECK_FALSE(logger.enabled(LogLevel::Info));
    }
    SECTION("sink registered, level == min → true (boundary)") {
        const Logger logger([](const LogRecord&) {}, LogLevel::Warn);
        CHECK(logger.enabled(LogLevel::Warn));
    }
    SECTION("sink registered, level above min → true") {
        const Logger logger([](const LogRecord&) {}, LogLevel::Warn);
        CHECK(logger.enabled(LogLevel::Error));
    }
    SECTION("default min_level (Debug) accepts all levels with sink") {
        const Logger logger([](const LogRecord&) {});
        CHECK(logger.enabled(LogLevel::Debug));
        CHECK(logger.enabled(LogLevel::Info));
        CHECK(logger.enabled(LogLevel::Warn));
        CHECK(logger.enabled(LogLevel::Error));
    }
}

TEST_CASE("Logger::enabled() mirrors log()'s short-circuit exactly", "[log][enabled]") {
    // If enabled() drifts from log()'s internal check, the outer guard silently
    // becomes wrong (either logs fire when they shouldn't, or vice versa).
    // Cross-check at every level / min_level combination.
    int callback_count = 0;
    auto const bump = [&](const LogRecord&) { ++callback_count; };

    for (auto const min_level :
         {LogLevel::Debug, LogLevel::Info, LogLevel::Warn, LogLevel::Error}) {
        for (auto const call_level :
             {LogLevel::Debug, LogLevel::Info, LogLevel::Warn, LogLevel::Error}) {
            const Logger logger(bump, min_level);
            callback_count = 0;
            auto const en = logger.enabled(call_level);
            logger.log(call_level, "test", {});
            auto const fired = (callback_count > 0);
            CHECK(en == fired);
        }
    }
}

// ===========================================================================
// Event fields: what each event carries, not only that it fires
// ===========================================================================

namespace {

// A captured record with its string fields copied, since a LogRecord's views
// end with the call that produced it.
using OwnedValue = std::variant<std::string, std::int64_t, std::uint64_t, bool>;

struct Event {
    LogLevel level;
    std::string name;
    std::map<std::string, OwnedValue> fields;
};

struct Capture {
    std::vector<Event> events;

    // The Logger copies its sink, and the sink points back here, so a
    // Capture outlives every client its logger is handed to.
    [[nodiscard]] auto logger() -> Logger {
        return Logger([this](const LogRecord& r) {
            Event e{.level = r.level, .name = std::string{r.event}, .fields = {}};
            for (auto const& [k, v] : r.fields)
                e.fields.emplace(std::string{k},
                                 std::visit(
                                     [](auto const& x) -> OwnedValue {
                                         if constexpr (std::is_same_v<std::decay_t<decltype(x)>,
                                                                      std::string_view>)
                                             return std::string{x};
                                         else
                                             return x;
                                     },
                                     v));
            events.push_back(std::move(e));
        });
    }

    [[nodiscard]] auto count(std::string_view name) const -> std::size_t {
        return static_cast<std::size_t>(
            std::ranges::count_if(events, [name](const Event& e) { return e.name == name; }));
    }

    // The one event of that name; a count other than one fails the test here.
    [[nodiscard]] auto only(std::string_view name) const -> const Event& {
        REQUIRE(count(name) == 1);
        return *std::ranges::find_if(events, [name](const Event& e) { return e.name == name; });
    }
};

} // namespace

template<typename T>
static auto field(const Event& e, std::string_view key) -> T {
    return std::get<T>(e.fields.at(std::string{key}));
}

// A client with one property on Speed, its stream open, over the given
// backend and logger: the state every enrichment path starts from.
static auto streaming_client(std::unique_ptr<IBackend> backend, const Logger& logger)
    -> AletheiaClient {
    AletheiaClient client(std::move(backend), logger);
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    return client;
}

namespace {
constexpr std::string_view k_violation = R"({
    "type": "property_batch",
    "results": [{"status": "fails", "type": "property", "property_index": 0,
                 "timestamp": 1000000, "reason": "core"}]
})";
constexpr std::string_view k_satisfaction = R"({
    "type": "property_batch",
    "results": [{"status": "holds", "type": "property", "property_index": 0,
                 "timestamp": 1000000}]
})";
constexpr std::string_view k_extraction = R"({
    "status": "success",
    "values": [{"name": "Speed", "value": 245}],
    "errors": [], "absent": []
})";

} // namespace

TEST_CASE("a logger is true exactly when it has a sink", "[log]") {
    Capture cap;
    CHECK_FALSE(static_cast<bool>(Logger{}));
    CHECK(static_cast<bool>(cap.logger()));
}

TEST_CASE("dbc.parsed carries the message count on both parse paths", "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
    AletheiaClient client(std::move(mock), cap.logger());

    REQUIRE(client.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
    REQUIRE(client.parse_dbc_text(std::stop_token{}, "VERSION \"\"").has_value());
    REQUIRE(cap.count("dbc.parsed") == 2);
    for (auto const& e : cap.events) {
        CHECK(e.level == LogLevel::Info);
        CHECK(field<std::uint64_t>(e, "messages") == 1);
    }
}

TEST_CASE("properties.set carries the property count", "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");
    AletheiaClient client(std::move(mock), cap.logger());

    std::vector<LtlFormula> props;
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"RPM"}, PhysicalValue{Rational{9000, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    auto const& e = cap.only("properties.set");
    CHECK(e.level == LogLevel::Info);
    CHECK(field<std::uint64_t>(e, "count") == 2);
}

TEST_CASE("stream.ended counts the verdicts and warnings, and re-emits uncached atoms",
          "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0, "reason": "r"},
            {"type": "property", "status": "unresolved", "property_index": 1, "reason": "r"},
            {"type": "property", "status": "holds", "property_index": 2},
            {"type": "property", "status": "holds", "property_index": 2}
        ],
        "warnings": [
            {"kind": "uncached_atom", "property_index": 1, "detail": "RPM"},
            {"kind": "other", "property_index": 0, "detail": "not re-emitted"}
        ]
    })");
    AletheiaClient client(std::move(mock), cap.logger());
    std::vector<LtlFormula> props;
    for (auto const* name : {"Speed", "RPM", "Voltage"})
        props.push_back(ltl::always(
            ltl::atomic(ltl::less_than(SignalName{name}, PhysicalValue{Rational{1, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    auto const& ended = cap.only("stream.ended");
    CHECK(ended.level == LogLevel::Info);
    CHECK(field<std::uint64_t>(ended, "numResults") == 4);
    CHECK(field<std::uint64_t>(ended, "numFails") == 1);
    CHECK(field<std::uint64_t>(ended, "numUnresolved") == 1);
    CHECK(field<std::uint64_t>(ended, "numWarnings") == 2);
    auto const& atom = cap.only("endstream.uncached_atom");
    CHECK(atom.level == LogLevel::Warn);
    CHECK(field<std::uint64_t>(atom, "property_index") == 1);
    CHECK(field<std::string>(atom, "detail") == "RPM");
}

TEST_CASE("frame.processed classifies the response and names the frame", "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({"status": "ack"})");
    mock->queue_response(std::string{k_satisfaction});
    mock->queue_response(std::string{k_violation});
    mock->queue_response(std::string{k_extraction});
    auto client = streaming_client(std::move(mock), cap.logger());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    for (std::int64_t ts : {1000, 2000, 3000})
        REQUIRE(client.send_frame(std::stop_token{}, Timestamp{ts}, id, dlc, data).has_value());

    REQUIRE(cap.count("frame.processed") == 3);
    const std::vector<std::string> expected{"ack", "satisfaction", "violation"};
    std::size_t i = 0;
    for (auto const& e : cap.events) {
        if (e.name != "frame.processed")
            continue;
        CHECK(e.level == LogLevel::Debug);
        CHECK(field<std::int64_t>(e, "ts") == static_cast<std::int64_t>((i + 1) * 1000));
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK(field<bool>(e, "extended") == false);
        CHECK(field<std::string>(e, "response") == expected.at(i));
        ++i;
    }
}

TEST_CASE("error and remote events log their timestamp and target", "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({"status": "ack"})");
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock), cap.logger());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    REQUIRE(client.send_error(std::stop_token{}, Timestamp{1000}).has_value());
    REQUIRE(client.send_remote(std::stop_token{}, Timestamp{2000}, id).has_value());

    auto const& err = cap.only("error_event.sent");
    CHECK(err.level == LogLevel::Debug);
    CHECK(field<std::int64_t>(err, "ts") == 1000);
    CHECK(field<std::string>(err, "response") == "ack");
    auto const& rem = cap.only("remote_event.sent");
    CHECK(rem.level == LogLevel::Debug);
    CHECK(field<std::int64_t>(rem, "ts") == 2000);
    CHECK(field<std::uint64_t>(rem, "canId") == 0x100);
    CHECK(field<bool>(rem, "extended") == false);
    CHECK(field<std::string>(rem, "response") == "ack");
}

TEST_CASE("a remote event on an extended identifier logs the extended bit set",
          "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock), cap.logger());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{ExtendedId::create(0x18FEF100).value()};
    REQUIRE(client.send_remote(std::stop_token{}, Timestamp{3000}, id).has_value());

    auto const& rem = cap.only("remote_event.sent");
    CHECK(field<std::uint64_t>(rem, "canId") == 0x18FEF100);
    CHECK(field<bool>(rem, "extended") == true);
}

TEST_CASE("cache.miss then cache.hit name the frame that was extracted", "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(std::string{k_violation});
    mock->queue_response(std::string{k_extraction});
    mock->queue_response(std::string{k_violation});
    auto client = streaming_client(std::move(mock), cap.logger());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, id, dlc, data).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{2000}, id, dlc, data).has_value());

    for (auto const* name : {"cache.miss", "cache.hit"}) {
        auto const& e = cap.only(name);
        CHECK(e.level == LogLevel::Debug);
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK(field<std::uint64_t>(e, "dlc") == 8);
    }
}

TEST_CASE("cache.full fires once, on the first frame past the cache's capacity",
          "[client][log][fields][cache]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    constexpr unsigned frames = 257;
    for ([[maybe_unused]] auto const frame : std::views::repeat(0, frames)) {
        mock->queue_response(std::string{k_violation});
        mock->queue_response(std::string{k_extraction});
    }
    auto client = streaming_client(std::move(mock), cap.logger());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(0U, frames)) {
        FramePayload data(8, std::byte{0});
        data[0] = static_cast<std::byte>(i & 0xFFU);
        data[1] = static_cast<std::byte>((i >> 8U) & 0xFFU);
        auto const r = client.send_frame(std::stop_token{}, Timestamp{static_cast<std::int64_t>(i)},
                                         id, dlc, data);
        REQUIRE(r.has_value());
        REQUIRE(std::get<PropertyBatch>(*r).first_violation()->enrichment.has_value());
        if (i + 1 < frames)
            CHECK(cap.count("cache.full") == 0);
    }
    auto const& full = cap.only("cache.full");
    CHECK(full.level == LogLevel::Warn);
    CHECK(field<std::uint64_t>(full, "size") == 256);
}

TEST_CASE("enrichment.property_index_oob names the index and the count on both paths",
          "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "type": "property_batch",
        "results": [{"status": "fails", "type": "property", "property_index": 1,
                     "timestamp": 1000000, "reason": "core"}]
    })");
    mock->queue_response(R"({
        "status": "complete",
        "results": [{"type": "property", "status": "fails", "property_index": 1, "reason": "r"}]
    })");
    auto client = streaming_client(std::move(mock), cap.logger());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, id, dlc, data).has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    REQUIRE(cap.count("enrichment.property_index_oob") == 2);
    for (auto const& e : cap.events) {
        if (e.name != "enrichment.property_index_oob")
            continue;
        CHECK(e.level == LogLevel::Warn);
        CHECK(field<std::int64_t>(e, "index") == 1);
        CHECK(field<std::uint64_t>(e, "count") == 1);
    }
}

TEST_CASE("without properties, a failing verdict is not an out-of-range index",
          "[client][log][fields]") {
    Capture cap;
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(std::string{k_violation});
    mock->queue_response(R"({
        "status": "complete",
        "results": [{"type": "property", "status": "fails", "property_index": 0, "reason": "r"}]
    })");
    AletheiaClient client(std::move(mock), cap.logger());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, id, dlc, data).has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());
    CHECK(cap.count("enrichment.property_index_oob") == 0);
}

TEST_CASE("extraction failures on the JSON path are logged by kind", "[client][log][fields]") {
    Capture cap;
    auto const fresh = [] {
        auto mock = std::make_unique<MockBackend>();
        mock->queue_response(R"({"status": "success"})"); // set_properties
        mock->queue_response(R"({"status": "success"})"); // start_stream
        return mock;
    };
    SECTION("the backend throws: extraction.process_failed") {
        auto mock = fresh();
        mock->queue_response(std::string{k_violation});
        // No extraction response is queued, so the mock throws on the call.
        auto client = streaming_client(std::move(mock), cap.logger());
        auto const id = CanId{StandardId::create(0x100).value()};
        REQUIRE(client
                    .send_frame(std::stop_token{}, Timestamp{1000}, id, Dlc::create(8).value(),
                                FramePayload(8))
                    .has_value());
        auto const& e = cap.only("extraction.process_failed");
        CHECK(e.level == LogLevel::Warn);
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK(field<std::string>(e, "error").contains("no queued response"));
    }
    SECTION("the response does not parse: extraction.parse_failed") {
        auto mock = fresh();
        mock->queue_response(std::string{k_violation});
        mock->queue_response(R"({"status": "success", "values": "not an array"})");
        auto client = streaming_client(std::move(mock), cap.logger());
        auto const id = CanId{StandardId::create(0x100).value()};
        REQUIRE(client
                    .send_frame(std::stop_token{}, Timestamp{1000}, id, Dlc::create(8).value(),
                                FramePayload(8))
                    .has_value());
        auto const& e = cap.only("extraction.parse_failed");
        CHECK(e.level == LogLevel::Warn);
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK_FALSE(field<std::string>(e, "error").empty());
    }
}

TEST_CASE("extraction failures on the binary path are logged by kind, and a success is not",
          "[client][log][fields]") {
    Capture cap;
    auto const arm = [&](std::unique_ptr<BinExtractMockBackend> mock) -> AletheiaClient {
        mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
        mock->queue_response(R"({"status": "success"})"); // set_properties
        mock->queue_response(R"({"status": "success"})"); // start_stream
        mock->queue_response(std::string{k_violation});
        AletheiaClient client(std::move(mock), cap.logger());
        REQUIRE(client.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
        std::vector<LtlFormula> props;
        props.push_back(ltl::always(
            ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{1, 1}}))));
        REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
        REQUIRE(client.start_stream(std::stop_token{}).has_value());
        return client;
    };
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const send = [&](AletheiaClient& client) {
        auto r = client.send_frame(std::stop_token{}, Timestamp{1000}, id, Dlc::create(8).value(),
                                   FramePayload(8));
        REQUIRE(r.has_value());
        auto const* v = std::get<PropertyBatch>(*r).first_violation();
        REQUIRE(v != nullptr);
        REQUIRE(v->enrichment.has_value());
        return v->enrichment->signals;
    };
    SECTION("a buffer that does not decode: extraction.parse_failed") {
        auto client = arm(std::make_unique<BinExtractMockBackend>(std::vector<std::byte>(9)));
        CHECK(send(client).empty());
        auto const& e = cap.only("extraction.parse_failed");
        CHECK(e.level == LogLevel::Warn);
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK(field<std::string>(e, "error").contains("Truncated"));
    }
    SECTION("an error other than BinaryUnsupported: extraction.process_failed, no fallback") {
        auto mock = std::make_unique<BinExtractMockBackend>(
            std::unexpected(AletheiaError{ErrorKind::Protocol, "boom"}));
        auto const* raw = mock.get();
        auto client = arm(std::move(mock));
        CHECK(send(client).empty());
        auto const& e = cap.only("extraction.process_failed");
        CHECK(e.level == LogLevel::Warn);
        CHECK(field<std::uint64_t>(e, "canId") == 0x100);
        CHECK(field<std::string>(e, "error") == "boom");
        CHECK_FALSE(took_json_extraction(*raw));
    }
    SECTION("a buffer that decodes: the value is enriched and nothing is warned") {
        auto client = arm(std::make_unique<BinExtractMockBackend>(one_value_at_index_zero()));
        auto const signals = send(client);
        REQUIRE(signals.contains(SignalName{"Speed"}));
        CHECK(signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{7, 1}});
        CHECK(cap.count("extraction.parse_failed") == 0);
        CHECK(cap.count("extraction.process_failed") == 0);
    }
}

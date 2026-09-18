// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: Client + MockBackend round-trip, lifecycle, batch, cache-full.
//
// Covers parse_dbc / extract_signals / build_frame / update_frame /
// validate_dbc / format_dbc JSON round-trips; client move + destructor
// lifecycle (C++ equivalent of Python/Go "double close is safe"); the
// send_frames batch API; and the 256-entry extraction cache eviction path.
#include "test_helpers.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <initializer_list>
#include <nlohmann/json.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <memory>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using Json = nlohmann::json;
using aletheia::test::BinExtractMockBackend;
using aletheia::test::make_test_dbc;
using aletheia::test::one_value_at_index_zero;
using aletheia::test::parsed_dbc_response_for;
using aletheia::test::took_json_extraction;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Client + Mock Backend round-trip tests
// ===========================================================================

TEST_CASE("client parse_dbc sends correct JSON and handles success", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get(); // retain for inspection
    mock_ptr->queue_response(parsed_dbc_response_for(make_test_dbc()));

    AletheiaClient client(std::move(mock));
    auto const result = client.parse_dbc(std::stop_token{}, make_test_dbc());

    CHECK(result.has_value());
    REQUIRE(mock_ptr->captured().size() == 1);

    auto j = Json::parse(mock_ptr->last_captured());
    CHECK(j["command"] == "parseDBC");
    CHECK(j["dbc"]["messages"][0]["id"] == 0x100);
}

TEST_CASE("client parse_dbc handles error response", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(
        R"({"status": "error", "code": "handler_validation_failed", "message": "Invalid DBC"})");

    AletheiaClient client(std::move(mock));
    auto result = client.parse_dbc(std::stop_token{}, make_test_dbc());

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("client extract_signals round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 120}],
        "errors": [],
        "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{Rational{120, 1}});

    // extract_signals is a binary-path call; the mock records a sentinel.
    // The canId/dlc/data marshalling is verified by the real-.so round-trip
    // tests (cross_binding_integration), not the mock.
    CHECK(mock_ptr->last_captured() == "<binary:extractAllSignals>");
}

TEST_CASE("client extract_signals falls back to JSON after parse_dbc with MockBackend",
          "[client][mock][binary_unsupported]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();
    // First response: parse_dbc success (populates signal_names_ cache).
    mock_ptr->queue_response(parsed_dbc_response_for(make_test_dbc()));
    // Second response: extract_signals JSON fallback.
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 55}],
        "errors": [],
        "absent": []
    })");

    AletheiaClient client(std::move(mock));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());

    // With the signal-name cache populated, Client tries the binary path
    // first; MockBackend's inherited default returns BinaryUnsupported, and
    // Client falls through to the JSON path.
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x37}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
}

TEST_CASE("client build_frame requires loaded DBC", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}},
    };
    auto result = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::State);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("no DBC loaded"));
}

TEST_CASE("client streaming workflow", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // Queue responses for: set_properties, start_stream, send_frame, end_stream
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "ack"})");
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0}
        ]
    })");

    AletheiaClient client(std::move(mock));

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    CHECK(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto frame_result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(frame_result.has_value());
    CHECK(std::holds_alternative<Ack>(*frame_result));

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    CHECK(end_result->results.size() == 1);
    CHECK(end_result->results[0].verdict == Verdict::Holds);

    // Verify command sequence.  setProperties is a real JSON command (sent via
    // process()); the streaming ops are binary-path calls the mock records as
    // `<binary:…>` sentinels (the real backend drives them through the binary FFI).
    REQUIRE(mock_ptr->captured().size() == 4);
    CHECK(Json::parse(mock_ptr->captured()[0])["command"] == "setProperties");
    CHECK(mock_ptr->captured()[1] == "<binary:startStream>");
    CHECK(mock_ptr->captured()[2] == "<binary:sendFrame>");
    CHECK(mock_ptr->captured()[3] == "<binary:endStream>");
}

TEST_CASE("client validate_dbc round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "status": "validation",
        "has_errors": false,
        "issues": [
            {"severity": "warning", "code": "empty_message", "detail": "Msg is empty"}
        ]
    })");

    AletheiaClient client(std::move(mock));
    auto result = client.validate_dbc(std::stop_token{}, make_test_dbc());

    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(result->issues.size() == 1);
    CHECK(result->issues[0].severity == IssueSeverity::Warning);
}

TEST_CASE("client format_dbc round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [{
                "id": 256, "name": "VehicleSpeed", "dlc": 8,
                "sender": "ECU1", "extended": false,
                "signals": [{
                    "name": "Speed", "startBit": 0, "length": 16,
                    "byteOrder": "little_endian", "signed": false,
                    "factor": {"numerator": 1, "denominator": 10},
                    "offset": 0, "minimum": 0, "maximum": 300, "unit": "km/h",
                    "presence": "always"
                }]
            }]
        }
    })");

    AletheiaClient client(std::move(mock));
    auto result = client.format_dbc(std::stop_token{});

    REQUIRE(result.has_value());
    CHECK(result->version == "1.0");
    CHECK(result->messages[0].signals[0].factor == RationalFactor{Rational{1, 10}});
}

TEST_CASE("client send_frame violation with enrichment fields", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "type": "property",
            "status": "fails",
            "property_index": {"numerator": 0, "denominator": 1},
            "timestamp": {"numerator": 2000000, "denominator": 1},
            "reason": "Speed limit exceeded"
        }]
    })");

    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{0});
    REQUIRE(v->timestamp.has_value());
    CHECK(*v->timestamp == Timestamp{2'000'000});
    CHECK(v->reason == "Speed limit exceeded");
}

TEST_CASE("client is movable", "[client]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));

    AletheiaClient client1(std::move(mock));
    CHECK(client1.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());

    AletheiaClient client2 = std::move(client1);
    CHECK(client2.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
}

// ---------------------------------------------------------------------------
// Client lifecycle / "close" semantics
// ---------------------------------------------------------------------------
// C++ uses RAII, not an explicit `close()` method — the destructor calls
// backend_->close(state_) when both are non-null. These tests mirror the
// Python and Go "double close / use after close" tests: they verify the
// C++ equivalent (move-from destructor, sequential scope lifecycle) is
// crash-safe and preserves backend state semantics.

TEST_CASE("moved-from client destructor is safe", "[client][lifecycle]") {
    // Destructor must handle a null state without dereferencing it. Both the
    // destructor and the move assignment release through one noexcept helper,
    // close_state, whose guard on the backend and the state protects against a
    // double close when the source of a move is destroyed afterwards. This is the C++ equivalent of
    // Python's and Go's "double close is safe" guarantee: the FFI state pointer is transferred to
    // the target, and the source is left in a valid-but- moved-from state whose destructor is a
    // no-op.
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));

    {
        AletheiaClient source(std::move(mock));
        {
            AletheiaClient target = std::move(source);
            CHECK(target.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
        } // target destructor closes state_
        // source destructor runs here — state_ is already nullptr from the
        // move; the guard in ~AletheiaClient prevents a double close.
    }
    // No crash, no double-free — test passes if we reach here.
    SUCCEED("moved-from client destructor completed without crash");
}

TEST_CASE("move-assignment releases current state before taking new", "[client][lifecycle]") {
    // Move-assigning an already-initialized client to another initialized
    // client must release the target's current state, so it is not leaked,
    // before adopting the source's. The same close_state helper the destructor
    // uses is what releases it.
    auto mock_a = std::make_unique<MockBackend>();
    mock_a->queue_response(parsed_dbc_response_for(make_test_dbc()));
    auto mock_b = std::make_unique<MockBackend>();
    mock_b->queue_response(parsed_dbc_response_for(make_test_dbc()));

    AletheiaClient client_a(std::move(mock_a));
    CHECK(client_a.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());

    AletheiaClient client_b(std::move(mock_b));
    // Overwrite client_a — the state_ from mock_a must be closed by the
    // move-assignment operator before client_a adopts mock_b's state.
    client_a = std::move(client_b);
    // Subsequent operations on client_a must use mock_b's queued responses.
    CHECK(client_a.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
    // client_b is now in moved-from state — destructor is a no-op (tested
    // implicitly by the lack of crash at end of scope).
}

TEST_CASE("sequential clients in same scope work independently", "[client][lifecycle]") {
    // Multiple clients created and destroyed in sequence must each have
    // independent state. This mirrors Python's test_sequential_clients.
    // Any shared mutable state across instances would be a serious bug —
    // the GHC RTS is reference-counted and thread-safe, but each
    // AletheiaClient owns its own StablePtr on the Haskell side.
    for (int i = 0; i < 3; ++i) {
        auto mock = std::make_unique<MockBackend>();
        mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
        AletheiaClient client(std::move(mock));
        CHECK(client.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
    } // Each iteration's destructor closes its state_ cleanly.
}

TEST_CASE("nested client scopes leave outer state intact", "[client][lifecycle]") {
    // Creating an inner client and destroying it inside an outer scope
    // must not affect the outer client's backend state. Guards against
    // bugs where the backend's close() logic somehow touches global state
    // that another live client depends on.
    auto mock_outer = std::make_unique<MockBackend>();
    mock_outer->queue_response(parsed_dbc_response_for(make_test_dbc())); // first outer op
    mock_outer->queue_response(parsed_dbc_response_for(make_test_dbc())); // second outer op

    AletheiaClient outer(std::move(mock_outer));
    CHECK(outer.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());

    {
        auto mock_inner = std::make_unique<MockBackend>();
        mock_inner->queue_response(parsed_dbc_response_for(make_test_dbc()));
        AletheiaClient inner(std::move(mock_inner));
        CHECK(inner.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
    } // inner destructed

    // Outer client must still be functional after inner's destruction.
    CHECK(outer.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());
}

// ===========================================================================
// update_frame client wiring
// ===========================================================================

TEST_CASE("client update_frame requires loaded DBC", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    std::vector<SignalValue> signals{
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},
    };

    auto result = client.update_frame(std::stop_token{}, id, dlc, data, signals);
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::State);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("no DBC loaded"));
}

// ===========================================================================
// send_frames batch
// ===========================================================================

TEST_CASE("send_frames all ack", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    backend->queue_response(R"({"status":"ack"})");     // frame 1
    backend->queue_response(R"({"status":"ack"})");     // frame 2
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload const data(8, std::byte{0});
    std::vector<Frame> frames{
        {.timestamp = Timestamp{1000}, .id = CanId{sid}, .dlc = dlc, .data = data},
        {.timestamp = Timestamp{2000}, .id = CanId{sid}, .dlc = dlc, .data = data},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE_FALSE(result.has_error());
    REQUIRE(result.responses.size() == 2);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
    CHECK(std::holds_alternative<Ack>(result.responses[1]));
}

TEST_CASE("send_frames stops on error with partial results", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    backend->queue_response(R"({"status":"ack"})");     // frame 1 — ok
    // frame 2 has mismatched DLC/payload — validation error before backend call
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload const good(8, std::byte{0});
    FramePayload const bad(3, std::byte{0}); // 3 bytes vs DLC 8
    std::vector<Frame> frames{
        {.timestamp = Timestamp{1000}, .id = CanId{sid}, .dlc = dlc, .data = good},
        {.timestamp = Timestamp{2000}, .id = CanId{sid}, .dlc = dlc, .data = bad},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.error->message().contains("payload"));
    // Partial results: frame 1 succeeded before frame 2 failed.
    REQUIRE(result.responses.size() == 1);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
}

TEST_CASE("send_frames with violation continues", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    backend->queue_response(R"({"status":"ack"})");     // frame 1
    backend->queue_response(
        R"({"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000,"reason":"test"}]})"); // frame 2
    // Enrichment triggers extract_signals for the violating frame:
    backend->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":350}],"errors":[],"absent":[]})");
    backend->queue_response(R"({"status":"ack"})"); // frame 3
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload const data(8, std::byte{0});
    std::vector<Frame> frames{
        {.timestamp = Timestamp{1000}, .id = CanId{sid}, .dlc = dlc, .data = data},
        {.timestamp = Timestamp{2000}, .id = CanId{sid}, .dlc = dlc, .data = data},
        {.timestamp = Timestamp{3000}, .id = CanId{sid}, .dlc = dlc, .data = data},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE_FALSE(result.has_error());
    REQUIRE(result.responses.size() == 3);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
    CHECK(std::holds_alternative<PropertyBatch>(result.responses[1]));
    CHECK(std::holds_alternative<Ack>(result.responses[2]));
}

TEST_CASE("send_frames negative timestamp", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    backend->queue_response(R"({"status":"ack"})");     // frame 1
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload const data(8, std::byte{0});
    std::vector<Frame> frames{
        {.timestamp = Timestamp{1000}, .id = CanId{sid}, .dlc = dlc, .data = data},
        {.timestamp = Timestamp{-1}, .id = CanId{sid}, .dlc = dlc, .data = data},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.error->message().contains("non-negative"));
    REQUIRE(result.responses.size() == 1);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
}

TEST_CASE("send_frames payload validation mid-batch reports frame index", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    backend->queue_response(R"({"status":"ack"})");     // frame 0
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const sid = CanId{StandardId::create(0x100).value()};
    auto const dlc8 = Dlc::create(8).value();
    auto const dlc4 = Dlc::create(4).value();
    std::array<std::byte, 8> good{};
    std::array<std::byte, 8> bad{}; // 8 bytes but DLC says 4

    std::vector<Frame> frames;
    frames.push_back({.timestamp = Timestamp{1000},
                      .id = sid,
                      .dlc = dlc8,
                      .data = FramePayload(good.begin(), good.end())});
    frames.push_back({.timestamp = Timestamp{2000},
                      .id = sid,
                      .dlc = dlc4,
                      .data = FramePayload(bad.begin(), bad.end())}); // mismatch
    frames.push_back({.timestamp = Timestamp{3000},
                      .id = sid,
                      .dlc = dlc8,
                      .data = FramePayload(good.begin(), good.end())});

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.responses.size() == 1); // frame 0 succeeded
    auto const msg = std::string(result.error->message());
    CHECK(msg.contains("frame 1"));
    CHECK(msg.contains("payload"));
}

TEST_CASE("send_frames empty", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const result = client.send_frames(std::stop_token{}, {});
    REQUIRE_FALSE(result.has_error());
    CHECK(result.responses.empty());
}

// ===========================================================================
// send_frames_lazy (lazy streaming variant — std::generator)
// ===========================================================================

static auto count_sentinel(const std::vector<std::string>& log, std::string_view want)
    -> std::size_t {
    return static_cast<std::size_t>(std::ranges::count(log, want));
}

// A mock-backed client already past set_properties + start_stream, with the
// given per-frame responses queued. Returns the client and a borrowed pointer
// to its (now client-owned) mock for call-log inspection.
static auto streaming_client(std::initializer_list<const char*> frame_responses)
    -> std::pair<AletheiaClient, MockBackend*> {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    for (auto const* r : frame_responses) {
        backend->queue_response(r);
    }
    auto* mock = backend.get();
    AletheiaClient client(std::move(backend));
    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(client.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    return {std::move(client), mock};
}

static auto ack_frames(std::size_t count) -> std::vector<Frame> {
    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    const FramePayload data(8, std::byte{0});
    std::vector<Frame> frames;
    frames.reserve(count);
    for (std::size_t i = 0; i < count; ++i) {
        frames.push_back({.timestamp = Timestamp{static_cast<std::int64_t>((i + 1) * 1000)},
                          .id = CanId{sid},
                          .dlc = dlc,
                          .data = data});
    }
    return frames;
}

TEST_CASE("send_frames_lazy yields one value per frame", "[client][batch][lazy]") {
    auto [client, mock] =
        streaming_client({R"({"status":"ack"})", R"({"status":"ack"})", R"({"status":"ack"})"});
    auto frames = ack_frames(3);

    std::size_t n = 0;
    for (auto&& r : client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(frames))) {
        REQUIRE(r.has_value());
        CHECK(std::holds_alternative<Ack>(*r));
        ++n;
    }
    CHECK(n == 3);
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 3);
}

TEST_CASE("send_frames_lazy stops after first error with frame index", "[client][batch][lazy]") {
    auto [client, mock] = streaming_client({R"({"status":"ack"})"}); // only frame 0 reaches backend
    auto const dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload const good(8, std::byte{0});
    FramePayload const bad(3, std::byte{0}); // 3 bytes vs DLC 8
    std::vector<Frame> frames{
        {.timestamp = Timestamp{1000}, .id = CanId{sid}, .dlc = dlc, .data = good},
        {.timestamp = Timestamp{2000}, .id = CanId{sid}, .dlc = dlc, .data = bad},
        {.timestamp = Timestamp{3000}, .id = CanId{sid}, .dlc = dlc, .data = good},
    };

    std::size_t oks = 0;
    std::string err_msg;
    for (auto&& r : client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(frames))) {
        if (!r.has_value()) {
            err_msg = std::string(r.error().message());
            break;
        }
        ++oks;
    }
    CHECK(oks == 1);
    CHECK(err_msg.contains("frame 1")); // index prefix mirrors send_frames
    CHECK(err_msg.contains("payload"));
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 1); // frame 2 never sent
}

TEST_CASE("send_frames_lazy surfaces violations and continues", "[client][batch][lazy]") {
    auto [client, mock] = streaming_client({
        R"({"status":"ack"})",
        R"({"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":2000,"reason":"test"}]})",
        R"({"status":"success","values":[{"name":"Speed","value":350}],"errors":[],"absent":[]})", // enrichment extract
        R"({"status":"ack"})",
    });
    auto frames = ack_frames(3);

    std::vector<FrameResponse> got;
    for (auto&& r : client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(frames))) {
        REQUIRE(r.has_value());
        got.push_back(*r);
    }
    REQUIRE(got.size() == 3);
    CHECK(std::holds_alternative<Ack>(got[0]));
    CHECK(std::holds_alternative<PropertyBatch>(got[1])); // a violation does not stop the stream
    CHECK(std::holds_alternative<Ack>(got[2]));
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 3);
}

TEST_CASE("send_frames_lazy empty source yields nothing", "[client][batch][lazy]") {
    auto [client, mock] = streaming_client({});
    std::vector<Frame> none;

    std::size_t n = 0;
    for (auto&& r : client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(none))) {
        (void)r;
        ++n;
    }
    CHECK(n == 0);
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 0);
}

TEST_CASE("send_frames_lazy commits only the consumed prefix", "[client][batch][lazy]") {
    auto [client, mock] =
        streaming_client({R"({"status":"ack"})", R"({"status":"ack"})", R"({"status":"ack"})",
                          R"({"status":"ack"})", R"({"status":"ack"})"});
    auto frames = ack_frames(5);

    std::size_t got = 0;
    for (auto&& r : client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(frames))) {
        REQUIRE(r.has_value());
        if (++got == 2) {
            break; // stop pulling — commit-prefix
        }
    }
    CHECK(got == 2);
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 2); // frames 3-5 never sent
}

TEST_CASE("send_frames_lazy matches send_frames", "[client][batch][lazy]") {
    auto const responses = {R"({"status":"ack"})", R"({"status":"ack"})", R"({"status":"ack"})"};

    auto [eager_client, eager_mock] = streaming_client(responses);
    auto eager_frames = ack_frames(3);
    auto eager = eager_client.send_frames(std::stop_token{}, eager_frames);

    auto [lazy_client, lazy_mock] = streaming_client(responses);
    auto lazy_frames = ack_frames(3);
    std::vector<FrameResponse> lazy;
    for (auto&& r :
         lazy_client.send_frames_lazy(std::stop_token{}, std::span<const Frame>(lazy_frames))) {
        REQUIRE(r.has_value());
        lazy.push_back(*r);
    }

    REQUIRE_FALSE(eager.has_error());
    REQUIRE(eager.responses.size() == lazy.size());
    for (std::size_t i = 0; i < lazy.size(); ++i) {
        CHECK(eager.responses[i].index() == lazy[i].index());
    }
    CHECK(eager_mock->captured() == lazy_mock->captured()); // identical backend call log
}

TEST_CASE("send_frames_lazy honors stop_token mid-stream", "[client][batch][lazy]") {
    // The stop-fired path (distinct from stopping by not-pulling): once stop is
    // requested, the next frame's send_frame returns ErrorKind::Cancellation,
    // which the generator co_yields as std::unexpected and then ends.
    auto [client, mock] =
        streaming_client({R"({"status":"ack"})", R"({"status":"ack"})", R"({"status":"ack"})"});
    auto frames = ack_frames(3);
    const std::stop_source source;

    std::size_t oks = 0;
    bool saw_cancellation = false;
    for (auto&& r : client.send_frames_lazy(source.get_token(), std::span<const Frame>(frames))) {
        if (!r.has_value()) {
            saw_cancellation = r.error().kind() == ErrorKind::Cancellation;
            break;
        }
        ++oks;
        source.request_stop(); // cancel after the first committed frame
    }
    CHECK(oks == 1);
    CHECK(saw_cancellation);
    CHECK(count_sentinel(mock->captured(), "<binary:sendFrame>") == 1); // only the committed frame
}

// ===========================================================================
// Move-assignment runtime test
// ===========================================================================

TEST_CASE("move-assignment transfers client state", "[client]") {
    // Source client: configured for streaming.
    auto backend_a = std::make_unique<MockBackend>();
    backend_a->queue_response(R"({"status":"success"})"); // set_properties
    backend_a->queue_response(R"({"status":"success"})"); // start_stream
    backend_a->queue_response(R"({"status":"ack"})");     // send_frame
    AletheiaClient a(std::move(backend_a));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    REQUIRE(a.set_properties(std::stop_token{}, std::span{&prop, 1}).has_value());
    REQUIRE(a.start_stream(std::stop_token{}).has_value());

    // Target client: separate backend (will be destroyed on assignment).
    auto backend_b = std::make_unique<MockBackend>();
    AletheiaClient b(std::move(backend_b));

    // Move-assign: b takes over a's state.
    b = std::move(a);

    auto id = StandardId::create(0x100).value();
    auto const dlc = Dlc::create(8).value();
    std::array<std::byte, 8> data{};
    auto resp = b.send_frame(std::stop_token{}, Timestamp{1000}, CanId{id}, dlc, data);
    REQUIRE(resp.has_value());
    CHECK(std::holds_alternative<Ack>(resp.value()));
}

// ===========================================================================
// Cache-full: extraction beyond the cache's capacity
// ===========================================================================

TEST_CASE("the public mock factory answers without anything queued", "[client][mock]") {
    // What an installed consumer can reach: the factory and the public headers.
    // The queueing methods are in a test-internal header, so a backend that
    // refused until its queue was filled would be one they could never call.
    auto backend = make_mock_backend();
    REQUIRE(backend);
    auto const state = backend->init();

    SECTION("a control-plane command is acknowledged") {
        CHECK(backend->process(state, R"({"command":"startStream"})") == R"({"status":"ack"})");
    }

    SECTION("every binary endpoint is acknowledged") {
        CHECK(backend->start_stream_binary(state) == R"({"status":"ack"})");
        CHECK(backend->end_stream_binary(state) == R"({"status":"ack"})");
        CHECK(backend->format_dbc_binary(state) == R"({"status":"ack"})");
        CHECK(backend->send_error_binary(state, Timestamp{0}) == R"({"status":"ack"})");
    }

    SECTION("a frame request comes back as a payload of the size asked for") {
        auto const id = CanId{StandardId::create(0x100).value()};
        auto const dlc = Dlc::create(8).value();
        auto const signals = SignalInjection::create({}, {}, {}).value();
        auto built = backend->build_frame_bin(state, id, dlc, signals, 8);
        REQUIRE(built.has_value());
        CHECK(built->size() == 8);
        CHECK(std::ranges::all_of(*built, [](std::byte b) { return b == std::byte{0}; }));
    }

    SECTION("the answer is canned, not consumed: it repeats") {
        CHECK(backend->start_stream_binary(state) == R"({"status":"ack"})");
        CHECK(backend->start_stream_binary(state) == R"({"status":"ack"})");
    }
}

TEST_CASE("the two doubles differ on purpose", "[client][mock]") {
    // The public one is fixed, so a consumer who cannot reach a queue still gets
    // an answer. The test-internal one refuses, because a suite that silently
    // received a fabricated answer would pass for the wrong reason.
    MockBackend configurable;
    auto const strict_state = configurable.init();
    CHECK_THROWS_AS(configurable.process(strict_state, "<binary:sendFrame>"), AletheiaException);

    auto fixed = make_mock_backend();
    auto const fixed_state = fixed->init();
    CHECK(fixed->process(fixed_state, "<binary:sendFrame>") == R"({"status":"ack"})");
}

TEST_CASE("MockBackend throws on queue exhaustion", "[client][mock]") {
    MockBackend mock;
    auto const state = mock.init();

    // Empty queue → exhaustion is a harness misconfiguration: the mock throws
    // rather than fabricating a default, as every binding's mock does. The
    // starved request is recorded BEFORE the throw, so captured() stays
    // populated on the erroring call.  Pin the kind AND exact message so a
    // silent downgrade (wrong ErrorKind, or a drifted op token) trips here.
    try {
        static_cast<void>(mock.process(state, "<binary:sendFrame>"));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.error().kind() == ErrorKind::State);
        CHECK(std::string{e.error().message()} ==
              "mock backend: no queued response for <binary:sendFrame>");
    }
    REQUIRE_FALSE(mock.captured().empty());
    CHECK(mock.last_captured() == "<binary:sendFrame>");

    // A JSON control-plane command starves the same way, but maps to the
    // generic "process" op token — the JSON→"process" mapping is the one most
    // likely to silently regress, so pin it exactly.
    try {
        static_cast<void>(mock.process(state, R"({"command":"setProperties","formulas":[]})"));
        FAIL("expected AletheiaException");
    } catch (const AletheiaException& e) {
        CHECK(e.error().kind() == ErrorKind::State);
        CHECK(std::string{e.error().message()} == "mock backend: no queued response for process");
    }

    // A queued response takes priority over the throw path.
    mock.queue_response(R"({"custom": true})");
    auto custom = mock.process(state, "<binary:sendFrame>");
    CHECK(custom == R"({"custom": true})");

    // Queue drained again → throws once more.
    CHECK_THROWS_AS(mock.process(state, "<binary:sendFrame>"), AletheiaException);
}

// Counts the releases of the state it hands out, so the handle's own policy has
// a test as well as the address sanitizer. The counter outlives the backend,
// which the client owns.
namespace {
class CountingCloseBackend : public MockBackend {
public:
    explicit CountingCloseBackend(int* closes) : closes_(closes) {}

protected:
    void close(void* state) override {
        ++*closes_;
        MockBackend::close(state);
    }

private:
    int* closes_;
};
} // namespace

TEST_CASE("the backend state is released exactly once over a client's life", "[client][state]") {
    SECTION("a move transfers the state rather than closing it") {
        int closes = 0;
        {
            AletheiaClient client{std::make_unique<CountingCloseBackend>(&closes)};
            CHECK(closes == 0);
            const AletheiaClient moved{std::move(client)};
            CHECK(closes == 0);
        }
        CHECK(closes == 1);
    }

    SECTION("assigning over a client releases what it held, once") {
        int first_closes = 0;
        int second_closes = 0;
        {
            AletheiaClient first{std::make_unique<CountingCloseBackend>(&first_closes)};
            AletheiaClient second{std::make_unique<CountingCloseBackend>(&second_closes)};
            second = std::move(first);
            // The state the target held is gone; the source's has moved across.
            CHECK(second_closes == 1);
            CHECK(first_closes == 0);
        }
        CHECK(first_closes == 1);
        CHECK(second_closes == 1);
    }

    SECTION("self-assignment releases nothing") {
        int closes = 0;
        {
            AletheiaClient client{std::make_unique<CountingCloseBackend>(&closes)};
            auto& alias = client;
            client = std::move(alias);
            CHECK(closes == 0);
        }
        CHECK(closes == 1);
    }
}

TEST_CASE("SignalInjection refuses a block the FFI would read past", "[client][injection]") {
    const std::vector<std::uint32_t> indices{0, 1};
    const std::vector<std::int64_t> numerators{1, 2};
    const std::vector<std::int64_t> denominators{1, 2};

    SECTION("three arrays of equal length are accepted") {
        auto block = SignalInjection::create(indices, numerators, denominators);
        REQUIRE(block.has_value());
        CHECK(block->count() == 2);
        CHECK(block->indices().size() == 2);
    }

    SECTION("a shorter numerator array is refused, not truncated") {
        const std::vector<std::int64_t> short_numerators{1};
        auto block = SignalInjection::create(indices, short_numerators, denominators);
        REQUIRE_FALSE(block.has_value());
        CHECK(block.error().contains("differ in length"));
    }

    SECTION("a shorter denominator array is refused too") {
        const std::vector<std::int64_t> short_denominators{1};
        auto block = SignalInjection::create(indices, numerators, short_denominators);
        REQUIRE_FALSE(block.has_value());
        CHECK(block.error().contains("differ in length"));
    }
}

TEST_CASE("MockBackend build_frame_bin / update_frame_bin error on queue exhaustion",
          "[client][mock]") {
    // Unlike process() (which returns std::string and throws on exhaustion),
    // the binary frame methods return std::expected and the Client forwards the
    // result directly — so exhaustion RETURNS a State-kinded unexpected with the
    // unified cross-binding message, it does NOT throw.  The op token is
    // still recorded on the starved call, matching Go / Python / Rust.
    MockBackend mock;
    auto const state = mock.init();
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    // The mock ignores the injection contents; an empty block suffices.
    auto const signals = SignalInjection::create({}, {}, {}).value();

    {
        auto result = mock.build_frame_bin(state, id, dlc, signals, 8);
        CHECK_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::State);
        CHECK(std::string{result.error().message()} ==
              "mock backend: no queued response for <binary:buildFrameBin>");
        CHECK(mock.last_captured() == "<binary:buildFrameBin>");
    }

    {
        auto result =
            mock.update_frame_bin(state, id, dlc, std::span<const std::byte>{}, signals, 8);
        CHECK_FALSE(result.has_value());
        CHECK(result.error().kind() == ErrorKind::State);
        CHECK(std::string{result.error().message()} ==
              "mock backend: no queued response for <binary:updateFrameBin>");
        CHECK(mock.last_captured() == "<binary:updateFrameBin>");
    }

    // Success path: a queued packed-frame byte buffer is returned verbatim.
    {
        mock.queue_frame_bytes({std::byte{0x01}, std::byte{0x02}});
        auto result = mock.build_frame_bin(state, id, dlc, signals, 8);
        REQUIRE(result.has_value());
        CHECK(*result == std::vector<std::byte>{std::byte{0x01}, std::byte{0x02}});
    }
}

TEST_CASE("parse_dbc_text arms the binary extraction path", "[client][mock]") {
    auto mock = std::make_unique<BinExtractMockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(parsed_dbc_response_for(make_test_dbc()));
    AletheiaClient client(std::move(mock));
    REQUIRE(client.parse_dbc_text(std::stop_token{}, "VERSION \"\"").has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const result =
        client.extract_signals(std::stop_token{}, id, Dlc::create(8).value(), FramePayload(8));
    REQUIRE(result.has_value());
    CHECK_FALSE(took_json_extraction(*mock_ptr));
}

TEST_CASE("reloading a DBC replaces the previous one's signals under the same message id",
          "[client][mock]") {
    auto mock = std::make_unique<BinExtractMockBackend>(one_value_at_index_zero());
    auto* mock_ptr = mock.get();
    auto const first = make_test_dbc();
    auto second = make_test_dbc();
    second.messages[0].signals[0].name = SignalName{"Other"};
    mock_ptr->queue_response(parsed_dbc_response_for(first));
    mock_ptr->queue_response(parsed_dbc_response_for(second));
    AletheiaClient client(std::move(mock));
    REQUIRE(client.parse_dbc(std::stop_token{}, first).has_value());
    REQUIRE(client.parse_dbc(std::stop_token{}, second).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    SECTION("the old signal no longer resolves") {
        const std::vector<SignalValue> signals{
            {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{1, 1}}}};
        auto const built = client.build_frame(std::stop_token{}, id, dlc, signals);
        REQUIRE_FALSE(built.has_value());
        CHECK(built.error().kind() == ErrorKind::Validation);
        CHECK_THAT(std::string{built.error().message()},
                   ContainsSubstring("signal 'Speed' not found"));
    }
    SECTION("a wire index names the new signal") {
        auto const result = client.extract_signals(std::stop_token{}, id, dlc, FramePayload(8));
        REQUIRE(result.has_value());
        REQUIRE(result->values.size() == 1);
        CHECK(result->values[0].name == SignalName{"Other"});
        CHECK(result->values[0].value == PhysicalValue{Rational{7, 1}});
    }
}

TEST_CASE("build_frame refuses a signal the message does not carry, by name", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(parsed_dbc_response_for(make_test_dbc()));
    AletheiaClient client(std::move(mock));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_test_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Nope"}, .value = PhysicalValue{Rational{1, 1}}}};
    auto const built = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE_FALSE(built.has_value());
    CHECK(built.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{built.error().message()}, ContainsSubstring("signal 'Nope' not found"));
}

TEST_CASE("client keys its signal cache on the extended bit for extraction and resolution",
          "[client][mock][extended]") {
    auto const id = CanId{ExtendedId::create(0x18FEF100).value()};
    auto dbc = make_test_dbc();
    dbc.messages[0].id = id;

    auto mock = std::make_unique<BinExtractMockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(parsed_dbc_response_for(dbc));
    AletheiaClient client(std::move(mock));
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});

    SECTION("extraction of an extended-ID frame takes the binary path") {
        auto const result = client.extract_signals(std::stop_token{}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(result->values.empty());
        CHECK(std::ranges::none_of(mock_ptr->captured(), [](const std::string& call) {
            return call == "<binary:extractAllSignals>";
        }));
    }
    SECTION("frame building resolves the extended-ID message") {
        mock_ptr->queue_frame_bytes(std::vector<std::byte>(8, std::byte{0}));
        const std::vector<SignalValue> signals{
            {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{1, 1}}}};
        auto const built = client.build_frame(std::stop_token{}, id, dlc, signals);
        REQUIRE(built.has_value());
    }
}

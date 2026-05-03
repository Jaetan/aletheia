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

#include <nlohmann/json.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using json = nlohmann::json;
using aletheia::test::make_test_dbc;
using aletheia::test::parsed_dbc_response_for;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Client + Mock Backend round-trip tests
// ===========================================================================

TEST_CASE("client parse_dbc sends correct JSON and handles success", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get(); // retain for inspection
    mock_ptr->queue_response(parsed_dbc_response_for(make_test_dbc()));

    AletheiaClient client(std::move(mock));
    auto result = client.parse_dbc(std::stop_token{}, make_test_dbc());

    CHECK(result.has_value());
    REQUIRE(mock_ptr->captured().size() == 1);

    auto j = json::parse(mock_ptr->last_captured());
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
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{Rational{120, 1}});

    auto j = json::parse(mock_ptr->last_captured());
    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
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
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
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
    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{Rational{100, 1}}},
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

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto frame_result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(frame_result.has_value());
    CHECK(std::holds_alternative<Ack>(*frame_result));

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    CHECK(end_result->results.size() == 1);
    CHECK(end_result->results[0].verdict == Verdict::Holds);

    // Verify command sequence
    REQUIRE(mock_ptr->captured().size() == 4);
    CHECK(json::parse(mock_ptr->captured()[0])["command"] == "setProperties");
    CHECK(json::parse(mock_ptr->captured()[1])["command"] == "startStream");
    CHECK(json::parse(mock_ptr->captured()[2])["type"] == "data");
    CHECK(json::parse(mock_ptr->captured()[3])["command"] == "endStream");
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
                    "offset": 0, "minimum": 0, "maximum": 300, "unit": "km/h"
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
        "status": "fails",
        "type": "property",
        "property_index": {"numerator": 0, "denominator": 1},
        "timestamp": {"numerator": 2000000, "denominator": 1},
        "reason": "Speed limit exceeded"
    })");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{0});
    CHECK(v.timestamp == Timestamp{2'000'000});
    CHECK(v.reason == "Speed limit exceeded");
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
    // Destructor must handle `state_ == nullptr` without dereferencing —
    // the guard at client.cpp:56 (`if (backend_ != nullptr && state_ != nullptr)`)
    // protects against a double close when the source of a move is
    // subsequently destroyed. This is the C++ equivalent of Python's and
    // Go's "double close is safe" guarantee: the FFI state pointer is
    // transferred to the target, and the source is left in a valid-but-
    // moved-from state whose destructor is a no-op.
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
    // client must release the target's current state (so it isn't leaked)
    // before adopting the source's state. The guard at client.cpp:73
    // (`if (backend_ != nullptr && state_ != nullptr)`) enforces this.
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
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    std::vector<SignalValue> signals{
        {SignalName{"RPM"}, PhysicalValue{Rational{3000, 1}}},
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
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{2000}, CanId{sid}, dlc, data},
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
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload good(8, std::byte{0});
    FramePayload bad(3, std::byte{0}); // 3 bytes vs DLC 8
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, good},
        {Timestamp{2000}, CanId{sid}, dlc, bad},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.error->message().find("payload") != std::string::npos);
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
        R"({"status":"fails","type":"property","property_index":0,"timestamp":2000,"reason":"test"})"); // frame 2
    // Enrichment triggers extract_signals for the violating frame:
    backend->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":350}],"errors":[],"absent":[]})");
    backend->queue_response(R"({"status":"ack"})"); // frame 3
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{2000}, CanId{sid}, dlc, data},
        {Timestamp{3000}, CanId{sid}, dlc, data},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE_FALSE(result.has_error());
    REQUIRE(result.responses.size() == 3);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
    CHECK(std::holds_alternative<Violation>(result.responses[1]));
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
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{-1}, CanId{sid}, dlc, data},
    };

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.error->message().find("non-negative") != std::string::npos);
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
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto sid = CanId{StandardId::create(0x100).value()};
    auto dlc8 = Dlc::create(8).value();
    auto dlc4 = Dlc::create(4).value();
    std::array<std::byte, 8> good{};
    std::array<std::byte, 8> bad{}; // 8 bytes but DLC says 4

    std::vector<Frame> frames;
    frames.push_back({Timestamp{1000}, sid, dlc8, FramePayload(good.begin(), good.end())});
    frames.push_back(
        {Timestamp{2000}, sid, dlc4, FramePayload(bad.begin(), bad.end())}); // mismatch
    frames.push_back({Timestamp{3000}, sid, dlc8, FramePayload(good.begin(), good.end())});

    auto result = client.send_frames(std::stop_token{}, frames);
    REQUIRE(result.has_error());
    CHECK(result.responses.size() == 1); // frame 0 succeeded
    auto msg = std::string(result.error->message());
    CHECK(msg.find("frame 1") != std::string::npos);
    CHECK(msg.find("payload") != std::string::npos);
}

TEST_CASE("send_frames empty", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    (void)client.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)client.start_stream(std::stop_token{});

    auto result = client.send_frames(std::stop_token{}, {});
    REQUIRE_FALSE(result.has_error());
    CHECK(result.responses.empty());
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
    (void)a.set_properties(std::stop_token{}, std::span{&prop, 1});
    (void)a.start_stream(std::stop_token{});

    // Target client: separate backend (will be destroyed on assignment).
    auto backend_b = std::make_unique<MockBackend>();
    AletheiaClient b(std::move(backend_b));

    // Move-assign: b takes over a's state.
    b = std::move(a);

    auto id = StandardId::create(0x100).value();
    auto dlc = Dlc::create(8).value();
    std::array<std::byte, 8> data{};
    auto resp = b.send_frame(std::stop_token{}, Timestamp{1000}, CanId{id}, dlc, data);
    REQUIRE(resp.has_value());
    CHECK(std::holds_alternative<Ack>(resp.value()));
}

// ===========================================================================
// Cache-full test (C2): extraction cache eviction beyond 256 entries
// ===========================================================================

TEST_CASE("extraction cache full still works on 257th frame", "[client][enrich][cache]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // Queue: set_properties, start_stream
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "success"})");

    // Queue 257 ack responses for send_frame
    for (int i = 0; i < 257; ++i)
        mock_ptr->queue_response(R"({"status": "ack"})");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();

    // Send 257 frames with distinct data payloads to fill and overflow the cache
    for (int i = 0; i < 257; ++i) {
        FramePayload data(8, std::byte{0});
        // Vary first two bytes to make each frame key unique
        data[0] = static_cast<std::byte>(i & 0xFF);
        data[1] = static_cast<std::byte>((i >> 8) & 0xFF);
        auto result = client.send_frame(
            std::stop_token{}, Timestamp{static_cast<std::int64_t>(i) * 1000}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(std::holds_alternative<Ack>(*result));
    }
}

TEST_CASE("MockBackend default response path", "[client][mock]") {
    MockBackend mock;
    auto* state = mock.init();

    // Fire-and-forget command (no queued response) → ack
    auto ack = mock.process(state, R"({"command":"sendFrame","data":{}})");
    CHECK(ack == R"({"status": "ack"})");

    // Binary-path fire-and-forget → ack
    auto ack_bin = mock.process(state, R"({"type":"data","ts":0})");
    CHECK(ack_bin == R"({"status": "ack"})");

    // Non-fire-and-forget command → success
    auto ok = mock.process(state, R"({"command":"setProperties","formulas":[]})");
    CHECK(ok == R"({"status": "success"})");

    // Queued response takes priority over defaults
    mock.queue_response(R"({"custom": true})");
    auto custom = mock.process(state, R"({"command":"sendFrame","data":{}})");
    CHECK(custom == R"({"custom": true})");
}

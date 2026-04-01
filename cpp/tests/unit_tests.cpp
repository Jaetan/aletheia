// Layer 2: Unit tests with mock backend.
// Tests JSON serialization, parsing, and client round-trips.
#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <nlohmann/json.hpp>

using namespace aletheia;
using json = nlohmann::json;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Helper: build a minimal DBC for testing
// ===========================================================================

static auto make_test_dbc() -> DbcDefinition {
    auto id = StandardId::create(0x100).value();
    auto dlc = Dlc::create(8).value();

    DbcSignal sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 10}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{300, 1}},
        .unit = Unit{"km/h"},
        .presence = AlwaysPresent{},
    };

    DbcMessage msg{
        .id = CanId{id},
        .name = MessageName{"VehicleSpeed"},
        .dlc = dlc,
        .sender = NodeName{"ECU1"},
        .signals = {sig},
    };

    return DbcDefinition{.version = "1.0", .messages = {msg}};
}

// ===========================================================================
// JSON Serialization tests
// ===========================================================================

TEST_CASE("serialize_parse_dbc produces valid JSON", "[json][serialize]") {
    auto dbc = make_test_dbc();
    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);

    CHECK(j["type"] == "command");
    CHECK(j["command"] == "parseDBC");
    CHECK(j["dbc"]["version"] == "1.0");
    CHECK(j["dbc"]["messages"].size() == 1);

    auto& msg = j["dbc"]["messages"][0];
    CHECK(msg["id"] == 0x100);
    CHECK(msg["name"] == "VehicleSpeed");
    CHECK(msg["dlc"] == 8);
    CHECK(msg["sender"] == "ECU1");
    CHECK(msg["extended"] == false);

    auto& sig = msg["signals"][0];
    CHECK(sig["name"] == "Speed");
    CHECK(sig["startBit"] == 0);
    CHECK(sig["length"] == 16);
    CHECK(sig["byteOrder"] == "little_endian");
    CHECK(sig["signed"] == false);
    CHECK(sig["factor"]["numerator"] == 1);
    CHECK(sig["factor"]["denominator"] == 10);
    CHECK(sig["offset"] == 0);
    CHECK(sig["minimum"] == 0);
    CHECK(sig["maximum"] == 300);
    CHECK(sig["unit"] == "km/h");
    CHECK(sig["presence"] == "always");
}

TEST_CASE("serialize_extract_signals produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto str = detail::serialize_extract_signals(id, dlc, data);
    auto j = json::parse(str);

    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["data"].size() == 8);
    CHECK(j["data"][0] == 0xE8);
    CHECK(j["data"][1] == 0x03);
}

TEST_CASE("serialize_build_frame produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{120.0}},
        {SignalName{"RPM"}, PhysicalValue{3000.0}},
    };
    auto str = detail::serialize_build_frame(id, Dlc::create(8).value(), signals);
    auto j = json::parse(str);

    CHECK(j["command"] == "buildFrame");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["signals"].size() == 2);
    CHECK(j["signals"][0]["name"] == "Speed");
    CHECK(j["signals"][0]["value"] == Catch::Approx(120.0));
    CHECK(j["signals"][1]["name"] == "RPM");
}

TEST_CASE("serialize_set_properties produces correct JSON", "[json][serialize]") {
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto str = detail::serialize_set_properties(props);
    auto j = json::parse(str);

    CHECK(j["command"] == "setProperties");
    CHECK(j["properties"].size() == 1);
    CHECK(j["properties"][0]["operator"] == "always");
    CHECK(j["properties"][0]["formula"]["operator"] == "atomic");
    CHECK(j["properties"][0]["formula"]["predicate"]["predicate"] == "lessThan");
    CHECK(j["properties"][0]["formula"]["predicate"]["signal"] == "Speed");
    CHECK(j["properties"][0]["formula"]["predicate"]["value"] == Catch::Approx(220.0));
}

TEST_CASE("serialize_send_frame produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto str = detail::serialize_send_frame(Timestamp{1'000'000}, id, dlc, data);
    auto j = json::parse(str);

    CHECK(j["type"] == "data");
    CHECK(j["timestamp"] == 1'000'000);
    CHECK(j["id"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["data"].size() == 8);
}

TEST_CASE("serialize multiplexed signal", "[json][serialize]") {
    auto id = StandardId::create(0x200).value();
    auto dlc = Dlc::create(8).value();

    DbcSignal sig{
        .name = SignalName{"MuxedTemp"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::BigEndian,
        .is_signed = true,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{-40, 1}},
        .minimum = RationalBound{Rational{-40, 1}},
        .maximum = RationalBound{Rational{215, 1}},
        .unit = Unit{"C"},
        .presence = Multiplexed{SignalName{"MuxSelector"}, MultiplexValue{3}},
    };

    DbcDefinition dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"Sensors"},
            .dlc = dlc,
            .sender = NodeName{"ECU2"},
            .signals = {sig},
        }},
    };

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);
    auto& jsig = j["dbc"]["messages"][0]["signals"][0];

    CHECK(jsig["byteOrder"] == "big_endian");
    CHECK(jsig["signed"] == true);
    CHECK(jsig["multiplexor"] == "MuxSelector");
    CHECK(jsig["multiplex_value"] == 3);
    CHECK_FALSE(jsig.contains("presence"));
}

TEST_CASE("serialize extended CAN ID in DBC", "[json][serialize]") {
    auto id = ExtendedId::create(0x18FEF100).value();
    auto dlc = Dlc::create(8).value();

    DbcDefinition dbc{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"J1939Msg"},
            .dlc = dlc,
            .sender = NodeName{"Truck"},
            .signals = {},
        }},
    };

    auto str = detail::serialize_parse_dbc(dbc);
    auto j = json::parse(str);
    auto& msg = j["dbc"]["messages"][0];

    CHECK(msg["id"] == 0x18FEF100);
    CHECK(msg["extended"] == true);
}

TEST_CASE("serialize metric temporal operators", "[json][serialize]") {
    auto inner = ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{1.0}));
    auto formula = ltl::always_within(Timestamp{2'000'000}, std::move(inner));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    auto str = detail::serialize_set_properties(props);
    auto j = json::parse(str);

    CHECK(j["properties"][0]["operator"] == "metricAlways");
    CHECK(j["properties"][0]["timebound"] == 2'000'000);
}

TEST_CASE("serialize all predicate types", "[json][serialize]") {
    auto check = [](Predicate p, const std::string& expected) {
        auto formula = ltl::atomic(std::move(p));
        std::vector<LtlFormula> props;
        props.push_back(std::move(formula));
        auto str = detail::serialize_set_properties(props);
        auto j = json::parse(str);
        CHECK(j["properties"][0]["predicate"]["predicate"] == expected);
    };

    check(ltl::equals(SignalName{"S"}, PhysicalValue{0}), "equals");
    check(ltl::less_than(SignalName{"S"}, PhysicalValue{0}), "lessThan");
    check(ltl::greater_than(SignalName{"S"}, PhysicalValue{0}), "greaterThan");
    check(ltl::at_most(SignalName{"S"}, PhysicalValue{0}), "lessThanOrEqual");
    check(ltl::at_least(SignalName{"S"}, PhysicalValue{0}), "greaterThanOrEqual");
    check(ltl::between(SignalName{"S"}, PhysicalValue{0}, PhysicalValue{100}), "between");
    check(ltl::changed_by(SignalName{"S"}, Delta{10.0}), "changedBy");
}

// ===========================================================================
// JSON Parsing tests
// ===========================================================================

TEST_CASE("parse_success on success response", "[json][parse]") {
    auto result = detail::parse_success(R"({"status": "success"})");
    CHECK(result.has_value());
}

TEST_CASE("parse_success on error response", "[json][parse]") {
    auto result = detail::parse_success(R"({"status": "error", "message": "DBC not loaded"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("DBC not loaded"));
}

TEST_CASE("parse_validation response", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "factor_zero", "detail": "Signal X has zero factor"},
            {"severity": "warning", "code": "empty_message", "detail": "Message Y is empty"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->has_errors);
    CHECK(result->issues.size() == 2);
    CHECK(result->issues[0].severity == IssueSeverity::Error);
    CHECK(result->issues[0].code == IssueCode::FactorZero);
    CHECK(result->issues[1].severity == IssueSeverity::Warning);
    CHECK(result->issues[1].code == IssueCode::EmptyMessage);
}

TEST_CASE("parse_extraction response", "[json][parse]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "Speed", "value": 120.5},
            {"name": "RPM", "value": 3000}
        ],
        "errors": [
            {"name": "BadSig", "error": "overflow"}
        ],
        "absent": ["MuxedTemp"]
    })");
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{120.5});
    CHECK(result->values[1].value == PhysicalValue{3000.0});
    CHECK(result->errors.size() == 1);
    CHECK(result->errors[0].first == SignalName{"BadSig"});
    CHECK(result->absent.size() == 1);
    CHECK(result->absent[0] == SignalName{"MuxedTemp"});
}

TEST_CASE("parse_extraction with rational values", "[json][parse]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [
            {"name": "Ratio", "value": {"numerator": 1, "denominator": 3}}
        ],
        "errors": [],
        "absent": []
    })");
    REQUIRE(result.has_value());
    CHECK(result->values[0].value.get() == Catch::Approx(1.0 / 3.0));
}

TEST_CASE("parse_frame_data response", "[json][parse]") {
    auto result = detail::parse_frame_data(R"({
        "status": "success",
        "data": [232, 3, 0, 0, 0, 0, 0, 0]
    })");
    REQUIRE(result.has_value());
    CHECK(result->size() == 8);
    CHECK((*result)[0] == std::byte{232});
    CHECK((*result)[1] == std::byte{3});
    CHECK((*result)[7] == std::byte{0});
}

TEST_CASE("parse_frame_response ack", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({"status": "ack"})");
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("parse_frame_response violation", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": 0,
        "timestamp": 5000000,
        "reason": "Speed exceeded limit"
    })");
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{0});
    CHECK(v.timestamp == Timestamp{5'000'000});
    CHECK(v.reason == "Speed exceeded limit");
}

TEST_CASE("parse_frame_response violation with rational index", "[json][parse]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "type": "property",
        "property_index": {"numerator": 2, "denominator": 1},
        "timestamp": {"numerator": 3000000, "denominator": 1}
    })");
    REQUIRE(result.has_value());
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{2});
    CHECK(v.timestamp == Timestamp{3'000'000});
}

TEST_CASE("parse_stream_result complete", "[json][parse]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "Never satisfied"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->results.size() == 2);
    CHECK(result->results[0].verdict == Verdict::Holds);
    CHECK(result->results[0].property_index == PropertyIndex{0});
    CHECK(result->results[1].verdict == Verdict::Fails);
    CHECK(result->results[1].timestamp == Timestamp{5'000'000});
    CHECK(result->results[1].reason == "Never satisfied");
}

TEST_CASE("parse_dbc_response", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "2.0",
            "messages": [{
                "id": 256,
                "name": "TestMsg",
                "dlc": 8,
                "sender": "Node1",
                "extended": false,
                "signals": [{
                    "name": "Sig1",
                    "startBit": 0,
                    "length": 8,
                    "byteOrder": "little_endian",
                    "signed": false,
                    "factor": 1,
                    "offset": 0,
                    "minimum": 0,
                    "maximum": 255,
                    "unit": ""
                }]
            }]
        }
    })");
    REQUIRE(result.has_value());
    CHECK(result->version == "2.0");
    CHECK(result->messages.size() == 1);
    CHECK(result->messages[0].name == MessageName{"TestMsg"});
    CHECK(result->messages[0].signals[0].name == SignalName{"Sig1"});
    CHECK(result->messages[0].signals[0].factor == RationalFactor{Rational{1, 1}});
}

// ===========================================================================
// Client + Mock Backend round-trip tests
// ===========================================================================

TEST_CASE("client parse_dbc sends correct JSON and handles success", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get(); // retain for inspection
    mock_ptr->queue_response(R"({"status": "success"})");

    AletheiaClient client(std::move(mock));
    auto result = client.parse_dbc(make_test_dbc());

    CHECK(result.has_value());
    REQUIRE(mock_ptr->captured().size() == 1);

    auto j = json::parse(mock_ptr->last_captured());
    CHECK(j["command"] == "parseDBC");
    CHECK(j["dbc"]["messages"][0]["id"] == 0x100);
}

TEST_CASE("client parse_dbc handles error response", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "error", "message": "Invalid DBC"})");

    AletheiaClient client(std::move(mock));
    auto result = client.parse_dbc(make_test_dbc());

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
    auto result = client.extract_signals(id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{120.0});

    auto j = json::parse(mock_ptr->last_captured());
    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
}

TEST_CASE("client build_frame round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success", "data": [232, 3, 0, 0, 0, 0, 0, 0]})");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{100.0}},
    };
    auto result = client.build_frame(id, Dlc::create(8).value(), signals);

    REQUIRE(result.has_value());
    CHECK((*result)[0] == std::byte{232});
    CHECK((*result)[1] == std::byte{3});
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

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    CHECK(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto frame_result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(frame_result.has_value());
    CHECK(std::holds_alternative<Ack>(*frame_result));

    auto end_result = client.end_stream();
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
    auto result = client.validate_dbc(make_test_dbc());

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
    auto result = client.format_dbc();

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
    auto result = client.send_frame(Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{0});
    CHECK(v.timestamp == Timestamp{2'000'000});
    CHECK(v.reason == "Speed limit exceeded");
}

TEST_CASE("client is movable", "[client]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");
    mock->queue_response(R"({"status": "success"})");

    AletheiaClient client1(std::move(mock));
    CHECK(client1.parse_dbc(make_test_dbc()).has_value());

    AletheiaClient client2 = std::move(client1);
    CHECK(client2.parse_dbc(make_test_dbc()).has_value());
}

// ===========================================================================
// Error handling and edge-case tests
// ===========================================================================

TEST_CASE("parse_success rejects malformed JSON", "[json][parse][error]") {
    auto result = detail::parse_success("not json at all");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_success rejects missing status field", "[json][parse][error]") {
    auto result = detail::parse_success(R"({"foo": "bar"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected status"));
}

TEST_CASE("parse_extraction rejects missing status field", "[json][parse][error]") {
    auto result = detail::parse_extraction(R"({"values": []})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("status"));
}

TEST_CASE("parse_extraction handles missing optional arrays", "[json][parse]") {
    auto result = detail::parse_extraction(R"({"status": "success"})");
    REQUIRE(result.has_value());
    CHECK(result->values.empty());
    CHECK(result->errors.empty());
    CHECK(result->absent.empty());
}

TEST_CASE("parse_frame_data accepts variable-length data", "[json][parse]") {
    auto result = detail::parse_frame_data(R"({"status": "success", "data": [1, 2, 3]})");
    REQUIRE(result.has_value());
    CHECK(result->size() == 3);
    CHECK((*result)[0] == std::byte{1});
    CHECK((*result)[2] == std::byte{3});
}

TEST_CASE("parse_frame_data accepts CAN-FD 64-byte data", "[json][parse]") {
    // DLC 15 → 64 bytes
    std::string json_str = R"({"status": "success", "data": [)";
    for (int i = 0; i < 64; ++i) {
        if (i > 0)
            json_str += ", ";
        json_str += std::to_string(i);
    }
    json_str += "]}";
    auto result = detail::parse_frame_data(json_str);
    REQUIRE(result.has_value());
    CHECK(result->size() == 64);
    CHECK((*result)[0] == std::byte{0});
    CHECK((*result)[63] == std::byte{63});
}

TEST_CASE("parse_frame_response rejects empty status", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({"foo": "bar"})");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unexpected frame status"));
}

TEST_CASE("parse_dbc_response rejects missing dbc field", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({"status": "success"})");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("dbc"));
}

TEST_CASE("parse_dbc_response rejects malformed signal", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "1.0",
            "messages": [{
                "id": 256, "name": "Msg", "dlc": 8,
                "signals": [{"MISSING_NAME": true}]
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response with empty messages array", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {"version": "1.0", "messages": []}
    })");
    REQUIRE(result.has_value());
    CHECK(result->messages.empty());
    CHECK(result->version == "1.0");
}

TEST_CASE("parse_dbc_response with empty signals array", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "EmptyMsg", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE(result.has_value());
    CHECK(result->messages.size() == 1);
    CHECK(result->messages[0].signals.empty());
}

TEST_CASE("parse_validation with unknown issue code returns Unknown", "[json][parse]") {
    auto result = detail::parse_validation(R"({
        "status": "validation",
        "has_errors": true,
        "issues": [
            {"severity": "error", "code": "some_future_code", "detail": "New check"}
        ]
    })");
    REQUIRE(result.has_value());
    CHECK(result->issues[0].code == IssueCode::Unknown);
}

TEST_CASE("parse_number rejects non-numeric JSON via exception", "[json][parse][error]") {
    // parse_number throws on bad input; the public wrapper converts to Result
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": "not_a_number"}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response rejects out-of-range CAN ID", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 99999, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("CAN ID"));
}

TEST_CASE("parse_dbc_response rejects out-of-range DLC", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "",
            "messages": [{
                "id": 256, "name": "Bad", "dlc": 99,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("DLC"));
}

TEST_CASE("parse_extraction rejects zero denominator in rational", "[json][parse][error]") {
    auto result = detail::parse_extraction(R"({
        "status": "success",
        "values": [{"name": "Bad", "value": {"numerator": 1, "denominator": 0}}],
        "errors": [], "absent": []
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("denominator"));
}

TEST_CASE("parse_frame_response rejects zero denominator in timestamp", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": 0,
        "timestamp": {"numerator": 1000, "denominator": 0}
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("denominator"));
}

TEST_CASE("parse_stream_result rejects malformed JSON", "[json][parse][error]") {
    auto result = detail::parse_stream_result("not json");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects missing results field", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({"status": "complete"})");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_frame_response rejects negative property_index", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": -1,
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_stream_result rejects negative property_index", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"status": "holds", "property_index": -5}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Negative property_index"));
}

TEST_CASE("parse_frame_response rejects fails with missing timestamp", "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": 0
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_frame_response rejects fails with missing property_index",
          "[json][parse][error]") {
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_stream_result rejects entry with missing status", "[json][parse][error]") {
    auto result = detail::parse_stream_result(R"({
        "status": "complete",
        "results": [{"property_index": 0}]
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Unknown verdict status"));
}

TEST_CASE("parse_rational_as_int rejects non-exact rational", "[json][parse][error]") {
    // {"numerator": 3, "denominator": 2} → 1.5, not an integer
    auto result = detail::parse_frame_response(R"({
        "status": "fails",
        "property_index": {"numerator": 3, "denominator": 2},
        "timestamp": 100
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("Non-exact rational"));
}

TEST_CASE("parse_rational rejects float input", "[json][parse][error]") {
    // A floating-point 1.5 should be rejected (not integer, not {num, den} dict)
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 1, "name": "M", "dlc": 8, "extended": false,
                "signals": [{
                    "name": "S", "startBit": 0, "length": 8,
                    "byteOrder": "little_endian", "signed": false,
                    "factor": 1.5, "offset": 0, "minimum": 0,
                    "maximum": 255, "unit": ""
                }]
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse_dbc_response accepts standard CAN ID at boundary (2047)", "[json][parse]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 2047, "name": "Max", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    REQUIRE(result.has_value());
    auto& id = result->messages[0].id;
    CHECK(std::get<StandardId>(id).value() == 2047);
}

TEST_CASE("parse_dbc_response rejects standard CAN ID at boundary (2048)", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 2048, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("CAN ID"));
}

TEST_CASE("parse_dbc_response rejects truncating standard CAN ID (70000)", "[json][parse][error]") {
    auto result = detail::parse_dbc_response(R"({
        "status": "success",
        "dbc": {
            "version": "", "messages": [{
                "id": 70000, "name": "Bad", "dlc": 8,
                "extended": false, "signals": []
            }]
        }
    })");
    CHECK_FALSE(result.has_value());
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("uint16"));
}

TEST_CASE("ExtractionResult::get helper", "[response]") {
    ExtractionResult result{
        .values =
            {
                {SignalName{"Speed"}, PhysicalValue{120.0}},
                {SignalName{"RPM"}, PhysicalValue{3000.0}},
            },
        .errors = {},
        .absent = {},
    };

    CHECK(result.get(SignalName{"Speed"}) == PhysicalValue{120.0});
    CHECK(result.get(SignalName{"RPM"}) == PhysicalValue{3000.0});
    CHECK(result.get(SignalName{"Missing"}) == PhysicalValue{0.0});
    CHECK(result.get(SignalName{"Missing"}, PhysicalValue{-1.0}) == PhysicalValue{-1.0});
    CHECK_FALSE(result.has_errors());
}

// ===========================================================================
// Formula pretty-printer tests
// ===========================================================================

TEST_CASE("format_formula always less than", "[enrich]") {
    auto f = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    CHECK(format_formula(f) == "always(Speed < 220)");
}

TEST_CASE("format_formula never pattern", "[enrich]") {
    auto f = ltl::never(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{100.0}));
    CHECK(format_formula(f) == "never Speed > 100");
}

TEST_CASE("format_formula eventually", "[enrich]") {
    auto f = ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{1.0})));
    CHECK(format_formula(f) == "eventually(Mode = 1)");
}

TEST_CASE("format_formula metric always", "[enrich]") {
    auto f =
        ltl::always_within(Timestamp{5'000'000},
                           ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    CHECK(format_formula(f) == "always within 5s (Speed < 220)");
}

TEST_CASE("format_formula metric eventually", "[enrich]") {
    auto f = ltl::within(Timestamp{2'000'000},
                         ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{1.0})));
    CHECK(format_formula(f) == "eventually within 2s (Mode = 1)");
}

TEST_CASE("format_formula next", "[enrich]") {
    auto f = ltl::next(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    CHECK(format_formula(f) == "next(Speed < 220)");
}

TEST_CASE("format_formula and", "[enrich]") {
    auto f = ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                       ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{500.0})));
    CHECK(format_formula(f) == "Speed < 220 and RPM > 500");
}

TEST_CASE("format_formula or", "[enrich]") {
    auto f = ltl::either(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                         ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{500.0})));
    CHECK(format_formula(f) == "Speed < 220 or RPM > 500");
}

TEST_CASE("format_formula until", "[enrich]") {
    auto f = ltl::until(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{50.0})),
                        ltl::atomic(ltl::equals(SignalName{"Brake"}, PhysicalValue{1.0})));
    CHECK(format_formula(f) == "Speed < 50 until Brake = 1");
}

TEST_CASE("format_formula release", "[enrich]") {
    auto f = ltl::release(ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{1.0})),
                          ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{0.0})));
    CHECK(format_formula(f) == "A = 1 release B = 0");
}

TEST_CASE("format_formula all predicate types", "[enrich]") {
    auto eq = ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{42.0}));
    CHECK(format_formula(eq) == "S = 42");

    auto lt = ltl::atomic(ltl::less_than(SignalName{"S"}, PhysicalValue{10.0}));
    CHECK(format_formula(lt) == "S < 10");

    auto gt = ltl::atomic(ltl::greater_than(SignalName{"S"}, PhysicalValue{5.0}));
    CHECK(format_formula(gt) == "S > 5");

    auto le = ltl::atomic(ltl::at_most(SignalName{"S"}, PhysicalValue{100.0}));
    CHECK(format_formula(le) == "S <= 100");

    auto ge = ltl::atomic(ltl::at_least(SignalName{"S"}, PhysicalValue{0.0}));
    CHECK(format_formula(ge) == "S >= 0");

    auto bw = ltl::atomic(ltl::between(SignalName{"S"}, PhysicalValue{10.0}, PhysicalValue{14.5}));
    CHECK(format_formula(bw) == "10 <= S <= 14.5");

    auto cb = ltl::atomic(ltl::changed_by(SignalName{"S"}, Delta{5.0}));
    auto cb_str = format_formula(cb);
    CHECK_THAT(cb_str, ContainsSubstring("S"));
    CHECK_THAT(cb_str, ContainsSubstring("> 5"));
}

// ===========================================================================
// Signal collection tests
// ===========================================================================

TEST_CASE("collect_signals multi-signal", "[enrich]") {
    auto f = ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                       ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{500.0})));
    auto signals = collect_signals(f);
    REQUIRE(signals.size() == 2);
    CHECK(signals[0] == SignalName{"Speed"});
    CHECK(signals[1] == SignalName{"RPM"});
}

TEST_CASE("collect_signals dedup", "[enrich]") {
    auto f = ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                       ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{0.0})));
    auto signals = collect_signals(f);
    CHECK(signals.size() == 1);
    CHECK(signals[0] == SignalName{"Speed"});
}

TEST_CASE("build_diagnostic always succeeds", "[enrich]") {
    auto f = ltl::always(
        ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                  ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{500.0}))));
    auto diag = build_diagnostic(f);
    CHECK(diag.signals.size() == 2);
    CHECK_FALSE(diag.formula_desc.empty());
    CHECK_THAT(diag.formula_desc, ContainsSubstring("Speed"));
    CHECK_THAT(diag.formula_desc, ContainsSubstring("RPM"));
}

// ===========================================================================
// Client enrichment tests
// ===========================================================================

TEST_CASE("set_properties auto-derives diagnostics", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // set_properties success
    mock_ptr->queue_response(R"({"status": "success"})");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());

    // Verify by triggering enrichment: start_stream, send_frame (violation), extraction
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 2000000,
        "reason": "Atomic: predicate failed"
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    REQUIRE(client.start_stream().has_value());
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0x00}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto result = client.send_frame(Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));

    auto& v = std::get<Violation>(*result);
    REQUIRE(v.enrichment.has_value());
    CHECK_THAT(v.enrichment->formula_desc, ContainsSubstring("Speed < 220"));
    CHECK_THAT(v.enrichment->enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK_THAT(v.enrichment->enriched_reason, ContainsSubstring("formula:"));
    CHECK(v.enrichment->signals.size() == 1);
    CHECK(v.enrichment->signals.at(SignalName{"Speed"}) == PhysicalValue{245.0});
    CHECK(v.enrichment->core_reason == "Atomic: predicate failed");
    CHECK_THAT(v.enrichment->enriched_reason,
               ContainsSubstring("[core: Atomic: predicate failed]"));
}

TEST_CASE("send_frame multi-signal enrichment", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 2000000
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}, {"name": "RPM", "value": 3000}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})),
                  ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{500.0}))));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(result.has_value());
    auto& v = std::get<Violation>(*result);
    REQUIRE(v.enrichment.has_value());
    CHECK(v.enrichment->signals.size() == 2);
    CHECK_THAT(v.enrichment->enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK_THAT(v.enrichment->enriched_reason, ContainsSubstring("RPM = 3000"));
}

TEST_CASE("extraction caching: same frame extracts once", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    // Two violations, same frame — only one extraction
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 1000000
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 2000000
    })");
    // No second extraction response needed — cached

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    auto r1 = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r1.has_value());
    CHECK(std::get<Violation>(*r1).enrichment.has_value());

    auto r2 = client.send_frame(Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(r2.has_value());
    CHECK(std::get<Violation>(*r2).enrichment.has_value());

    // Count extractAllSignals commands (should be exactly 1)
    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        auto j = json::parse(captured);
        if (j.contains("command") && j["command"] == "extractAllSignals")
            ++extract_count;
    }
    CHECK(extract_count == 1);
}

TEST_CASE("end_stream enriches failed verdicts", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "Never satisfied"}
        ]
    })");
    // EOS enrichment: extract_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Mode", "value": 0}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{1.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream();
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 1);
    CHECK(end_result->results[0].verdict == Verdict::Fails);
    REQUIRE(end_result->results[0].enrichment.has_value());
    CHECK_THAT(end_result->results[0].enrichment->formula_desc, ContainsSubstring("Mode = 1"));
    CHECK_THAT(end_result->results[0].enrichment->enriched_reason, ContainsSubstring("Mode = 0"));
    CHECK(end_result->results[0].enrichment->core_reason == "Never satisfied");
    CHECK_THAT(end_result->results[0].enrichment->enriched_reason,
               ContainsSubstring("[core: Never satisfied]"));
}

TEST_CASE("start_stream clears extraction cache", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 1000000
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");
    // end first stream
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [{"type": "property", "status": "holds", "property_index": 0}]
    })");
    // second stream
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream (clears cache)
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 1000000
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 250}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    auto r1 = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r1.has_value());
    REQUIRE(client.end_stream().has_value());

    // Second stream: same frame data but cache cleared
    REQUIRE(client.start_stream().has_value());
    auto r2 = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r2.has_value());
    CHECK(std::get<Violation>(*r2).enrichment.has_value());

    // Should have 2 extractAllSignals calls (cache was cleared)
    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        auto j = json::parse(captured);
        if (j.contains("command") && j["command"] == "extractAllSignals")
            ++extract_count;
    }
    CHECK(extract_count == 2);
}

TEST_CASE("no enrichment without set_properties", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 2000000,
        "reason": "Speed limit exceeded"
    })");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    auto& v = std::get<Violation>(*result);
    CHECK_FALSE(v.enrichment.has_value());
}

// ===========================================================================
// CoreReason enrichment tests
// ===========================================================================

TEST_CASE("violation enrichment omits core_reason when empty", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 2000000
    })");
    mock->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    auto& v = std::get<Violation>(*result);
    REQUIRE(v.enrichment.has_value());
    CHECK(v.enrichment->core_reason.empty());
    // enriched_reason should NOT contain "[core:" when reason is empty
    CHECK_THAT(v.enrichment->enriched_reason, !ContainsSubstring("[core:"));
}

// ===========================================================================
// End-of-stream last-known signal values test
// ===========================================================================

TEST_CASE("end_stream enrichment includes last-known signal values", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    // First frame: violation triggers extraction → populates cache
    mock_ptr->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 0, "timestamp": 1000000,
        "reason": "Atomic: predicate failed"
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");
    // Second frame: ack (no violation)
    mock_ptr->queue_response(R"({"status": "ack"})");
    // End stream: violation at EOS
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "MetricEventually: window expired"}
        ]
    })");
    // EOS enrichment: extract_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{300.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    REQUIRE(client.send_frame(Timestamp{1'000'000}, id, dlc, data).has_value());
    REQUIRE(client.send_frame(Timestamp{2'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream();
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 1);
    REQUIRE(end_result->results[0].enrichment.has_value());
    auto& enrichment = *end_result->results[0].enrichment;

    // Last-known values from last-frame tracking (populated by send_frame)
    CHECK_FALSE(enrichment.signals.empty());
    CHECK(enrichment.signals.at(SignalName{"Speed"}) == PhysicalValue{245.0});
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK(enrichment.core_reason == "MetricEventually: window expired");
    CHECK_THAT(enrichment.enriched_reason,
               ContainsSubstring("[core: MetricEventually: window expired]"));
}

// ===========================================================================
// update_frame tests
// ===========================================================================

TEST_CASE("serialize_update_frame produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    std::vector<SignalValue> signals{
        {SignalName{"RPM"}, PhysicalValue{3000.0}},
    };
    auto str = detail::serialize_update_frame(id, dlc, data, signals);
    auto j = json::parse(str);

    CHECK(j["command"] == "updateFrame");
    CHECK(j["canId"] == 0x100);
    CHECK(j["dlc"] == 8);
    CHECK(j["data"].size() == 8);
    CHECK(j["data"][0] == 0xE8);
    CHECK(j["data"][1] == 0x03);
    CHECK(j["signals"].size() == 1);
    CHECK(j["signals"][0]["name"] == "RPM");
    CHECK(j["signals"][0]["value"] == Catch::Approx(3000.0));
}

TEST_CASE("client update_frame round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success", "data": [232, 3, 184, 11, 0, 0, 0, 0]})");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    std::vector<SignalValue> signals{
        {SignalName{"RPM"}, PhysicalValue{3000.0}},
    };

    auto result = client.update_frame(id, dlc, data, signals);
    REQUIRE(result.has_value());
    CHECK(result->size() == 8);
    CHECK((*result)[0] == std::byte{232});
    CHECK((*result)[2] == std::byte{184});
    CHECK((*result)[3] == std::byte{11});
}

// ===========================================================================
// Payload validation tests
// ===========================================================================

TEST_CASE("send_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value(); // expects 8 bytes
    FramePayload short_data(3, std::byte{0});
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, short_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("payload length 3"));
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("expected 8 bytes"));
}

TEST_CASE("extract_signals rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload long_data(16, std::byte{0}); // 16 bytes but DLC 8 expects 8
    auto result = client.extract_signals(id, dlc, long_data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("update_frame rejects payload length mismatch", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload bad_data(5, std::byte{0});
    std::vector<SignalValue> signals{{SignalName{"S"}, PhysicalValue{1.0}}};
    auto result = client.update_frame(id, dlc, bad_data, signals);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

TEST_CASE("send_frame accepts correct payload length", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0}); // exactly 8 bytes for DLC 8
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

TEST_CASE("send_frame accepts CAN-FD payload", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "ack"})");
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(15).value(); // DLC 15 = 64 bytes
    FramePayload data(64, std::byte{0});
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<Ack>(*result));
}

// ===========================================================================
// Negative timestamp validation test
// ===========================================================================

TEST_CASE("send_frame rejects negative timestamp", "[client][validation]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{-1000}, id, dlc, data);

    CHECK_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string{result.error().message()}, ContainsSubstring("non-negative"));
}

// ===========================================================================
// EOS enrichment from ack-only frames (last-frame tracking)
// ===========================================================================

TEST_CASE("end_stream enrichment uses last-frame tracking, not just cache", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    // Frame gets ack (no violation) — NOT in extraction cache, but tracked in last_frames_
    mock_ptr->queue_response(R"({"status": "ack"})");
    // End stream: property fails at EOS
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "MetricEventually: window expired"}
        ]
    })");
    // EOS enrichment: extract_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 150}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula =
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{300.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    // Send a frame that gets ack (no violation, so no extraction cache entry)
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto frame_result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(frame_result.has_value());
    CHECK(std::holds_alternative<Ack>(*frame_result));

    auto end_result = client.end_stream();
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 1);
    REQUIRE(end_result->results[0].enrichment.has_value());
    auto& enrichment = *end_result->results[0].enrichment;

    // Signal values came from last-frame tracking, not the extraction cache
    CHECK_FALSE(enrichment.signals.empty());
    CHECK(enrichment.signals.at(SignalName{"Speed"}) == PhysicalValue{150.0});
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Speed = 150"));
}

// ===========================================================================
// Logger
// ===========================================================================

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

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(Timestamp{1'000'000}, id, dlc, data).has_value());
    REQUIRE(client.end_stream().has_value());

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

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    // Should not crash or produce output
    REQUIRE(client.set_properties(props).has_value());
}

// ===========================================================================
// Check API — one-shot methods
// ===========================================================================

TEST_CASE("Check::signal never_exceeds", "[check]") {
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{220});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Speed < 220)");
}

TEST_CASE("Check::signal never_below", "[check]") {
    auto result = Check::signal("Voltage").never_below(PhysicalValue{11.5});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Voltage >= 11.5)");
}

TEST_CASE("Check::signal stays_between", "[check]") {
    auto result = Check::signal("Voltage").stays_between(PhysicalValue{11.5}, PhysicalValue{14.5});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(11.5 <= Voltage <= 14.5)");
}

TEST_CASE("Check::signal never_equals", "[check]") {
    auto result = Check::signal("ErrorCode").never_equals(PhysicalValue{255});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "never ErrorCode = 255");
}

// ===========================================================================
// Check API — two-step methods
// ===========================================================================

TEST_CASE("Check::signal equals always", "[check]") {
    auto result = Check::signal("Gear").equals(PhysicalValue{0}).always();
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Gear = 0)");
}

TEST_CASE("Check::signal settles_between within", "[check]") {
    using namespace std::chrono_literals;
    auto result =
        Check::signal("Temp").settles_between(PhysicalValue{60}, PhysicalValue{80}).within(500ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always within 500ms (60 <= Temp <= 80)");
}

// ===========================================================================
// Check API — causal chains (when/then)
// ===========================================================================

TEST_CASE("Check::when then equals within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Brake")
                      .exceeds(PhysicalValue{50})
                      .then("BrakeLight")
                      .equals(PhysicalValue{1})
                      .within(100ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))");
}

TEST_CASE("Check::when drops_below then within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Voltage")
                      .drops_below(PhysicalValue{11})
                      .then("Warning")
                      .equals(PhysicalValue{1})
                      .within(50ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Voltage < 11) or eventually within 50ms (Warning = 1))");
}

TEST_CASE("Check::when then stays_between within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Brake")
                      .exceeds(PhysicalValue{50})
                      .then("Speed")
                      .stays_between(PhysicalValue{0}, PhysicalValue{10})
                      .within(200ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Brake > 50) or eventually within 200ms (0 <= Speed <= 10))");
}

TEST_CASE("Check::when equals then exceeds within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Ignition")
                      .equals(PhysicalValue{1})
                      .then("FuelPump")
                      .exceeds(PhysicalValue{0})
                      .within(50ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Ignition = 1) or eventually within 50ms (FuelPump > 0))");
}

// ===========================================================================
// Check API — metadata
// ===========================================================================

TEST_CASE("Check metadata named and severity", "[check]") {
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{220});
    result.named("SpeedLimit").severity("critical");
    CHECK(result.name() == "SpeedLimit");
    CHECK(result.check_severity() == "critical");
    CHECK(result.signal_name() == "Speed");
    CHECK(result.condition_desc() == "< 220");
}

TEST_CASE("Check signal_name and condition_desc populated", "[check]") {
    auto r1 = Check::signal("V").never_below(PhysicalValue{11.5});
    CHECK(r1.signal_name() == "V");
    CHECK(r1.condition_desc() == ">= 11.5");

    auto r2 = Check::signal("E").never_equals(PhysicalValue{0});
    CHECK(r2.signal_name() == "E");
    CHECK(r2.condition_desc() == "!= 0");
}

TEST_CASE("Check when/then metadata", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Brake")
                      .exceeds(PhysicalValue{50})
                      .then("Light")
                      .equals(PhysicalValue{1})
                      .within(100ms);
    CHECK(result.signal_name() == "Light");
    CHECK(result.condition_desc() == "= 1 within 100ms");
}

// ===========================================================================
// Check API — to_formula consumed on second call
// ===========================================================================

TEST_CASE("Check to_formula consumed", "[check]") {
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{220});
    auto f1 = result.to_formula();
    REQUIRE(f1.has_value());
    auto f2 = result.to_formula();
    CHECK_FALSE(f2.has_value());
}

// ===========================================================================
// Check API — error cases
// ===========================================================================

TEST_CASE("Check settles_between negative time throws", "[check]") {
    using namespace std::chrono_literals;
    auto builder = Check::signal("T").settles_between(PhysicalValue{0}, PhysicalValue{100});
    CHECK_THROWS_AS(builder.within(-1ms), std::invalid_argument);
}

TEST_CASE("Check when/then negative time throws", "[check]") {
    using namespace std::chrono_literals;
    auto cond = Check::when("A").exceeds(PhysicalValue{0}).then("B").equals(PhysicalValue{1});
    CHECK_THROWS_AS(cond.within(-1ms), std::invalid_argument);
}

// ===========================================================================
// Check API — equivalence with manual ltl:: construction
// ===========================================================================

TEST_CASE("Check never_exceeds matches manual ltl", "[check]") {
    auto check_f = Check::signal("Speed").never_exceeds(PhysicalValue{220}).to_formula();
    auto manual_f =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220})));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check stays_between matches manual ltl", "[check]") {
    auto check_f =
        Check::signal("V").stays_between(PhysicalValue{11.5}, PhysicalValue{14.5}).to_formula();
    auto manual_f = ltl::always(
        ltl::atomic(ltl::between(SignalName{"V"}, PhysicalValue{11.5}, PhysicalValue{14.5})));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check never_equals matches manual ltl", "[check]") {
    auto check_f = Check::signal("Err").never_equals(PhysicalValue{255}).to_formula();
    auto manual_f = ltl::never(ltl::equals(SignalName{"Err"}, PhysicalValue{255}));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check settles matches manual ltl", "[check]") {
    using namespace std::chrono_literals;
    auto check_f = Check::signal("T")
                       .settles_between(PhysicalValue{60}, PhysicalValue{80})
                       .within(500ms)
                       .to_formula();
    auto manual_f = ltl::always_within(
        Timestamp{500'000},
        ltl::atomic(ltl::between(SignalName{"T"}, PhysicalValue{60}, PhysicalValue{80})));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

// ===========================================================================
// Check API — add_checks client integration
// ===========================================================================

TEST_CASE("add_checks sends properties to backend", "[check][client]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");
    AletheiaClient client(std::move(mock));

    std::vector<CheckResult> checks;
    checks.push_back(Check::signal("Speed").never_exceeds(PhysicalValue{220}));
    checks.push_back(
        Check::signal("Voltage").stays_between(PhysicalValue{11.5}, PhysicalValue{14.5}));
    auto result = client.add_checks(std::move(checks));
    REQUIRE(result.has_value());
}

TEST_CASE("add_checks rejects consumed check", "[check][client]") {
    auto mock = std::make_unique<MockBackend>();
    AletheiaClient client(std::move(mock));

    auto check = Check::signal("Speed").never_exceeds(PhysicalValue{220});
    auto _ = check.to_formula(); // consume
    (void)_;

    std::vector<CheckResult> checks;
    checks.push_back(std::move(check));
    auto result = client.add_checks(std::move(checks));
    REQUIRE_FALSE(result.has_value());
    CHECK(std::string(result.error().message()).find("already consumed") != std::string::npos);
}

// ===========================================================================
// Multiplexing query helpers
// ===========================================================================

static auto make_mux_dbc() -> DbcDefinition {
    auto id = StandardId::create(0x200).value();
    auto dlc = Dlc::create(8).value();

    std::vector<DbcSignal> sigs;
    sigs.push_back(DbcSignal{.name = SignalName{"MuxSelector"},
                             .start_bit = BitPosition{0},
                             .bit_length = BitLength{8},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 1}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{255, 1}},
                             .unit = Unit{""},
                             .presence = AlwaysPresent{}});
    sigs.push_back(DbcSignal{.name = SignalName{"Temperature"},
                             .start_bit = BitPosition{8},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = true,
                             .factor = RationalFactor{Rational{1, 10}},
                             .offset = RationalOffset{Rational{-40, 1}},
                             .minimum = RationalBound{Rational{-40, 1}},
                             .maximum = RationalBound{Rational{215, 1}},
                             .unit = Unit{"degC"},
                             .presence = Multiplexed{.multiplexor = SignalName{"MuxSelector"},
                                                     .mux_value = MultiplexValue{0}}});
    sigs.push_back(DbcSignal{.name = SignalName{"Pressure"},
                             .start_bit = BitPosition{8},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 100}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{655, 1}},
                             .unit = Unit{"bar"},
                             .presence = Multiplexed{.multiplexor = SignalName{"MuxSelector"},
                                                     .mux_value = MultiplexValue{1}}});
    sigs.push_back(DbcSignal{.name = SignalName{"Voltage"},
                             .start_bit = BitPosition{40},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 100}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{65, 1}},
                             .unit = Unit{"V"},
                             .presence = AlwaysPresent{}});

    DbcMessage msg{.id = CanId{id},
                   .name = MessageName{"MuxMessage"},
                   .dlc = dlc,
                   .sender = NodeName{"ECU"},
                   .signals = std::move(sigs)};
    return DbcDefinition{.version = "1.0", .messages = {std::move(msg)}};
}

TEST_CASE("DbcMessage::is_multiplexed", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    CHECK(dbc.messages[0].is_multiplexed());

    auto plain = make_test_dbc();
    CHECK_FALSE(plain.messages[0].is_multiplexed());
}

TEST_CASE("DbcMessage::always_present_signals", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto ap = dbc.messages[0].always_present_signals();
    REQUIRE(ap.size() == 2);
    CHECK(ap[0].name == SignalName{"MuxSelector"});
    CHECK(ap[1].name == SignalName{"Voltage"});
}

TEST_CASE("DbcMessage::multiplexed_signals", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto ms = dbc.messages[0].multiplexed_signals();
    REQUIRE(ms.size() == 2);
    CHECK(ms[0].name == SignalName{"Temperature"});
    CHECK(ms[1].name == SignalName{"Pressure"});
}

TEST_CASE("DbcMessage::multiplexor_names", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto mn = dbc.messages[0].multiplexor_names();
    REQUIRE(mn.size() == 1);
    CHECK(mn[0] == SignalName{"MuxSelector"});
}

TEST_CASE("DbcMessage::mux_values", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto mv = dbc.messages[0].mux_values(SignalName{"MuxSelector"});
    REQUIRE(mv.size() == 2);
    CHECK(mv[0] == MultiplexValue{0});
    CHECK(mv[1] == MultiplexValue{1});

    auto empty = dbc.messages[0].mux_values(SignalName{"NonExistent"});
    CHECK(empty.empty());
}

TEST_CASE("DbcMessage::signals_for_mux_value", "[dbc][mux]") {
    auto dbc = make_mux_dbc();

    auto s0 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{0});
    REQUIRE(s0.size() == 3); // MuxSelector + Temperature + Voltage
    CHECK(s0[0].name == SignalName{"MuxSelector"});
    CHECK(s0[1].name == SignalName{"Temperature"});
    CHECK(s0[2].name == SignalName{"Voltage"});

    auto s1 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{1});
    REQUIRE(s1.size() == 3); // MuxSelector + Pressure + Voltage
    CHECK(s1[1].name == SignalName{"Pressure"});

    auto s99 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{99});
    CHECK(s99.size() == 2); // only always-present

    // Unknown multiplexor name — only always-present signals returned.
    auto su = dbc.messages[0].signals_for_mux_value(SignalName{"NonExistent"}, MultiplexValue{0});
    CHECK(su.size() == 2);
    CHECK(su[0].name == SignalName{"MuxSelector"});
    CHECK(su[1].name == SignalName{"Voltage"});
}

TEST_CASE("DbcMessage::multiplexor_names non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    CHECK(plain.messages[0].multiplexor_names().empty());
}

TEST_CASE("DbcMessage::always_present_signals non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    auto ap = plain.messages[0].always_present_signals();
    CHECK(ap.size() == plain.messages[0].signals.size());
}

TEST_CASE("DbcMessage::signal_by_name", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto* sig = dbc.messages[0].signal_by_name(SignalName{"Temperature"});
    REQUIRE(sig != nullptr);
    CHECK(sig->is_signed == true);

    // Always-present signal.
    auto* mux_sel = dbc.messages[0].signal_by_name(SignalName{"MuxSelector"});
    REQUIRE(mux_sel != nullptr);
    CHECK(std::holds_alternative<AlwaysPresent>(mux_sel->presence));

    CHECK(dbc.messages[0].signal_by_name(SignalName{"NoSuch"}) == nullptr);
}

TEST_CASE("DbcMessage::mux_values non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    CHECK(plain.messages[0].mux_values(SignalName{"Anything"}).empty());
}

TEST_CASE("DbcMessage::signals_for_mux_value non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    // Unknown multiplexor on a non-mux message returns all signals (all always-present).
    auto sigs = plain.messages[0].signals_for_mux_value(SignalName{"Anything"}, MultiplexValue{0});
    CHECK(sigs.size() == plain.messages[0].signals.size());
}

TEST_CASE("DbcDefinition::message_by_id", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto id = StandardId::create(0x200).value();
    auto* msg = dbc.message_by_id(CanId{id});
    REQUIRE(msg != nullptr);
    CHECK(msg->name == MessageName{"MuxMessage"});

    auto missing = StandardId::create(0x7FF).value(); // valid 11-bit, not in DBC
    CHECK(dbc.message_by_id(CanId{missing}) == nullptr);

    // Extended ID 0x200 should not match standard ID 0x200.
    auto ext = ExtendedId::create(0x200).value();
    CHECK(dbc.message_by_id(CanId{ext}) == nullptr);
}

TEST_CASE("DbcDefinition::message_by_id with extended ID", "[dbc]") {
    auto std_id = StandardId::create(0x200).value();
    auto ext_id = ExtendedId::create(0x200).value();
    DbcMessage std_msg{.id = CanId{std_id},
                       .name = MessageName{"StdMsg"},
                       .dlc = Dlc::create(8).value(),
                       .sender = NodeName{"ECU"},
                       .signals = {}};
    DbcMessage ext_msg{.id = CanId{ext_id},
                       .name = MessageName{"ExtMsg"},
                       .dlc = Dlc::create(8).value(),
                       .sender = NodeName{"ECU"},
                       .signals = {}};
    DbcDefinition dbc{.version = "1.0", .messages = {std_msg, ext_msg}};

    auto* found_std = dbc.message_by_id(CanId{std_id});
    REQUIRE(found_std != nullptr);
    CHECK(found_std->name == MessageName{"StdMsg"});

    auto* found_ext = dbc.message_by_id(CanId{ext_id});
    REQUIRE(found_ext != nullptr);
    CHECK(found_ext->name == MessageName{"ExtMsg"});
}

TEST_CASE("DbcDefinition::message_by_name", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto* msg = dbc.message_by_name(MessageName{"MuxMessage"});
    REQUIRE(msg != nullptr);
    CHECK(msg->signals.size() == 4);

    CHECK(dbc.message_by_name(MessageName{"NoSuch"}) == nullptr);

    // Empty DBC returns nullptr.
    DbcDefinition empty{.version = "1.0", .messages = {}};
    CHECK(empty.message_by_name(MessageName{"Anything"}) == nullptr);
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

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)client.set_properties(std::span{&prop, 1});
    (void)client.start_stream();

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{2000}, CanId{sid}, dlc, data},
    };

    auto result = client.send_frames(frames);
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

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)client.set_properties(std::span{&prop, 1});
    (void)client.start_stream();

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload good(8, std::byte{0});
    FramePayload bad(3, std::byte{0}); // 3 bytes vs DLC 8
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, good},
        {Timestamp{2000}, CanId{sid}, dlc, bad},
    };

    auto result = client.send_frames(frames);
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
        R"({"status":"fails","property_index":0,"timestamp":2000,"reason":"test"})"); // frame 2
    // Enrichment triggers extract_signals for the violating frame:
    backend->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":350}],"errors":[],"absent":[]})");
    backend->queue_response(R"({"status":"ack"})"); // frame 3
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)client.set_properties(std::span{&prop, 1});
    (void)client.start_stream();

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{2000}, CanId{sid}, dlc, data},
        {Timestamp{3000}, CanId{sid}, dlc, data},
    };

    auto result = client.send_frames(frames);
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

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)client.set_properties(std::span{&prop, 1});
    (void)client.start_stream();

    auto dlc = Dlc::create(8).value();
    auto sid = StandardId::create(0x100).value();
    FramePayload data(8, std::byte{0});
    std::vector<Frame> frames{
        {Timestamp{1000}, CanId{sid}, dlc, data},
        {Timestamp{-1}, CanId{sid}, dlc, data},
    };

    auto result = client.send_frames(frames);
    REQUIRE(result.has_error());
    CHECK(result.error->message().find("non-negative") != std::string::npos);
    REQUIRE(result.responses.size() == 1);
    CHECK(std::holds_alternative<Ack>(result.responses[0]));
}

TEST_CASE("send_frames empty", "[client][batch]") {
    auto backend = std::make_unique<MockBackend>();
    backend->queue_response(R"({"status":"success"})"); // set_properties
    backend->queue_response(R"({"status":"success"})"); // start_stream
    AletheiaClient client(std::move(backend));

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)client.set_properties(std::span{&prop, 1});
    (void)client.start_stream();

    auto result = client.send_frames({});
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

    auto prop = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{300})));
    (void)a.set_properties(std::span{&prop, 1});
    (void)a.start_stream();

    // Target client: separate backend (will be destroyed on assignment).
    auto backend_b = std::make_unique<MockBackend>();
    AletheiaClient b(std::move(backend_b));

    // Move-assign: b takes over a's state.
    b = std::move(a);

    auto id = StandardId::create(0x100).value();
    auto dlc = Dlc::create(8).value();
    std::array<std::byte, 8> data{};
    auto resp = b.send_frame(Timestamp{1000}, CanId{id}, dlc, data);
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
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();

    // Send 257 frames with distinct data payloads to fill and overflow the cache
    for (int i = 0; i < 257; ++i) {
        FramePayload data(8, std::byte{0});
        // Vary first two bytes to make each frame key unique
        data[0] = static_cast<std::byte>(i & 0xFF);
        data[1] = static_cast<std::byte>((i >> 8) & 0xFF);
        auto result =
            client.send_frame(Timestamp{static_cast<std::int64_t>(i) * 1000}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(std::holds_alternative<Ack>(*result));
    }
}

// ===========================================================================
// Property index OOB test (C3): violation with out-of-bounds property_index
// ===========================================================================

TEST_CASE("violation with OOB property_index skips enrichment", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();

    // Queue: set_properties, start_stream, send_frame (violation with index 999)
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "status": "fails", "type": "property",
        "property_index": 999, "timestamp": 1000000,
        "reason": "some reason"
    })");

    AletheiaClient client(std::move(mock));
    // Set only 1 property — index 999 is out of bounds
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{220.0})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<Violation>(*result));
    auto& v = std::get<Violation>(*result);
    CHECK(v.property_index == PropertyIndex{999});
    CHECK(v.reason == "some reason");
    // Enrichment skipped due to OOB property index
    CHECK_FALSE(v.enrichment.has_value());
}

// ===========================================================================
// bytes_to_dlc error paths
// ===========================================================================

TEST_CASE("bytes_to_dlc valid CAN 2.0B sizes", "[types]") {
    auto r7 = bytes_to_dlc(7);
    REQUIRE(r7.has_value());
    CHECK(r7->value() == 7);

    auto r8 = bytes_to_dlc(8);
    REQUIRE(r8.has_value());
    CHECK(r8->value() == 8);
}

TEST_CASE("bytes_to_dlc valid CAN-FD sizes", "[types]") {
    auto r12 = bytes_to_dlc(12);
    REQUIRE(r12.has_value());
    CHECK(r12->value() == 9);

    auto r64 = bytes_to_dlc(64);
    REQUIRE(r64.has_value());
    CHECK(r64->value() == 15);
}

TEST_CASE("bytes_to_dlc invalid sizes return error", "[types]") {
    auto r9 = bytes_to_dlc(9);
    REQUIRE_FALSE(r9.has_value());
    CHECK_THAT(r9.error(), ContainsSubstring("invalid DLC"));

    auto r65 = bytes_to_dlc(65);
    REQUIRE_FALSE(r65.has_value());
    CHECK_THAT(r65.error(), ContainsSubstring("invalid DLC"));
}

// ===========================================================================
// format_formula MetricUntil and MetricRelease
// ===========================================================================

TEST_CASE("format_formula metric until", "[enrich]") {
    using namespace std::chrono_literals;
    auto f = LtlFormula{MetricUntil{.bound = Timestamp{3'000'000},
                                    .left = std::make_unique<LtlFormula>(ltl::atomic(
                                        ltl::less_than(SignalName{"Speed"}, PhysicalValue{50}))),
                                    .right = std::make_unique<LtlFormula>(ltl::atomic(
                                        ltl::equals(SignalName{"Brake"}, PhysicalValue{1})))}};
    CHECK(format_formula(f) == "Speed < 50 until within 3s Brake = 1");
}

TEST_CASE("format_formula metric release", "[enrich]") {
    using namespace std::chrono_literals;
    auto f =
        LtlFormula{MetricRelease{.bound = Timestamp{500'000},
                                 .left = std::make_unique<LtlFormula>(
                                     ltl::atomic(ltl::equals(SignalName{"A"}, PhysicalValue{1}))),
                                 .right = std::make_unique<LtlFormula>(
                                     ltl::atomic(ltl::equals(SignalName{"B"}, PhysicalValue{0})))}};
    CHECK(format_formula(f) == "A = 1 release within 500ms B = 0");
}

// ===========================================================================
// Rational comparison
// ===========================================================================

TEST_CASE("Rational operator<=> and operator==", "[types]") {
    Rational a{1, 2};  // 0.5
    Rational b{2, 4};  // 0.5
    Rational c{3, 4};  // 0.75
    Rational d{-1, 2}; // -0.5

    SECTION("equality") {
        CHECK(a == b);
        CHECK_FALSE(a == c);
    }

    SECTION("less than") {
        CHECK(a < c);
        CHECK(d < a);
        CHECK_FALSE(c < a);
    }

    SECTION("greater than") {
        CHECK(c > a);
        CHECK_FALSE(a > c);
    }

    SECTION("less than or equal") {
        CHECK(a <= b);
        CHECK(a <= c);
        CHECK_FALSE(c <= a);
    }

    SECTION("negative values") {
        Rational neg{-3, 4};
        CHECK(neg < a);
        CHECK(d == Rational{-1, 2});
    }
}

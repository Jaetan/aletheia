// Layer 2: Unit tests with mock backend.
// Tests JSON serialization, parsing, and client round-trips.
#define CATCH_CONFIG_MAIN
#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

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
        .factor = ScaleFactor{0.1},
        .offset = ScaleOffset{0.0},
        .minimum = PhysicalValue{0.0},
        .maximum = PhysicalValue{300.0},
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
    CHECK(sig["factor"] == Catch::Approx(0.1));
    CHECK(sig["offset"] == Catch::Approx(0.0));
    CHECK(sig["minimum"] == Catch::Approx(0.0));
    CHECK(sig["maximum"] == Catch::Approx(300.0));
    CHECK(sig["unit"] == "km/h");
    CHECK(sig["presence"] == "always");
}

TEST_CASE("serialize_extract_signals produces correct JSON", "[json][serialize]") {
    auto id = CanId{StandardId::create(0x100).value()};
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto str = detail::serialize_extract_signals(id, data);
    auto j = json::parse(str);

    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
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
    auto str = detail::serialize_build_frame(id, signals);
    auto j = json::parse(str);

    CHECK(j["command"] == "buildFrame");
    CHECK(j["canId"] == 0x100);
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
    FramePayload data{};
    auto str = detail::serialize_send_frame(Timestamp{1'000'000}, id, data);
    auto j = json::parse(str);

    CHECK(j["type"] == "data");
    CHECK(j["timestamp"] == 1'000'000);
    CHECK(j["id"] == 0x100);
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
        .factor = ScaleFactor{1.0},
        .offset = ScaleOffset{-40.0},
        .minimum = PhysicalValue{-40.0},
        .maximum = PhysicalValue{215.0},
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
        "status": "violation",
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
        "status": "violation",
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
            {"type": "property", "status": "satisfaction", "property_index": 0},
            {"type": "property", "status": "violation", "property_index": 1,
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
    CHECK(result->messages[0].signals[0].factor == ScaleFactor{1.0});
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
    FramePayload data{std::byte{0xE8}, std::byte{0x03}};
    auto result = client.extract_signals(id, data);

    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{120.0});

    auto j = json::parse(mock_ptr->last_captured());
    CHECK(j["command"] == "extractAllSignals");
    CHECK(j["canId"] == 0x100);
}

TEST_CASE("client build_frame round-trip", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success", "data": [232, 3, 0, 0, 0, 0, 0, 0]})");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{100.0}},
    };
    auto result = client.build_frame(id, signals);

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
            {"type": "property", "status": "satisfaction", "property_index": 0}
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
    FramePayload data{};
    auto frame_result = client.send_frame(Timestamp{1'000'000}, id, data);
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
    CHECK(result->messages[0].signals[0].factor == ScaleFactor{0.1});
}

TEST_CASE("client send_frame violation with enrichment fields", "[client][mock]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "status": "violation",
        "type": "property",
        "property_index": {"numerator": 0, "denominator": 1},
        "timestamp": {"numerator": 2000000, "denominator": 1},
        "reason": "Speed limit exceeded"
    })");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    FramePayload data{};
    auto result = client.send_frame(Timestamp{2'000'000}, id, data);

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

// Cross-binding log event vocabulary parity — C++ side.
//
// Reads docs/LOG_EVENTS.yaml and asserts:
//
//   1. The YAML is well-formed (15 entries, each with name + valid level
//      ∈ {debug, info, warn} + non-empty description, no duplicate names).
//   2. Every event captured from a comprehensive workflow against the mock
//      backend is a member of the canonical YAML name set — catches a
//      future binding-side emit-call that drifts from the cross-binding
//      canonical set.
//
// This is the "missing mechanism" half of R18 cluster 10: a structural
// gate mirroring python/tests/test_log_events_parity.py and
// go/aletheia/log_events_test.go.  It was added alongside the surface fix
// of Go's rogue 16th `dbc.text_parsed` event so the same class of drift
// cannot recur silently in any binding.
//
// The workflow exercises:
//   - parse_dbc          (JSON-shape DBC path → dbc.parsed)
//   - parse_dbc_text     (DBC-text parser path → dbc.parsed)
//   - set_properties     (properties.set)
//   - start_stream       (stream.started)
//   - send_frame ack     (frame.processed)
//   - send_frame violate (frame.processed + cache.miss + enrichment.*)
//   - end_stream         (stream.ended)
//
// Events not exercised (require exotic setups; they remain protected by
// the membership assertion against any future drift): rts.cores_mismatch
// (real FFI mismatch only), cache.full (cache capacity bound), error_event.sent
// and remote_event.sent (event-injection paths).
#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#ifndef ALETHEIA_REPO_ROOT
#error "ALETHEIA_REPO_ROOT must be defined at compile time by CMake"
#endif

using namespace aletheia;

namespace {

constexpr std::array<std::string_view, 3> kValidLevels = {"debug", "info", "warn"};

auto repo_root() -> std::filesystem::path {
    return std::filesystem::path{ALETHEIA_REPO_ROOT};
}

auto yaml_path() -> std::filesystem::path {
    return repo_root() / "docs" / "LOG_EVENTS.yaml";
}

struct LogEventRow {
    std::string name;
    std::string level;
    std::string description;
};

auto load_log_events() -> std::vector<LogEventRow> {
    const auto path = yaml_path();
    REQUIRE(std::filesystem::exists(path));
    auto root = YAML::LoadFile(path.string());
    REQUIRE(root["events"]);
    REQUIRE(root["events"].IsSequence());

    std::vector<LogEventRow> out;
    out.reserve(root["events"].size());
    for (const auto& node : root["events"]) {
        out.push_back(LogEventRow{
            .name = node["name"].as<std::string>(),
            .level = node["level"].as<std::string>(),
            .description = node["description"].as<std::string>(),
        });
    }
    return out;
}

auto canonical_event_set() -> std::set<std::string> {
    auto rows = load_log_events();
    std::set<std::string> set;
    for (auto& row : rows)
        set.insert(std::move(row.name));
    return set;
}

} // namespace

// ----- 1. YAML schema sanity -----

TEST_CASE("LOG_EVENTS.yaml is well-formed", "[parity][log][yaml]") {
    auto rows = load_log_events();
    REQUIRE(rows.size() == 15);

    std::set<std::string> seen;
    for (size_t i = 0; i < rows.size(); ++i) {
        const auto& row = rows[i];
        INFO("events[" << i << "] name=" << row.name);

        CHECK_FALSE(row.name.empty());
        CHECK(row.name.find('.') != std::string::npos);
        CHECK(seen.insert(row.name).second);

        const bool level_valid =
            std::find(kValidLevels.begin(), kValidLevels.end(), row.level) != kValidLevels.end();
        CHECK(level_valid);

        CHECK_FALSE(row.description.empty());
    }
}

// ----- 2. comprehensive workflow ⊆ canonical set -----

namespace {

constexpr std::string_view kDbcSourceText = R"DBC(VERSION ""
NS_ :
BS_:
BU_: ECU
BO_ 256 EngineData: 8 ECU
 SG_ Speed : 0|16@1+ (1,0) [0|300] "kph" Vector__XXX

)DBC";

// Mock JSON for parse_dbc / parse_dbc_text — minimal shape that matches
// the wire contract enforced by detail::parse_parsed_dbc.
constexpr std::string_view kParseDbcResponse = R"JSON({
    "status": "success",
    "dbc": {
        "version": "1.0",
        "messages": [{
            "id": 256, "extended": false, "name": "EngineData", "dlc": 8,
            "sender": "ECU",
            "signals": [{
                "name": "Speed", "startBit": 0, "length": 16,
                "byteOrder": "little_endian", "signed": false,
                "factor": {"numerator": 1, "denominator": 1},
                "offset": {"numerator": 0, "denominator": 1},
                "minimum": {"numerator": 0, "denominator": 1},
                "maximum": {"numerator": 300, "denominator": 1},
                "unit": "kph",
                "presence": "always",
                "valueDescriptions": []
            }]
        }]
    }
})JSON";

} // namespace

TEST_CASE("emitted events are subset of LOG_EVENTS.yaml", "[parity][log][workflow]") {
    auto known = canonical_event_set();

    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // Queue: parse_dbc, parse_dbc_text, set_properties, start_stream,
    //        send_frame (ack), send_frame (violation),
    //        enrichment extraction (success), end_stream, EOS extraction.
    mock_ptr->queue_response(std::string{kParseDbcResponse});
    mock_ptr->queue_response(std::string{kParseDbcResponse});
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "ack"})");
    mock_ptr->queue_response(
        R"({"status":"fails","type":"property","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"})");
    mock_ptr->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]})");
    mock_ptr->queue_response(R"({
        "status":"complete",
        "results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}]
    })");
    mock_ptr->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]})");

    std::vector<std::string> captured;
    Logger logger([&](const LogRecord& r) { captured.emplace_back(r.event); });

    AletheiaClient client(std::move(mock), logger);

    // 1. parse_dbc (JSON path)
    DbcDefinition dbc{.version = "1.0"};
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    // 2. parse_dbc_text (DBC-text path — was the divergent path in Go)
    REQUIRE(client.parse_dbc_text(std::stop_token{}, kDbcSourceText).has_value());

    // 3. set_properties
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());

    // 4. start_stream
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();

    // 5. send_frame ack
    FramePayload data_ack(8, std::byte{0});
    REQUIRE(
        client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data_ack).has_value());

    // 6. send_frame violation triggers enrichment
    FramePayload data_violate(8, std::byte{0});
    data_violate[0] = std::byte{0xFF};
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{5'000'000}, id, dlc, data_violate)
                .has_value());

    // 7. end_stream
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    REQUIRE_FALSE(captured.empty());

    // Core assertion: every captured event is in the canonical YAML set.
    // A future emit-site drift fails this check loudly with the offending name.
    std::set<std::string> unique_emitted;
    for (const auto& e : captured)
        unique_emitted.insert(e);

    for (const auto& event : unique_emitted) {
        INFO("emitted event: " << event);
        const bool in_canonical = known.contains(event);
        CHECK(in_canonical);
    }

    // Sanity floor: dbc.parsed MUST be exercised — that's the path that
    // drifted; without this the gate is silently weakened.
    CHECK(unique_emitted.contains("dbc.parsed"));
}

// Unit test of the gate's rejection logic: confirms the canonical set
// does NOT contain the rogue dbc.text_parsed event.  This is independent
// of any binding workflow, so we know the membership check would have
// caught the original R18 drift even if a future workflow change ever
// stopped exercising parse_dbc_text.
TEST_CASE("LOG_EVENTS.yaml rejects the known R18 drift event", "[parity][log][regression]") {
    auto known = canonical_event_set();
    CHECK_FALSE(known.contains("dbc.text_parsed"));
    CHECK(known.contains("dbc.parsed"));
}

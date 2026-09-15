// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Cross-binding log event vocabulary parity — C++ side.
//
// Reads docs/LOG_EVENTS.yaml and asserts:
//
//   1. The YAML is well-formed (16 entries, each with name + valid level
//      ∈ {debug, info, warn} + non-empty description, no duplicate names).
//   2. Every event captured from a comprehensive workflow against the mock
//      backend is a member of the canonical YAML name set — catches a
//      future binding-side emit-call that drifts from the cross-binding
//      canonical set.
//
// This is the mechanism half of the log-events parity gate, mirroring
// python/tests/test_log_events_parity.py and go/aletheia/log_events_test.go:
// a binding that grows an emit call outside the canonical set fails here
// rather than drifting silently.
//
// The workflow exercises:
//   - parse_dbc          (JSON-shape DBC path → dbc.parsed)
//   - parse_dbc_text     (DBC-text parser path → dbc.parsed)
//   - set_properties     (properties.set)
//   - start_stream       (stream.started)
//   - send_frame ack     (frame.processed)
//   - send_frame violate (frame.processed + cache.miss + enrichment.*)
//   - end_stream         (stream.ended + endstream.uncached_atom per warning)
//
// Events not exercised (require exotic setups; they remain protected by
// the membership assertion against any future drift): rts.cores_mismatch
// (real FFI mismatch only), cache.full (cache capacity bound), error_event.sent
// and remote_event.sent (event-injection paths).
#include <catch2/catch_test_macros.hpp>
#include <cstddef>
#include <yaml-cpp/yaml.h>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>
#include <catch2/catch_message.hpp>

#include <algorithm>
#include <array>
#include <cstdlib>
#include <filesystem>
#include <memory>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "repo_root.hpp"

using aletheia::test::repo_root;

using namespace aletheia;

constexpr std::array<std::string_view, 3> k_valid_levels = {"debug", "info", "warn"};

static auto yaml_path() -> std::filesystem::path {
    return repo_root() / "docs" / "LOG_EVENTS.yaml";
}

namespace {
struct LogEventRow {
    std::string name;
    std::string level;
    std::string description;
};
} // namespace

static auto load_log_events() -> std::vector<LogEventRow> {
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

static auto canonical_event_set() -> std::set<std::string> {
    auto rows = load_log_events();
    std::set<std::string> set;
    for (auto& row : rows)
        set.insert(std::move(row.name));
    return set;
}

// ----- 1. YAML schema sanity -----

TEST_CASE("LOG_EVENTS.yaml is well-formed", "[parity][log][yaml]") {
    auto rows = load_log_events();
    REQUIRE(rows.size() == 16);

    std::set<std::string> seen;
    for (size_t i = 0; i < rows.size(); ++i) {
        const auto& row = rows[i];
        INFO("events[" << i << "] name=" << row.name);

        CHECK_FALSE(row.name.empty());
        CHECK(row.name.contains('.'));
        CHECK(seen.insert(row.name).second);

        CHECK(std::ranges::contains(k_valid_levels, row.level));

        CHECK_FALSE(row.description.empty());
    }
}

// ----- 2. comprehensive workflow ⊆ canonical set -----

constexpr std::string_view k_dbc_source_text = R"DBC(VERSION ""
NS_ :
BS_:
BU_: ECU
BO_ 256 EngineData: 8 ECU
 SG_ Speed : 0|16@1+ (1,0) [0|300] "kph" Vector__XXX

)DBC";

// Mock JSON for parse_dbc / parse_dbc_text — minimal shape that matches
// the wire contract enforced by detail::parse_parsed_dbc.
constexpr std::string_view k_parse_dbc_response = R"JSON({
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

// Drive one full client workflow against a queued mock and return the set of
// log events it emitted, so the checks below read as claims about that set
// rather than as a script.
static auto events_of_one_workflow() -> std::set<std::string> {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    // Queue: parse_dbc, parse_dbc_text, set_properties, start_stream,
    //        send_frame (ack), send_frame (violation),
    //        enrichment extraction (success), end_stream, EOS extraction.
    mock_ptr->queue_response(std::string{k_parse_dbc_response});
    mock_ptr->queue_response(std::string{k_parse_dbc_response});
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({"status": "ack"})");
    mock_ptr->queue_response(
        R"({"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}]})");
    mock_ptr->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]})");
    mock_ptr->queue_response(R"({
        "status":"complete",
        "results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}],
        "warnings":[{"kind":"uncached_atom","property_index":0,"detail":"UnobservedSignal"}]
    })");
    mock_ptr->queue_response(
        R"({"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]})");

    std::vector<std::string> captured;
    const Logger logger([&](const LogRecord& r) { captured.emplace_back(r.event); });

    AletheiaClient client(std::move(mock), logger);

    // 1. parse_dbc (JSON path)
    const DbcDefinition dbc{.version = "1.0"};
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    // 2. parse_dbc_text (the DBC-text path, which emits dbc.parsed too)
    REQUIRE(client.parse_dbc_text(std::stop_token{}, k_dbc_source_text).has_value());

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

    std::set<std::string> unique_emitted;
    for (const auto& e : captured)
        unique_emitted.insert(e);
    return unique_emitted;
}

TEST_CASE("emitted events are subset of LOG_EVENTS.yaml", "[parity][log][workflow]") {
    auto known = canonical_event_set();

    const auto unique_emitted = events_of_one_workflow();

    // Core assertion: every emitted event is in the canonical YAML set.
    // A future emit-site drift fails this check loudly with the offending name.
    for (const auto& event : unique_emitted) {
        INFO("emitted event: " << event);
        const bool in_canonical = known.contains(event);
        CHECK(in_canonical);
    }

    // Sanity floor: dbc.parsed must be exercised. Without it a workflow that
    // stopped reaching the parse paths would leave the gate asserting nothing
    // about them.
    CHECK(unique_emitted.contains("dbc.parsed"));

    // Sanity floor: the EndStream Complete carries an uncached_atom warning,
    // so the per-warning event MUST fire — otherwise a future refactor that
    // drops the emit site would slip past this gate.
    CHECK(unique_emitted.contains("endstream.uncached_atom"));
}

// The gate's rejection logic on its own, independent of any workflow: the
// canonical set must not contain dbc.text_parsed, because the text path emits
// dbc.parsed like the JSON path and a separate name for it would be an event
// one binding has and the others do not.
TEST_CASE("LOG_EVENTS.yaml rejects the known drift event", "[parity][log][regression]") {
    auto known = canonical_event_set();
    CHECK_FALSE(known.contains("dbc.text_parsed"));
    CHECK(known.contains("dbc.parsed"));
}

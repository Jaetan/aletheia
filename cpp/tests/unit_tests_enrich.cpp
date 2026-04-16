// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: violation enrichment, collect_signals, build_diagnostic, core-reason,
// last-known values, and OOB property_index handling.
//
// Covers the enrichment pipeline: auto-derived diagnostics from set_properties,
// extraction caching across repeated frames, end-of-stream enrichment via
// last-frame tracking, core_reason propagation from the backend, and the
// defensive path where a backend returns a property_index outside the caller's
// property list.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <nlohmann/json.hpp>

#include <cstddef>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using json = nlohmann::json;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Signal collection tests
// ===========================================================================

TEST_CASE("collect_signals multi-signal", "[enrich]") {
    auto f = ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
                       ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    auto signals = collect_signals(f);
    REQUIRE(signals.size() == 2);
    CHECK(signals[0] == SignalName{"Speed"});
    CHECK(signals[1] == SignalName{"RPM"});
}

TEST_CASE("collect_signals dedup", "[enrich]") {
    auto f = ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
                       ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{}})));
    auto signals = collect_signals(f);
    CHECK(signals.size() == 1);
    CHECK(signals[0] == SignalName{"Speed"});
}

TEST_CASE("build_diagnostic always succeeds", "[enrich]") {
    auto f = ltl::always(
        ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
                  ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}}))));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
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
    CHECK(v.enrichment->signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{245, 1}});
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
        ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
                  ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}}))));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
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
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
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
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
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
    CHECK(enrichment.signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{245, 1}});
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK(enrichment.core_reason == "MetricEventually: window expired");
    CHECK_THAT(enrichment.enriched_reason,
               ContainsSubstring("[core: MetricEventually: window expired]"));
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
        ltl::eventually(ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
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
    CHECK(enrichment.signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{150, 1}});
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Speed = 150"));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
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

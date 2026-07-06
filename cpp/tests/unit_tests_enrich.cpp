// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
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

#include <cstddef>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Signal collection tests
// ===========================================================================

TEST_CASE("collect_signals multi-signal", "[enrich]") {
    auto f = ltl::both(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}})));
    auto signals = collect_signals(f);
    REQUIRE(signals.size() == 2);
    CHECK(signals[0] == SignalName{"Speed"});
    CHECK(signals[1] == SignalName{"RPM"});
}

TEST_CASE("collect_signals dedup", "[enrich]") {
    auto f =
        ltl::both(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
                  ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{}})));
    auto signals = collect_signals(f);
    CHECK(signals.size() == 1);
    CHECK(signals[0] == SignalName{"Speed"});
}

TEST_CASE("build_diagnostic always succeeds", "[enrich]") {
    auto f = ltl::always(ltl::both(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
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
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());

    // Verify by triggering enrichment: start_stream, send_frame (violation), extraction
    mock_ptr->queue_response(R"({"status": "success"})");
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 2000000,
                    "reason": "Atomic: predicate failed"
        }]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0x00}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));

    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    REQUIRE(v->enrichment.has_value());
    CHECK_THAT(v->enrichment->formula_desc, ContainsSubstring("Speed < 220"));
    CHECK_THAT(v->enrichment->enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK_THAT(v->enrichment->enriched_reason, ContainsSubstring("formula:"));
    CHECK(v->enrichment->signals.size() == 1);
    CHECK(v->enrichment->signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{245, 1}});
    CHECK(v->enrichment->core_reason == "Atomic: predicate failed");
    CHECK_THAT(v->enrichment->enriched_reason,
               ContainsSubstring("[core: Atomic: predicate failed]"));
}

TEST_CASE("send_frame enrichment renders the observed value exactly (kernel formatℚ)",
          "[client][enrich]") {
    // r25 B5a: the observed value renders via the kernel formatℚ (the renderer
    // the predicate threshold already uses), not lossy %g/to_double(). 740/3 is
    // non-terminating: old `{:g}` gave "246.667"; formatℚ gives the exact "740/3".
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{"status": "fails", "type": "property",
                     "property_index": 0, "timestamp": 2000000}]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": {"numerator": 740, "denominator": 3}}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0}, std::byte{0}, std::byte{0}, std::byte{0}};
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));
    auto* v = std::get<PropertyBatch>(*result).first_violation();
    REQUIRE(v != nullptr);
    REQUIRE(v->enrichment.has_value());
    CHECK_THAT(v->enrichment->enriched_reason, ContainsSubstring("Speed = 740/3"));
    CHECK_THAT(v->enrichment->enriched_reason, !ContainsSubstring("246.667"));
}

TEST_CASE("send_frame multi-signal enrichment", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 2000000
        }]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}, {"name": "RPM", "value": 3000}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(ltl::both(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})),
        ltl::atomic(ltl::greater_than(SignalName{"RPM"}, PhysicalValue{Rational{500, 1}}))));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(result.has_value());
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    REQUIRE(v->enrichment.has_value());
    CHECK(v->enrichment->signals.size() == 2);
    CHECK_THAT(v->enrichment->enriched_reason, ContainsSubstring("Speed = 245"));
    CHECK_THAT(v->enrichment->enriched_reason, ContainsSubstring("RPM = 3000"));
}

TEST_CASE("extraction caching: same frame extracts once", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    // Two violations, same frame — only one extraction
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 1000000
        }]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 2000000
        }]
    })");
    // No second extraction response needed — cached

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    auto r1 = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r1.has_value());
    CHECK(std::get<PropertyBatch>(*r1).first_violation()->enrichment.has_value());

    auto r2 = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(r2.has_value());
    CHECK(std::get<PropertyBatch>(*r2).first_violation()->enrichment.has_value());

    // Count extractAllSignals commands (should be exactly 1)
    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        if (captured == "<binary:extractAllSignals>")
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
    // EOS enrichment: merge_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Mode", "value": 0}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
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

TEST_CASE("end_stream surfaces uncached_atom warnings", "[client][warnings]") {
    // R21 cluster 1 — AGDA-D-12.1: kernel emits one `uncached_atom`
    // warning per atom whose target signal never appeared in trace.
    // Verifies the C++ binding decodes these into StreamResult::warnings.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "unresolved", "property_index": 0,
             "reason": "Atomic: predicate never resolved at end of stream"}
        ],
        "warnings": [
            {"kind": "uncached_atom", "property_index": 0, "detail": "UnobservedSignal"}
        ]
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(ltl::atomic(
        ltl::less_than(SignalName{"UnobservedSignal"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->warnings.size() == 1);
    CHECK(end_result->warnings[0].kind == "uncached_atom");
    CHECK(end_result->warnings[0].property_index.get() == 0);
    CHECK(end_result->warnings[0].detail == "UnobservedSignal");
}

TEST_CASE("start_stream clears extraction cache", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 1000000
        }]
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
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 1000000
        }]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 250}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    auto r1 = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r1.has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    // Second stream: same frame data but cache cleared
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto r2 = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r2.has_value());
    CHECK(std::get<PropertyBatch>(*r2).first_violation()->enrichment.has_value());

    // Should have 2 extractAllSignals calls (cache was cleared)
    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        if (captured == "<binary:extractAllSignals>")
            ++extract_count;
    }
    CHECK(extract_count == 2);
}

TEST_CASE("no enrichment without set_properties", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 2000000,
                    "reason": "Speed limit exceeded"
        }]
    })");

    AletheiaClient client(std::move(mock));
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK_FALSE(v->enrichment.has_value());
}

// ===========================================================================
// CoreReason enrichment tests
// ===========================================================================

TEST_CASE("violation enrichment omits core_reason when empty", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 2000000
        }]
    })");
    mock->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    REQUIRE(v->enrichment.has_value());
    CHECK(v->enrichment->core_reason.empty());
    // enriched_reason should NOT contain "[core:" when reason is empty
    CHECK_THAT(v->enrichment->enriched_reason, !ContainsSubstring("[core:"));
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
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 1000000,
                    "reason": "Atomic: predicate failed"
        }]
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
    // EOS enrichment: merge_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xF5}, std::byte{0}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0}, std::byte{0}, std::byte{0}};
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
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
    // EOS enrichment: merge_last_known_values re-extracts from last frame
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 150}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    auto formula = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Speed"}, PhysicalValue{Rational{300, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // Send a frame that gets ack (no violation, so no extraction cache entry)
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto frame_result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(frame_result.has_value());
    CHECK(std::holds_alternative<Ack>(*frame_result));

    auto end_result = client.end_stream(std::stop_token{});
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
// Extract-once EOS enrichment: one extraction per tracked frame
// ===========================================================================

TEST_CASE("end_stream extracts each tracked frame once across properties", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    // End stream: two properties fail/unresolve, sharing the one tracked frame.
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "Never satisfied"},
            {"type": "property", "status": "unresolved", "property_index": 1,
             "reason": "Atomic: predicate never resolved at end of stream"}
        ]
    })");
    // ONE extraction of the single tracked frame serves BOTH properties —
    // the full-frame result is merged once and distributed per diagnostic.
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "Mode", "value": 0}, {"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    // One extraction per tracked frame (1), not per property × frame (2).
    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        if (captured == "<binary:extractAllSignals>")
            ++extract_count;
    }
    CHECK(extract_count == 1);

    // Distribution filters the merged map down to each property's own signals.
    REQUIRE(end_result->results[0].enrichment.has_value());
    CHECK(end_result->results[0].enrichment->signals.size() == 1);
    CHECK(end_result->results[0].enrichment->signals.at(SignalName{"Mode"}) ==
          PhysicalValue{Rational{0, 1}});
    CHECK_THAT(end_result->results[0].enrichment->enriched_reason, ContainsSubstring("Mode = 0"));
    REQUIRE(end_result->results[1].enrichment.has_value());
    CHECK(end_result->results[1].enrichment->signals.size() == 1);
    CHECK(end_result->results[1].enrichment->signals.at(SignalName{"Speed"}) ==
          PhysicalValue{Rational{245, 1}});
    CHECK_THAT(end_result->results[1].enrichment->enriched_reason,
               ContainsSubstring("Speed = 245"));
}

TEST_CASE("end_stream with no tracked frames attaches fallback enrichment without extraction",
          "[client][enrich]") {
    // Zero extraction FFI calls when there is nothing to extract, yet the
    // enrichment must STILL be attached to every Fails/Unresolved result via
    // the empty-values fallback reason. (The union-empty skip guard has the
    // same observable contract — 0 extractions + attach-always — and is not
    // separately reachable through the public API: every LtlFormula leaf
    // carries a signal name, so a collected diagnostic always wants ≥ 1
    // signal.)
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "Never satisfied"}
        ]
    })");
    // Deliberately NO extraction response queued — none may be consumed.

    AletheiaClient client(std::move(mock));
    auto formula = ltl::eventually(
        ltl::atomic(ltl::equals(SignalName{"Mode"}, PhysicalValue{Rational{1, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // No frames sent — last-frame tracking stays empty.
    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 1);

    std::size_t extract_count = 0;
    for (const auto& captured : mock_ptr->captured()) {
        if (captured == "<binary:extractAllSignals>")
            ++extract_count;
    }
    CHECK(extract_count == 0);

    REQUIRE(end_result->results[0].enrichment.has_value());
    const auto& enrichment = *end_result->results[0].enrichment;
    CHECK(enrichment.signals.empty());
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("violated:"));
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Mode = 1"));
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("[core: Never satisfied]"));
    CHECK(enrichment.core_reason == "Never satisfied");
}

// ===========================================================================
// Extract-once EOS enrichment: adversarial-review pins (frame-loop shape)
// ===========================================================================

namespace {

// One sentinel per logical full-frame extraction — the FFI-call cardinality
// the extract-once shape pins (idiom of the counting loops above).
auto count_extraction_sentinels(const MockBackend& mock) -> std::size_t {
    std::size_t count = 0;
    for (const auto& captured : mock.captured())
        if (captured == "<binary:extractAllSignals>")
            ++count;
    return count;
}

// Occurrences of a named log event in a (level, event) capture — the Logger
// callback idiom from unit_tests_log.cpp.
auto count_log_event(const std::vector<std::pair<LogLevel, std::string>>& events,
                     std::string_view name) -> std::size_t {
    std::size_t count = 0;
    for (const auto& [level, event] : events)
        if (event == name)
            ++count;
    return count;
}

// Two properties over distinct signals, so the EOS wanted-signal union is
// {SigA, SigB} (mirrors the Python/Go extract-once suites).
auto two_signal_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigA"}, PhysicalValue{Rational{10, 1}}))));
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigB"}, PhysicalValue{Rational{10, 1}}))));
    return props;
}

} // namespace

TEST_CASE("end_stream with all properties holding makes zero extraction calls",
          "[client][enrich]") {
    // All-Holds finalization with a tracked frame: collect_enrichable_results
    // comes back empty, so the frame loop never runs — 0 extraction sentinels
    // and no enrichment attached to any result.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame (tracked)
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "holds", "property_index": 0},
            {"type": "property", "status": "holds", "property_index": 1}
        ]
    })");
    // Deliberately NO extraction response queued — none may be consumed.

    AletheiaClient client(std::move(mock));
    REQUIRE(client.set_properties(std::stop_token{}, two_signal_properties()).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_extraction_sentinels(*mock_ptr) == 0);
    CHECK_FALSE(end_result->results[0].enrichment.has_value());
    CHECK_FALSE(end_result->results[1].enrichment.has_value());
}

TEST_CASE("end_stream frame loop breaks early once the wanted union is covered",
          "[client][enrich]") {
    // EARLY-BREAK discriminator: two tracked frames (0x100, 0x200), and the
    // first frame's extraction already covers the whole wanted union
    // {SigA, SigB} — so the loop must stop after ONE extraction. Deleting the
    // `if (remaining.empty()) break;` line in merge_last_known_values makes
    // the loop extract frame 0x200 too (2 sentinels) and fails this test.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame 0x100
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame 0x200
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "eventually unmet"},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "eventually unmet"}
        ]
    })");
    // Frame 0x100 (lowest CAN id, extracted first) covers the union.
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "SigA", "value": 5}, {"name": "SigB", "value": 7}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    REQUIRE(client.set_properties(std::stop_token{}, two_signal_properties()).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto id1 = CanId{StandardId::create(0x100).value()};
    auto id2 = CanId{StandardId::create(0x200).value()};
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id1, dlc, data).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id2, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_extraction_sentinels(*mock_ptr) == 1);
    REQUIRE(end_result->results[0].enrichment.has_value());
    CHECK(end_result->results[0].enrichment->signals.at(SignalName{"SigA"}) ==
          PhysicalValue{Rational{5, 1}});
    REQUIRE(end_result->results[1].enrichment.has_value());
    CHECK(end_result->results[1].enrichment->signals.at(SignalName{"SigB"}) ==
          PhysicalValue{Rational{7, 1}});
}

TEST_CASE("end_stream merge is first-frame-wins across tracked frames", "[client][enrich]") {
    // FIRST-FRAME-WINS discriminator. Frame 0x100 (lower CAN id, so extracted
    // first in the (CAN id value, extended) map order) reports SigA=1; frame
    // 0x200 reports SigA=2 AND SigB=3. The union is {SigA, SigB} and SigB is
    // still missing after frame 0x100, so the early break does NOT fire and
    // both frames are extracted (2 sentinels). The merge keeps SigA=1 from
    // the first frame — an overwrite/last-wins merge would surface SigA=2 —
    // while SigB=3 arrives from frame 0x200.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame 0x100
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame 0x200
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "eventually unmet"},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "eventually unmet"}
        ]
    })");
    // EOS extraction, frame 0x100 (first).
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "SigA", "value": 1}],
        "errors": [], "absent": []
    })");
    // EOS extraction, frame 0x200 (second — its SigA must lose the merge).
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "SigA", "value": 2}, {"name": "SigB", "value": 3}],
        "errors": [], "absent": []
    })");

    AletheiaClient client(std::move(mock));
    REQUIRE(client.set_properties(std::stop_token{}, two_signal_properties()).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto id1 = CanId{StandardId::create(0x100).value()};
    auto id2 = CanId{StandardId::create(0x200).value()};
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id1, dlc, data).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id2, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_extraction_sentinels(*mock_ptr) == 2);
    REQUIRE(end_result->results[0].enrichment.has_value());
    // First frame wins: SigA = 1. A last-wins merge would yield SigA = 2.
    CHECK(end_result->results[0].enrichment->signals.at(SignalName{"SigA"}) ==
          PhysicalValue{Rational{1, 1}});
    REQUIRE(end_result->results[1].enrichment.has_value());
    CHECK(end_result->results[1].enrichment->signals.at(SignalName{"SigB"}) ==
          PhysicalValue{Rational{3, 1}});
}

TEST_CASE("end_stream failed extraction warns once per frame, not per property",
          "[client][enrich]") {
    // Two failing properties share ONE tracked frame whose extraction fails
    // (the queued extraction response is an error — the mock's unqueued
    // default is a success, so the failure must be explicit). The shared
    // frame loop attempts the frame once (1 sentinel) and emits ONE
    // enrichment.extraction_failed warning — the old P-outer shape warned
    // once per property (twice here). Both entries still get the
    // empty-values fallback enrichment.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "eventually unmet"},
            {"type": "property", "status": "fails", "property_index": 1,
             "timestamp": 5000000, "reason": "eventually unmet"}
        ]
    })");
    // EOS extraction fails.
    mock_ptr->queue_response(R"({"status": "error", "code": "decode_error", "message": "boom"})");

    std::vector<std::pair<LogLevel, std::string>> events;
    Logger logger([&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });
    AletheiaClient client(std::move(mock), logger);

    REQUIRE(client.set_properties(std::stop_token{}, two_signal_properties()).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_extraction_sentinels(*mock_ptr) == 1);
    CHECK(count_log_event(events, "enrichment.extraction_failed") == 1);

    for (const auto& pr : end_result->results) {
        REQUIRE(pr.enrichment.has_value());
        CHECK(pr.enrichment->signals.empty());
        CHECK_THAT(pr.enrichment->enriched_reason, ContainsSubstring("violated:"));
        CHECK_THAT(pr.enrichment->enriched_reason, ContainsSubstring("[core: eventually unmet]"));
    }
}

TEST_CASE("end_stream OOB property_index is excluded while the valid entry is still enriched",
          "[client][enrich]") {
    // Finalization batch [index 0 valid Fails, index 7 OOB Fails] against a
    // single registered property: exactly one enrichment.property_index_oob
    // warning, the OOB entry gets NO enrichment, the valid entry is enriched,
    // and the sentinel count reflects the valid entry's extraction only.
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();

    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [
            {"type": "property", "status": "fails", "property_index": 0,
             "timestamp": 5000000, "reason": "eventually unmet"},
            {"type": "property", "status": "fails", "property_index": 7,
             "timestamp": 5000000, "reason": "eventually unmet"}
        ]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "SigA", "value": 5}],
        "errors": [], "absent": []
    })");

    std::vector<std::pair<LogLevel, std::string>> events;
    Logger logger([&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });
    AletheiaClient client(std::move(mock), logger);

    // Only ONE property registered — index 7 is out of bounds.
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigA"}, PhysicalValue{Rational{10, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_log_event(events, "enrichment.property_index_oob") == 1);
    CHECK(count_extraction_sentinels(*mock_ptr) == 1);

    REQUIRE(end_result->results[0].enrichment.has_value());
    CHECK(end_result->results[0].enrichment->signals.at(SignalName{"SigA"}) ==
          PhysicalValue{Rational{5, 1}});
    CHECK_FALSE(end_result->results[1].enrichment.has_value());
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
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 999, "timestamp": 1000000,
                    "reason": "some reason"
        }]
    })");

    AletheiaClient client(std::move(mock));
    // Set only 1 property — index 999 is out of bounds
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{999});
    CHECK(v->reason == "some reason");
    // Enrichment skipped due to OOB property index
    CHECK_FALSE(v->enrichment.has_value());
}

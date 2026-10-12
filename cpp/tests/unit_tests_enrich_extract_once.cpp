// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: end-of-stream enrichment extracting each tracked frame once,
// and a violation whose property index is out of the caller's range.
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/mock_backend.hpp"
#include "enrich_sentinels.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <algorithm>
#include <cstddef>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using aletheia::test::count_extraction_sentinels;
using Catch::Matchers::ContainsSubstring;

// Occurrences of a named log event in a captured level-and-event sequence.
static auto count_log_event(const std::vector<std::pair<LogLevel, std::string>>& events,
                            std::string_view name) -> std::size_t {
    return static_cast<std::size_t>(
        std::ranges::count_if(events, [name](auto const& e) { return e.second == name; }));
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

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    // One extraction per tracked frame (1), not per property × frame (2).
    auto const extract_count = count_extraction_sentinels(*mock_ptr);
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

    auto const extract_count = count_extraction_sentinels(*mock_ptr);
    CHECK(extract_count == 0);

    REQUIRE(end_result->results[0].enrichment.has_value());
    auto const& enrichment = *end_result->results[0].enrichment;
    CHECK(enrichment.signals.empty());
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("violated:"));
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("Mode = 1"));
    CHECK_THAT(enrichment.enriched_reason, ContainsSubstring("[core: Never satisfied]"));
    CHECK(enrichment.core_reason == "Never satisfied");
}

// ===========================================================================
// Extract-once end-of-stream enrichment: the frame-loop's shape
// ===========================================================================

// Two properties over distinct signals, so the EOS wanted-signal union is
// {SigA, SigB} (mirrors the Python/Go extract-once suites).
static auto two_signal_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigA"}, PhysicalValue{Rational{10, 1}}))));
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigB"}, PhysicalValue{Rational{10, 1}}))));
    return props;
}

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

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
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

    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto const id1 = CanId{StandardId::create(0x100).value()};
    auto const id2 = CanId{StandardId::create(0x200).value()};
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

    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto const id1 = CanId{StandardId::create(0x100).value()};
    auto const id2 = CanId{StandardId::create(0x200).value()};
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
    const Logger logger(
        [&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });
    AletheiaClient client(std::move(mock), logger);

    REQUIRE(client.set_properties(std::stop_token{}, two_signal_properties()).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data).has_value());

    auto end_result = client.end_stream(std::stop_token{});
    REQUIRE(end_result.has_value());
    REQUIRE(end_result->results.size() == 2);

    CHECK(count_extraction_sentinels(*mock_ptr) == 1);
    CHECK(count_log_event(events, "enrichment.extraction_failed") == 1);

    for (auto const& pr : end_result->results) {
        REQUIRE(pr.enrichment.has_value());
        CHECK(pr.enrichment->signals.empty());
        CHECK_THAT(pr.enrichment->enriched_reason, ContainsSubstring("violated:"));
        CHECK_THAT(pr.enrichment->enriched_reason, ContainsSubstring("[core: eventually unmet]"));
    }
}

TEST_CASE("end_stream OOB property_index is excluded while the valid entry is still enriched",
          "[client][enrich]") {
    // Finalization batch [index 0 valid Fails, an OOB Fails] against a
    // single registered property: exactly one enrichment.property_index_oob
    // warning, the OOB entry gets NO enrichment, the valid entry is enriched,
    // and the sentinel count reflects the valid entry's extraction only. The
    // first OOB index is the count itself, the boundary the check draws.
    auto const oob = GENERATE(1, 7);
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
            {"type": "property", "status": "fails", "property_index": )" +
                             std::to_string(oob) + R"(,
             "timestamp": 5000000, "reason": "eventually unmet"}
        ]
    })");
    mock_ptr->queue_response(R"({
        "status": "success",
        "values": [{"name": "SigA", "value": 5}],
        "errors": [], "absent": []
    })");

    std::vector<std::pair<LogLevel, std::string>> events;
    const Logger logger(
        [&](const LogRecord& r) { events.emplace_back(r.level, std::string{r.event}); });
    AletheiaClient client(std::move(mock), logger);

    // Only ONE property registered — index 7 is out of bounds.
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"SigA"}, PhysicalValue{Rational{10, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
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
// A violation whose property index is out of the caller's range
// ===========================================================================

TEST_CASE("violation with OOB property_index skips enrichment", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();

    // Queue: set_properties, start_stream, send_frame (violation with an index
    // past the one property: the count itself, or far past it)
    auto const oob = GENERATE(std::size_t{1}, std::size_t{999});
    mock->queue_response(R"({"status": "success"})"); // set_properties
    mock->queue_response(R"({"status": "success"})"); // start_stream
    mock->queue_response(R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": )" +
                         std::to_string(oob) + R"(, "timestamp": 1000000,
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

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    auto result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);

    REQUIRE(result.has_value());
    REQUIRE(std::holds_alternative<PropertyBatch>(*result));
    auto& b = std::get<PropertyBatch>(*result);
    auto* v = b.first_violation();
    REQUIRE(v != nullptr);
    CHECK(v->property_index == PropertyIndex{oob});
    CHECK(v->reason == "some reason");
    // Enrichment skipped due to OOB property index
    CHECK_FALSE(v->enrichment.has_value());
}

TEST_CASE("set_properties replaces the diagnostics and forgets cached extractions",
          "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    const std::string violation = R"({
        "type": "property_batch",
        "results": [{
            "status": "fails", "type": "property",
                    "property_index": 0, "timestamp": 1000000
        }]
    })";
    const std::string extraction = R"({
        "status": "success",
        "values": [{"name": "Speed", "value": 245}],
        "errors": [], "absent": []
    })";
    mock_ptr->queue_response(violation);
    mock_ptr->queue_response(extraction);
    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties again
    mock_ptr->queue_response(violation);
    mock_ptr->queue_response(extraction);

    AletheiaClient client(std::move(mock));
    std::vector<LtlFormula> first;
    first.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, first).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload data(8, std::byte{0});
    auto const r1 = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(r1.has_value());
    auto const* v1 = std::get<PropertyBatch>(*r1).first_violation();
    REQUIRE(v1 != nullptr);
    REQUIRE(v1->enrichment.has_value());
    CHECK_THAT(v1->enrichment->formula_desc, ContainsSubstring("Speed"));

    // The same frame under a new property set: the enrichment describes the
    // new property, index 0 of the new set and not of both sets appended, and
    // the frame is extracted afresh rather than served from the old cache.
    std::vector<LtlFormula> second;
    second.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Other"}, PhysicalValue{Rational{1, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, second).has_value());
    auto const r2 = client.send_frame(std::stop_token{}, Timestamp{2'000'000}, id, dlc, data);
    REQUIRE(r2.has_value());
    auto const* v2 = std::get<PropertyBatch>(*r2).first_violation();
    REQUIRE(v2 != nullptr);
    REQUIRE(v2->enrichment.has_value());
    CHECK_THAT(v2->enrichment->formula_desc, ContainsSubstring("Other"));
    CHECK(count_extraction_sentinels(*mock_ptr) == 2);
}

TEST_CASE("end_stream forgets the frames of the stream it ends", "[client][enrich]") {
    auto mock = std::make_unique<MockBackend>();
    auto* mock_ptr = mock.get();
    mock_ptr->queue_response(R"({"status": "success"})"); // set_properties
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream
    mock_ptr->queue_response(R"({"status": "ack"})");     // send_frame
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [{"type": "property", "status": "holds", "property_index": 0}]
    })");
    mock_ptr->queue_response(R"({"status": "success"})"); // start_stream again
    mock_ptr->queue_response(R"({
        "status": "complete",
        "results": [{"type": "property", "status": "fails", "property_index": 0, "reason": "r"}]
    })");
    AletheiaClient client(std::move(mock));
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto const id = CanId{StandardId::create(0x100).value()};
    const FramePayload data(8, std::byte{0});
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, id, Dlc::create(8).value(), data)
                .has_value());
    REQUIRE(client.end_stream(std::stop_token{}).has_value());

    // The second stream saw no frame, so its failing verdict has no values
    // to draw on: the first stream's frame must not be extracted for it.
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto const ended = client.end_stream(std::stop_token{});
    REQUIRE(ended.has_value());
    REQUIRE(ended->results[0].enrichment.has_value());
    CHECK(ended->results[0].enrichment->signals.empty());
    CHECK(count_extraction_sentinels(*mock_ptr) == 0);
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// End-of-stream three-valued finalization through the real libaletheia-ffi.so.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <memory>
#include <optional>
#include <ranges>
#include <span>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "find_lib.hpp"

using aletheia::test::find_lib;

using namespace aletheia;

// ---------------------------------------------------------------------------
// End-of-stream three-valued Kleene finalization
// ---------------------------------------------------------------------------
//
// These tests mirror python/tests/test_eos_finalization.py::TestMissingSignalFinalization
// to give C++ client-level coverage of the Unresolved (Unsure) verdict. The
// Agda coalgebra finalizes an Atomic whose signal was never observed to
// FinalVerdict.Unsure; this propagates through And/Or via the Kleene truth
// tables (Unsure ∧ Holds = Unsure, Unsure ∨ Fails = Unsure) and reaches the
// binding as Verdict::Unresolved.
//
// make_two_message_dbc() gives two messages: Msg256 carries Speed, Msg512
// carries Rpm. The LTL property references Speed; sending only Msg512 frames
// leaves the Speed atomic unresolved.

static auto make_two_message_dbc() -> DbcDefinition {
    auto speed_id = StandardId::create(0x100).value();
    auto rpm_id = StandardId::create(0x200).value();
    auto const dlc = Dlc::create(8).value();

    DbcSignal speed_sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"kph"},
        .presence = AlwaysPresent{},
    };

    DbcSignal rpm_sig{
        .name = SignalName{"Rpm"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages =
            {
                DbcMessage{
                    .id = CanId{speed_id},
                    .name = MessageName{"Msg256"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {speed_sig},
                },
                DbcMessage{
                    .id = CanId{rpm_id},
                    .name = MessageName{"Msg512"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {rpm_sig},
                },
            },
    };
}

static auto bytes_of(std::uint16_t raw) -> FramePayload {
    return FramePayload{static_cast<std::byte>(raw & 0xFFU),
                        static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0}};
}

TEST_CASE("end_stream: Always on never-observed signal after 1 frame → Unresolved",
          "[integration][eos][unresolved]") {
    // A single Msg512 frame (no Speed) leaves the Always(Speed<100)
    // atomic unresolved. Under three-valued Kleene this propagates via
    // And (Atomic) (Always _) as Unsure ∧ Holds = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    auto ack = client.send_frame(std::stop_token{}, Timestamp{0}, rpm_id, dlc, bytes_of(5));
    REQUIRE(ack.has_value());
    CHECK(std::holds_alternative<Ack>(*ack));

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Always on never-observed signal after 5 frames → Unresolved",
          "[integration][eos][unresolved]") {
    // Multiple frames without the referenced signal should still finalize to
    // Unresolved — the Kleene fixed point persists regardless of progression
    // count.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{5})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: changed_by on one-frame trace → Unresolved",
          "[integration][eos][unresolved]") {
    // A single frame gives changed_by(0) no prior observation to compare
    // against, so it finalizes to Unsure. The negation stays Unsure (Kleene
    // fixed point) and Always on a non-empty trace leaves behind And (Not
    // Atomic) (Always ...) which reduces to Unsure ∧ Holds = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::negate(ltl::atomic(ltl::changed_by(SignalName{"Speed"}, Delta{Rational{0, 1}}))));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    auto const ack =
        client.send_frame(std::stop_token{}, Timestamp{0}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack.has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on never-observed signal → Unresolved",
          "[integration][eos][unresolved]") {
    // The Or φ (Eventually ψ) → Eventually ψ absorption is guarded by
    // finalizesFails φ = true, and a bare Atomic finalizes to Unsure, so the
    // Or persists and finalizes via Unsure ∨ Fails = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{5})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on 0 frames still finalizes to Fails",
          "[integration][eos][unresolved]") {
    // Contrast with the N ≥ 1 case above. With no progression, finalizeL is
    // applied directly to Eventually _ which returns Fails (liveness
    // operators do not get three-valued absorption on the empty trace).
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Fails);
}

TEST_CASE("end_stream: 0 frames + Always(missing) → Holds (vacuous)",
          "[integration][eos][unresolved]") {
    // Standard LTLf vacuous truth: G φ on the empty trace holds regardless
    // of whether φ's signal is observable. This differentiates the
    // empty-trace path (direct finalizeL on Always) from the non-empty path
    // (finalizeL after progression leaves an And behind).
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: signal recovers after missing → Holds", "[integration][eos][unresolved]") {
    // Once the signal is observed at least once with a true value, the
    // And (Atomic) (Always ...) absorption collapses back to Always (Atomic)
    // via combineAnd Satisfied l. Confirms the Unresolved path only bites
    // when the signal is missing for the entire stream.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();

    // Three frames of Msg512 (Speed absent).
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{3})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }
    // Two frames of Msg256 with Speed = 10 (< 100).
    auto const ack1 =
        client.send_frame(std::stop_token{}, Timestamp{3000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack1.has_value());
    auto const ack2 =
        client.send_frame(std::stop_token{}, Timestamp{4000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack2.has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: K3 combination — Unresolved And Holds = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∧ Holds = Unsure. Left conjunct references
    // Speed (never observed → Unsure), right conjunct references Rpm
    // (observed < 100 → Holds). End result must be Unresolved.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto lhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Rpm"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::both(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{3})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: K3 combination — Unresolved Or Fails = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∨ Fails = Unsure. Left disjunct references
    // Speed (never observed → Unsure), right disjunct is an Eventually that
    // references Rpm but requires an unsatisfiable threshold (→ Fails under
    // direct finalization). The right disjunct is an Eventually on a
    // threshold Rpm never reaches: a liveness operator that no progression
    // satisfied finalizes to Fails on a non-empty trace. An Always would not
    // do, since it holds vacuously when nothing matches.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto lhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Rpm"}, PhysicalValue{Rational{999999, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::either(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{3})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Unresolved result carries enrichment when diagnostics present",
          "[integration][eos][unresolved][enrich]") {
    // client_stream.cpp end_stream() calls enrich_end_stream_results, which collects
    // both Fails and Unresolved verdicts. Verify the enrichment pipeline runs
    // on the Unresolved branch by checking that reason and enrichment are
    // populated.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (auto const i : std::views::iota(std::uint64_t{0}, std::uint64_t{3})) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    auto const& pr = end->results[0];
    CHECK(pr.verdict == Verdict::Unresolved);
    // The Agda core emits a human-readable reason for Unresolved verdicts.
    CHECK_FALSE(pr.reason.empty());
    // end-of-stream enrichment attaches unconditionally for Unresolved — the
    // ViolationEnrichment field should be populated.
    REQUIRE(pr.enrichment.has_value());
    CHECK_FALSE(pr.enrichment->enriched_reason.empty());
}

TEST_CASE("end_stream: enrichment carries the newest payload of a repeated CAN id",
          "[integration][eos][unresolved][enrich]") {
    // The last-frame cache updates an entry in place, assigning the identifier,
    // then the length, then the payload.  A second frame on one CAN id has to
    // replace the bytes and not only the two fields before them, or enrichment
    // reports the newest frame's header beside the oldest frame's values.  The
    // frames carry different values for that reason: with one value the
    // assignment is unobservable and the cache could drop it unnoticed.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    // A liveness property no frame witnesses: both frames carry a Speed under
    // the bound, so the Eventually finalizes to Fails, which is what attaches
    // an enrichment.  The diagnostic names Speed, which is what keeps Speed in
    // the enrichment's signal map, since that map is filtered to the
    // diagnostic's own signals.
    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // Speed is the signal of message 0x100 in this DBC, scaled by one with no
    // offset, so a frame built from a raw value carries that value.
    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    REQUIRE(
        client.send_frame(std::stop_token{}, Timestamp{0}, speed_id, dlc, bytes_of(5)).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, speed_id, dlc, bytes_of(7))
                .has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    auto const& pr = end->results[0];
    CHECK(pr.verdict == Verdict::Fails);
    REQUIRE(pr.enrichment.has_value());
    REQUIRE(pr.enrichment->signals.contains(SignalName{"Speed"}));
    // Seven, the second frame's value, and not five, the first frame's.
    CHECK(pr.enrichment->signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{7, 1}});
}

TEST_CASE("end_stream: the last-frame cache keeps a standard and an extended id of one value apart",
          "[integration][eos][unresolved][enrich]") {
    // The cache is keyed on the identifier's value and its extended bit
    // together. A standard 0x100 and an extended 0x100 are two messages, and
    // a key that dropped the bit would hold one entry for both, so the second
    // frame would replace the first and enrichment would report one message's
    // bytes under the other's signal.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto dbc = make_two_message_dbc();
    auto const extended_id = CanId{ExtendedId::create(0x100).value()};
    dbc.messages[1].id = extended_id;
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    // One liveness property per signal, each unwitnessed, so each finalizes to
    // Fails and carries an enrichment filtered to its own signal.
    std::vector<LtlFormula> props;
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}}))));
    props.push_back(ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Rpm"}, PhysicalValue{Rational{10, 1}}))));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const standard_id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{0}, standard_id, dlc, bytes_of(5))
                .has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, extended_id, dlc, bytes_of(7))
                .has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 2);
    for (auto const& pr : end->results) {
        CHECK(pr.verdict == Verdict::Fails);
        REQUIRE(pr.enrichment.has_value());
    }
    auto const& speed = end->results[0].enrichment->signals;
    auto const& rpm = end->results[1].enrichment->signals;
    REQUIRE(speed.contains(SignalName{"Speed"}));
    REQUIRE(rpm.contains(SignalName{"Rpm"}));
    CHECK(speed.at(SignalName{"Speed"}) == PhysicalValue{Rational{5, 1}});
    CHECK(rpm.at(SignalName{"Rpm"}) == PhysicalValue{Rational{7, 1}});
}

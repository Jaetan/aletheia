// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Streaming property checks, DBC validation with its warnings and refusals,
// and the isolation of two clients, through the real libaletheia-ffi.so.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "bounds_dbc.hpp"
#include "find_lib.hpp"
#include "integration_fixtures.hpp"
#include "required.hpp"

using aletheia::test::required;

using aletheia::test::find_lib;
using aletheia::test::has_warning;
using aletheia::test::make_bounds_dbc;
using aletheia::test::make_integration_dbc;

using namespace aletheia;

// A DBC with a mux signal present for MULTIPLE selector values.  The JSON side
// admits it, but the .dbc text form cannot express it, so re-parsing the emitted
// text does not reproduce the input DBC — format_dbc_text refuses it.
static auto make_multi_value_mux_dbc() -> DbcDefinition {
    auto const id = StandardId::create(0x123).value();
    auto const dlc = Dlc::create(8).value();

    const DbcSignal selector{
        .name = SignalName{"Selector"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    const DbcSignal payload{
        .name = SignalName{"Payload"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = Multiplexed{.multiplexor = SignalName{"Selector"},
                                .multiplex_values = {MultiplexValue{1}, MultiplexValue{2}}},
    };
    return DbcDefinition{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"MultiMux"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {selector, payload},
        }},
    };
}

// A DBC with slaves under TWO Always masters (the split-master shape).  Every
// error-class mux check passes — each named master exists and there is no
// cycle — but .dbc text keeps a single M marker, so re-parsing the emitted
// text would rebind every slave to one master; the JSON side admits the shape.
static auto make_split_master_mux_dbc() -> DbcDefinition {
    auto const id = StandardId::create(0x124).value();
    auto const dlc = Dlc::create(8).value();

    auto const make_sig = [](std::string_view name, std::uint16_t start_bit,
                             SignalPresence presence) -> DbcSignal {
        return DbcSignal{
            .name = SignalName{std::string{name}},
            .start_bit = BitPosition{start_bit},
            .bit_length = BitLength{8},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = false,
            .factor = RationalFactor{Rational{1, 1}},
            .offset = RationalOffset{Rational{0, 1}},
            .minimum = RationalBound{Rational{0, 1}},
            .maximum = RationalBound{Rational{255, 1}},
            .unit = Unit{""},
            .presence = std::move(presence),
        };
    };
    return DbcDefinition{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"SplitMaster"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals =
                {
                    make_sig("MuxA", 0, AlwaysPresent{}),
                    make_sig("MuxB", 8, AlwaysPresent{}),
                    make_sig("A", 16,
                             Multiplexed{.multiplexor = SignalName{"MuxA"},
                                         .multiplex_values = {MultiplexValue{0}}}),
                    make_sig("B", 24,
                             Multiplexed{.multiplexor = SignalName{"MuxB"},
                                         .multiplex_values = {MultiplexValue{0}}}),
                },
        }},
    };
}

TEST_CASE("streaming LTL check via real FFI — property holds", "[integration]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // Property: always(Speed < 200)
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{200, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();

    // Speed 100, 120 and 150 km/h at the DBC's factor of one tenth, all
    // under the threshold.
    for (auto const raw : {std::uint16_t{1000}, std::uint16_t{1200}, std::uint16_t{1500}}) {
        const FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                                static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0}};
        auto const result =
            client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(std::holds_alternative<Ack>(*result));
    }

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("streaming LTL check via real FFI — property violated", "[integration]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // Property: always(Speed < 120) — will be violated by Speed=150
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{120, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    bool got_violation = false;

    // Speed 100, 110 and 150 km/h at the DBC's factor of one tenth; the last
    // one breaks the threshold.
    for (auto const raw : {std::uint16_t{1000}, std::uint16_t{1100}, std::uint16_t{1500}}) {
        const FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                                static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0},
                                std::byte{0}};
        auto const result =
            client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        if (std::holds_alternative<PropertyBatch>(*result))
            got_violation = true;
    }

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());

    // Either got a mid-stream violation or end-of-stream violation
    auto const eos_violation = !end->results.empty() && end->results[0].verdict == Verdict::Fails;
    CHECK((got_violation || eos_violation));
}

TEST_CASE("non-monotonic timestamp rejected by Agda via real FFI", "[integration][monotonic]") {
    // Backward timestamps would make metric LTL operators silently produce
    // wrong verdicts (∸ clamps to 0 on negative differences). Agda's
    // handleDataFrame refuses them — this is the single source of truth
    // across all bindings, proven in
    // Aletheia.Protocol.FrameProcessor.Properties.Monotonic (PROPERTY 28).
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{500, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const FramePayload payload{std::byte{10}, std::byte{0}, std::byte{0}, std::byte{0},
                               std::byte{0},  std::byte{0}, std::byte{0}, std::byte{0}};

    // First frame at t=5000 µs — accepted.
    auto const ok = client.send_frame(std::stop_token{}, Timestamp{5000}, id, dlc, payload);
    REQUIRE(ok.has_value());
    CHECK(std::holds_alternative<Ack>(*ok));

    // Regressing to t=4999 µs — rejected by Agda.
    auto const err = client.send_frame(std::stop_token{}, Timestamp{4999}, id, dlc, payload);
    REQUIRE_FALSE(err.has_value());
    CHECK(err.error().code() == ErrorCode::HandlerNonMonotonicTimestamp);

    // Same-timestamp frames (≥, not >) are accepted.
    auto const eq = client.send_frame(std::stop_token{}, Timestamp{5000}, id, dlc, payload);
    REQUIRE(eq.has_value());
    CHECK(std::holds_alternative<Ack>(*eq));

    // Anchor unchanged after rejection — next ≥ 5000 still accepted.
    auto const fwd = client.send_frame(std::stop_token{}, Timestamp{6000}, id, dlc, payload);
    REQUIRE(fwd.has_value());
    CHECK(std::holds_alternative<Ack>(*fwd));

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
}

TEST_CASE("validate DBC via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    auto const result = client.validate_dbc(std::stop_token{}, make_integration_dbc());
    REQUIRE(result.has_value());
    // Our test DBC is well-formed — no errors expected
    CHECK_FALSE(result->has_errors);
}

TEST_CASE("VAL_ value descriptions round-trip via real FFI",
          "[integration][dbc][value_descriptions]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    constexpr std::string_view text = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 300 Transmission: 8 ECU
 SG_ EngineState : 8|2@1+ (1,0) [0|3] "" Vector__XXX

VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;
)";

    auto const parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE(parsed.has_value());
    REQUIRE(parsed->dbc.messages.size() == 1);
    REQUIRE(parsed->dbc.messages[0].signals.size() == 1);
    auto const& sig = parsed->dbc.messages[0].signals[0];
    REQUIRE(sig.value_descriptions.size() == 4);
    CHECK(sig.value_descriptions[0].value == 0);
    CHECK(sig.value_descriptions[0].description == "Off");
    CHECK(sig.value_descriptions[1].value == 1);
    CHECK(sig.value_descriptions[1].description == "Cranking");
    CHECK(sig.value_descriptions[2].value == 2);
    CHECK(sig.value_descriptions[2].description == "Running");
    CHECK(sig.value_descriptions[3].value == 3);
    CHECK(sig.value_descriptions[3].description == "Stall");

    auto const formatted = client.format_dbc_text(std::stop_token{}, parsed->dbc);
    REQUIRE(formatted.has_value());
    constexpr std::string_view want_line =
        R"(VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;)";
    CHECK(formatted->text.contains(want_line));
    // format_dbc_text is always strict: this DBC round-trips, so it yields a
    // DbcText carrying the (advisory, here empty) wfTextIssues diagnostics.
    CHECK(formatted->issues.empty());
}

TEST_CASE("format_dbc_text refuses a multi-value mux via real FFI",
          "[integration][dbc][format][roundtrip]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // A multi-value mux selector does not round-trip through .dbc text, so the
    // always-strict formatter refuses it with a typed round-trip error rather
    // than emitting lossy text.
    auto const result = client.format_dbc_text(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE_FALSE(result.has_value());
    auto const& err = result.error();
    CHECK(err.kind() == ErrorKind::TextRoundtrip);
    CHECK(err.code() == ErrorCode::HandlerTextRoundtripFailed);
    REQUIRE(err.issues().has_value());

    // Led by the error-severity text_roundtrip_divergence issue the handler
    // prepends, plus the multi_value_mux_selector diagnostic.
    bool has_divergence = false;
    bool has_mux = false;
    for (auto const& issue : *err.issues()) {
        if (issue.code == IssueCode::TextRoundtripDivergence)
            has_divergence = true;
        if (issue.code == IssueCode::MultiValueMuxSelector)
            has_mux = true;
    }
    CHECK(has_divergence);
    CHECK(has_mux);
}

TEST_CASE("CHECK 23 unknown_value_description_target warning via real FFI",
          "[integration][dbc][value_descriptions][validator]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    constexpr std::string_view text = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Rpm : 0|16@1+ (1,0) [0|8000] "rpm" Vector__XXX

VAL_ 999 GhostSignal 0 "Off" 1 "On" ;
)";

    auto const parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE(parsed.has_value());
    auto const hit = std::ranges::any_of(parsed->warnings, [](const ValidationIssue& issue) {
        return issue.code == IssueCode::UnknownValueDescriptionTarget;
    });
    CHECK(hit);
}

TEST_CASE("CHECK 24 multi_value_mux_selector warning via real FFI",
          "[integration][dbc][validator][mux]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // validate_dbc mirrors the round-trip diagnostic warning-class: the shape
    // loads and streams fine, so has_errors stays false.
    auto const result = client.validate_dbc(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(has_warning(result->issues, IssueCode::MultiValueMuxSelector));

    // The load route surfaces the same warning without blocking.
    auto const parsed = client.parse_dbc(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE(parsed.has_value());
    CHECK(has_warning(parsed->warnings, IssueCode::MultiValueMuxSelector));
}

TEST_CASE("CHECK 25 mux_master_incoherent warning via real FFI",
          "[integration][dbc][validator][mux]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // The split-master shape passes every error-class mux check, so only the
    // warning-class mirror names it.
    auto const result = client.validate_dbc(std::stop_token{}, make_split_master_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(has_warning(result->issues, IssueCode::MuxMasterIncoherent));

    // The load route surfaces the same warning without blocking.
    auto const parsed = client.parse_dbc(std::stop_token{}, make_split_master_mux_dbc());
    REQUIRE(parsed.has_value());
    CHECK(has_warning(parsed->warnings, IssueCode::MuxMasterIncoherent));
}

// An eight-bit unsigned signal at factor 1, offset 0 carries [0, 255], so a
// declared maximum of 1000, or a minimum of -5, admits values no raw value
// encodes. That is an error: validation reports it, and the load route refuses
// the DBC with it, one issue for the bound at fault.
static auto make_range_dbc(Rational minimum, Rational maximum) -> DbcDefinition {
    return DbcDefinition{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{StandardId::create(0x101).value()},
            .name = MessageName{"M"},
            .dlc = Dlc::create(8).value(),
            .sender = NodeName{"ECU"},
            .signals = {DbcSignal{
                .name = SignalName{"S"},
                .start_bit = BitPosition{0},
                .bit_length = BitLength{8},
                .byte_order = ByteOrder::LittleEndian,
                .is_signed = false,
                .factor = RationalFactor{Rational{1, 1}},
                .offset = RationalOffset{Rational{0, 1}},
                .minimum = RationalBound{minimum},
                .maximum = RationalBound{maximum},
                .unit = Unit{""},
                .presence = AlwaysPresent{},
            }},
        }},
    };
}

// The issues naming range_exceeds_bits: exactly one, an error, with `detail`.
static void check_one_range_issue(std::span<const ValidationIssue> issues,
                                  std::string_view detail) {
    std::vector<ValidationIssue> named;
    std::ranges::copy_if(issues, std::back_inserter(named), [](const ValidationIssue& issue) {
        return issue.code == IssueCode::RangeExceedsBits;
    });
    REQUIRE(named.size() == 1);
    CHECK(named.front().severity == IssueSeverity::Error);
    CHECK(named.front().detail == detail);
}

TEST_CASE("a declared range past the values a signal's bits carry is refused at load",
          "[integration][dbc][validator]") {
    auto client = required(AletheiaClient::create(required(make_ffi_backend(find_lib()))));
    struct Case {
        Rational minimum;
        Rational maximum;
        std::string_view detail;
    };
    for (auto const& [minimum, maximum, detail] : std::to_array<Case>({
             {.minimum = Rational{0, 1},
              .maximum = Rational{1000, 1},
              .detail = "Message 'M', signal 'S': declared maximum lies above the values its "
                        "bits carry"},
             {.minimum = Rational{-5, 1},
              .maximum = Rational{255, 1},
              .detail = "Message 'M', signal 'S': declared minimum lies below the values its "
                        "bits carry"},
         })) {
        CAPTURE(detail);
        auto const dbc = make_range_dbc(minimum, maximum);

        auto const validated = client.validate_dbc(std::stop_token{}, dbc);
        REQUIRE(validated.has_value());
        CHECK(validated->has_errors);
        check_one_range_issue(validated->issues, detail);

        auto const parsed = client.parse_dbc(std::stop_token{}, dbc);
        REQUIRE_FALSE(parsed.has_value());
        CHECK(parsed.error().code() == ErrorCode::HandlerValidationFailed);
        REQUIRE(parsed.error().issues().has_value());
        check_one_range_issue(*parsed.error().issues(), detail);
    }
}

TEST_CASE("a bound that names no part of a DBC carries no field", "[integration][input_bounds]") {
    auto client = required(AletheiaClient::create(required(make_ffi_backend(find_lib()))));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_bounds_dbc()).has_value());
    // 63 always-wrappers around an atomic predicate nest the command's JSON
    // past max_nesting_depth.
    auto formula = ltl::atomic(ltl::equals(SignalName{"S"}, PhysicalValue{Rational{0, 1}}));
    std::ranges::for_each(std::views::repeat(0, 63),
                          [&formula](auto) { formula = ltl::always(std::move(formula)); });
    std::vector<LtlFormula> properties;
    properties.push_back(std::move(formula));

    auto const result = client.set_properties(std::stop_token{}, properties);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == bound_kind_nesting_depth);
    CHECK_FALSE(result.error().bound_info()->field.has_value());
}

TEST_CASE("rejected DBC text parse carries typed validation issues via real FFI",
          "[integration][dbc][validation]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // minimal.dbc's EngineStatus message with EngineTemp renamed to
    // EngineSpeed — a duplicate signal name, an error-severity issue, so the
    // kernel rejects the parse with handler_validation_failed carrying the
    // structured issues alongside the legacy message text.
    constexpr std::string_view text = R"(VERSION "1.0"

NS_ :

BS_:

BU_: Engine Gateway

BO_ 256 EngineStatus: 8 Engine
 SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm" Gateway
 SG_ EngineSpeed : 16|8@1+ (1,-40) [-40|215] "degC" Gateway
)";

    auto const parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE_FALSE(parsed.has_value());
    CHECK(parsed.error().code() == ErrorCode::HandlerValidationFailed);
    CHECK(std::string{parsed.error().message()}.contains("duplicate signal name"));
    REQUIRE(parsed.error().issues().has_value());
    auto const hit =
        std::ranges::any_of(*parsed.error().issues(), [](const ValidationIssue& issue) {
            return issue.severity == IssueSeverity::Error &&
                   issue.code == IssueCode::DuplicateSignalName;
        });
    CHECK(hit);
}

// ---------------------------------------------------------------------------
// Client isolation test
// ---------------------------------------------------------------------------
// Two independent AletheiaClient instances over the real library, their calls
// interleaved step by step on one thread, lenient then strict, so every call of
// one lands between calls of the other:
//
//   lenient                           strict
//   ────────                          ────────
//   parse_dbc(dbc)                    parse_dbc(dbc)
//   set_properties(Speed < 200)       set_properties(Speed < 100)
//   start_stream()                    start_stream()
//   send_frame(Speed = 150)           send_frame(Speed = 150)
//   end_stream() → Holds              end_stream() → Fails
//
// Same DBC, same frame data, different properties → different verdicts.
// This proves each client owns independent state; the order is driven, the
// same on every run.

static auto speed_below(PhysicalValue threshold) -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, threshold))));
    return props;
}

static auto verdict_of(const FrameResponse& sent, const StreamResult& ended) -> Verdict {
    auto const mid_violation = std::holds_alternative<PropertyBatch>(sent);
    return (mid_violation || ended.results[0].verdict == Verdict::Fails) ? Verdict::Fails
                                                                         : Verdict::Holds;
}

TEST_CASE("interleaved clients have independent state via real FFI", "[integration][concurrent]") {
    auto const lib = find_lib();
    auto lenient = required(
        AletheiaClient::create(required(make_ffi_backend(lib)))); // Speed 150 < 200 → Holds
    auto strict = required(
        AletheiaClient::create(required(make_ffi_backend(lib)))); // Speed 150 >= 100 → Fails
    const std::array<std::reference_wrapper<AletheiaClient>, 2> clients{lenient, strict};

    auto const dbc = make_integration_dbc();
    for (AletheiaClient& client : clients)
        REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());
    REQUIRE(lenient.set_properties(std::stop_token{}, speed_below(PhysicalValue{Rational{200, 1}}))
                .has_value());
    REQUIRE(strict.set_properties(std::stop_token{}, speed_below(PhysicalValue{Rational{100, 1}}))
                .has_value());
    for (AletheiaClient& client : clients)
        REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::uint16_t raw = 1500; // Speed 150 km/h at factor one tenth
    const FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                            static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                            std::byte{0},
                            std::byte{0},
                            std::byte{0},
                            std::byte{0},
                            std::byte{0},
                            std::byte{0}};
    auto const sent_lenient =
        lenient.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    auto const sent_strict =
        strict.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
    REQUIRE(sent_lenient.has_value());
    REQUIRE(sent_strict.has_value());

    auto const ended_lenient = lenient.end_stream(std::stop_token{});
    auto const ended_strict = strict.end_stream(std::stop_token{});
    REQUIRE(ended_lenient.has_value());
    REQUIRE(ended_strict.has_value());
    REQUIRE_FALSE(ended_lenient->results.empty());
    REQUIRE_FALSE(ended_strict->results.empty());

    // Same data, different properties → different verdicts proves isolation
    CHECK(verdict_of(*sent_lenient, *ended_lenient) == Verdict::Holds);
    CHECK(verdict_of(*sent_strict, *ended_strict) == Verdict::Fails);
}

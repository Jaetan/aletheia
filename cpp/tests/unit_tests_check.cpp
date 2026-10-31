// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: Check DSL (one-shot, two-step, when/then chains).
//
// Covers the check::signal / check::when builders, metadata (named/severity/
// signal_name/condition_desc), equivalence with hand-rolled ltl:: formulas,
// and the add_checks client integration path.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/json.hpp"
#include "detail/mock_backend.hpp"
#include "every_alternative.hpp"
#include "required.hpp"
#include "test_helpers.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/enrich.hpp>

#include <cstdint>
#include <limits>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

using aletheia::test::make_test_dbc;
using aletheia::test::required;

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Check API — one-shot methods
// ===========================================================================

TEST_CASE("check::signal never_exceeds", "[check]") {
    auto const result =
        required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(Speed <= 220)");
}

TEST_CASE("check::signal never_below", "[check]") {
    auto const result =
        required(check::signal("Voltage").never_below(PhysicalValue{Rational{23, 2}}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(Voltage >= 11.5)");
}

TEST_CASE("check::signal stays_between", "[check]") {
    auto const result = required(check::signal("Voltage").stays_between(
        PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(11.5 <= Voltage <= 14.5)");
}

TEST_CASE("check::signal never_equals", "[check]") {
    auto const result =
        required(check::signal("ErrorCode").never_equals(PhysicalValue{Rational{255, 1}}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "never ErrorCode = 255");
}

// ===========================================================================
// Check API — two-step methods
// ===========================================================================

TEST_CASE("check::signal equals always", "[check]") {
    auto const result = required(check::signal("Gear").equals(PhysicalValue{Rational{}}).always());
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(Gear = 0)");
}

TEST_CASE("check::signal settles_between within", "[check]") {
    auto const result = required(
        check::signal("Temp")
            .settles_between(PhysicalValue{Rational{60, 1}}, PhysicalValue{Rational{80, 1}})
            .within(TimeBound{500'000}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always within 500ms (60 <= Temp <= 80)");
}

// ===========================================================================
// Check API — causal chains (when/then)
// ===========================================================================

TEST_CASE("check::when then equals within", "[check]") {
    auto const result = required(check::when("Brake")
                                     .exceeds(PhysicalValue{Rational{50, 1}})
                                     .then("BrakeLight")
                                     .equals(PhysicalValue{Rational{1, 1}})
                                     .within(TimeBound{100'000}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) ==
          "always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))");
}

TEST_CASE("check::when drops_below then within", "[check]") {
    auto const result = required(check::when("Voltage")
                                     .drops_below(PhysicalValue{Rational{11, 1}})
                                     .then("Warning")
                                     .equals(PhysicalValue{Rational{1, 1}})
                                     .within(TimeBound{50'000}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(not(Voltage < 11) or eventually within 50ms (Warning = 1))");
}

TEST_CASE("check::when then stays_between within", "[check]") {
    auto const result =
        required(check::when("Brake")
                     .exceeds(PhysicalValue{Rational{50, 1}})
                     .then("Speed")
                     .stays_between(PhysicalValue{Rational{}}, PhysicalValue{Rational{10, 1}})
                     .within(TimeBound{200'000}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) ==
          "always(not(Brake > 50) or eventually within 200ms (0 <= Speed <= 10))");
}

TEST_CASE("check::when equals then exceeds within", "[check]") {
    auto const result = required(check::when("Ignition")
                                     .equals(PhysicalValue{Rational{1, 1}})
                                     .then("FuelPump")
                                     .exceeds(PhysicalValue{Rational{}})
                                     .within(TimeBound{50'000}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) ==
          "always(not(Ignition = 1) or eventually within 50ms (FuelPump > 0))");
}

// ===========================================================================
// Check API — metadata
// ===========================================================================

TEST_CASE("Check metadata named and severity", "[check]") {
    auto result = required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    result.named("SpeedLimit").severity("critical");
    CHECK(result.name() == "SpeedLimit");
    CHECK(result.check_severity() == "critical");
    CHECK(result.signal_name() == "Speed");
    CHECK(result.condition_desc() == "<= 220");
}

TEST_CASE("Check signal_name and condition_desc populated", "[check]") {
    auto const r1 = required(check::signal("V").never_below(PhysicalValue{Rational{23, 2}}));
    CHECK(r1.signal_name() == "V");
    CHECK(r1.condition_desc() == ">= 11.5");

    auto const r2 = required(check::signal("E").never_equals(PhysicalValue{Rational{}}));
    CHECK(r2.signal_name() == "E");
    CHECK(r2.condition_desc() == "!= 0");
}

TEST_CASE("Check when/then metadata", "[check]") {
    auto const result = required(check::when("Brake")
                                     .exceeds(PhysicalValue{Rational{50, 1}})
                                     .then("Light")
                                     .equals(PhysicalValue{Rational{1, 1}})
                                     .within(TimeBound{100'000}));
    CHECK(result.signal_name() == "Light");
    CHECK(result.condition_desc() == "= 1 within 100000\u00b5s");
}

// ===========================================================================
// Check API — to_formula returns copy without consuming
// ===========================================================================

TEST_CASE("Check to_formula non-consuming", "[check]") {
    auto const result =
        required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    auto const f1 = result.to_formula();
    auto const f2 = result.to_formula();
    CHECK(format_formula(f1) == format_formula(f2).value());
}

// ===========================================================================
// Check API — error cases
// ===========================================================================

// The kernel's refusal of a check's formula: kind Validation, the code of a
// property checked on its own, and the reason set_properties gives.
static void check_refused(Result<CheckResult> const& built, std::string_view message) {
    REQUIRE_FALSE(built.has_value());
    CHECK(built.error().kind() == ErrorKind::Validation);
    CHECK(built.error().code() == ErrorCode::HandlerPropertyRefused);
    CHECK(built.error().message() == message);
}

TEST_CASE("a range whose lo is above its hi is refused, naming both bounds", "[check]") {
    // As in Rust and Go: stays_between refuses at once, and settles_between and
    // the then-signal's stays_between at their within, the call that finishes
    // the chain.
    auto const ten = PhysicalValue{Rational{10, 1}};
    auto const five = PhysicalValue{Rational{5, 1}};
    check_refused(check::signal("S").stays_between(ten, five), "between: min 10 exceeds max 5");
    check_refused(check::signal("S").settles_between(ten, five).within(TimeBound{1'000}),
                  "between: min 10 exceeds max 5");
    check_refused(
        check::when("A").exceeds(five).then("B").stays_between(ten, five).within(TimeBound{1'000}),
        "between: min 10 exceeds max 5");
    // The kernel renders each bound, so a half reads as a decimal.
    check_refused(
        check::signal("S").stays_between(PhysicalValue{Rational{1, 2}}, PhysicalValue{Rational{}}),
        "between: min 0.5 exceeds max 0");
    // Equal bounds are a range.
    CHECK(check::signal("S").stays_between(five, five).has_value());
    CHECK(check::signal("S").settles_between(five, five).within(TimeBound{1'000}).has_value());
    CHECK(check::when("A")
              .exceeds(five)
              .then("B")
              .stays_between(five, five)
              .within(TimeBound{1'000})
              .has_value());
}

TEST_CASE("Check within accepts a zero bound and the largest the kernel reads", "[check]") {
    // Zero checks only the current step; 2^64-1 microseconds is the kernel's
    // largest time bound.
    auto const largest = TimeBound{std::numeric_limits<std::uint64_t>::max()};
    auto const settles = check::signal("T").settles_between(PhysicalValue{Rational{}},
                                                            PhysicalValue{Rational{100, 1}});
    CHECK(required(settles.within(TimeBound{0})).condition_desc() ==
          "between 0 and 100 within 0\u00b5s");
    CHECK(required(settles.within(largest)).condition_desc() ==
          "between 0 and 100 within 18446744073709551615\u00b5s");
    auto const cond = check::when("A")
                          .exceeds(PhysicalValue{Rational{}})
                          .then("B")
                          .equals(PhysicalValue{Rational{1, 1}});
    CHECK(required(cond.within(TimeBound{0})).condition_desc() == "= 1 within 0\u00b5s");
    CHECK(required(cond.within(largest)).condition_desc() ==
          "= 1 within 18446744073709551615\u00b5s");
}

TEST_CASE("every builder shape describes its condition in full", "[check]") {
    auto const lo = PhysicalValue{Rational{23, 2}};
    auto const hi = PhysicalValue{Rational{29, 2}};
    auto const one = PhysicalValue{Rational{1, 1}};
    auto const seven_ms = TimeBound{7'000};
    auto const sig = check::signal("S");
    CHECK(required(sig.never_exceeds(one)).condition_desc() == "<= 1");
    CHECK(required(sig.never_below(one)).condition_desc() == ">= 1");
    CHECK(required(sig.never_equals(one)).condition_desc() == "!= 1");
    CHECK(required(sig.stays_between(lo, hi)).condition_desc() == "between 11.5 and 14.5");
    CHECK(required(sig.equals(one).always()).condition_desc() == "= 1");
    CHECK(required(sig.settles_between(lo, hi).within(seven_ms)).condition_desc() ==
          "between 11.5 and 14.5 within 7000\u00b5s");
    auto const then = check::when("A").exceeds(one).then("B");
    CHECK(required(then.equals(one).within(seven_ms)).condition_desc() == "= 1 within 7000\u00b5s");
    CHECK(required(then.exceeds(lo).within(seven_ms)).condition_desc() ==
          "> 11.5 within 7000\u00b5s");
    CHECK(required(then.stays_between(lo, hi).within(seven_ms)).condition_desc() ==
          "between 11.5 and 14.5 within 7000\u00b5s");
}

TEST_CASE("a check built from a formula alone describes nothing", "[check]") {
    // A description of literal text alone reaches no kernel, so it reads the
    // same whether the runtime is up or not.
    auto const formula = [] {
        return ltl::always(
            ltl::atomic(Equals{.signal = SignalName{"B"}, .value = PhysicalValue{Rational{}}}));
    };
    CHECK(CheckResult{formula()}.condition_desc() == "");
    CHECK(CheckResult{formula(), "B", ""}.condition_desc() == "");
    CHECK(CheckResult{formula(), "B", "custom"}.condition_desc() == "custom");
}

// ===========================================================================
// Check API — equivalence with manual ltl:: construction
// ===========================================================================

TEST_CASE("Check never_exceeds matches manual ltl", "[check]") {
    auto const check_f =
        required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}))
            .to_formula();
    auto const manual_f = ltl::always(ltl::atomic(
        required(ltl::less_than_or_equal(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}}))));
    CHECK(format_formula(check_f) == format_formula(manual_f).value());
}

TEST_CASE("Check stays_between matches manual ltl", "[check]") {
    auto const check_f = required(check::signal("V").stays_between(PhysicalValue{Rational{23, 2}},
                                                                   PhysicalValue{Rational{29, 2}}))
                             .to_formula();
    auto const manual_f = ltl::always(ltl::atomic(required(ltl::between(
        SignalName{"V"}, PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}}))));
    CHECK(format_formula(check_f) == format_formula(manual_f).value());
}

TEST_CASE("Check never_equals matches manual ltl", "[check]") {
    auto const check_f =
        required(check::signal("Err").never_equals(PhysicalValue{Rational{255, 1}})).to_formula();
    auto const manual_f =
        ltl::never(required(ltl::equals(SignalName{"Err"}, PhysicalValue{Rational{255, 1}})));
    CHECK(format_formula(check_f) == format_formula(manual_f).value());
}

TEST_CASE("Check settles matches manual ltl", "[check]") {
    auto const check_f = required(check::signal("T")
                                      .settles_between(PhysicalValue{Rational{60, 1}},
                                                       PhysicalValue{Rational{80, 1}})
                                      .within(TimeBound{500'000}))
                             .to_formula();
    auto const manual_f = required(ltl::always_within(
        TimeBound{500'000},
        ltl::atomic(required(ltl::between(SignalName{"T"}, PhysicalValue{Rational{60, 1}},
                                          PhysicalValue{Rational{80, 1}})))));
    CHECK(format_formula(check_f) == format_formula(manual_f).value());
}

// ===========================================================================
// Check API — add_checks client integration
// ===========================================================================

TEST_CASE("add_checks sends properties to backend", "[check][client]") {
    auto mock = std::make_unique<MockBackend>();
    auto const* mock_ptr = mock.get();
    mock->queue_response(R"({"status": "success"})");
    auto client = required(AletheiaClient::create(std::move(mock)));

    std::vector<CheckResult> checks;
    checks.push_back(
        required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}})));
    checks.push_back(required(check::signal("Voltage").stays_between(
        PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}})));
    auto const result = client.add_checks(std::stop_token{}, std::move(checks));
    REQUIRE(result.has_value());
    REQUIRE(mock_ptr->captured().size() == 1);
    CHECK_THAT(mock_ptr->last_captured(), ContainsSubstring("\"Speed\""));
    CHECK_THAT(mock_ptr->last_captured(), ContainsSubstring("\"Voltage\""));
}

TEST_CASE("default_checks are prepended in add_checks", "[check][client]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");

    std::vector<CheckResult> defaults;
    defaults.push_back(required(check::signal("Voltage").stays_between(
        PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}})));

    auto const* mock_ptr = mock.get();
    auto client = required(AletheiaClient::create(std::move(mock), {}, std::move(defaults)));

    std::vector<CheckResult> checks;
    checks.push_back(
        required(check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}})));
    auto const result = client.add_checks(std::stop_token{}, std::move(checks));
    REQUIRE(result.has_value());
    REQUIRE(mock_ptr->captured().size() == 1);
    CHECK(mock_ptr->last_captured().find("\"Voltage\"") <
          mock_ptr->last_captured().find("\"Speed\""));
}

TEST_CASE("a check and add_checks return the serializer's refusal of a name that is not UTF-8",
          "[check][client]") {
    // A property is serialized before the kernel or the backend sees it, and
    // the JSON writer refuses a byte that is not UTF-8: the builder answers
    // that refusal as a Validation error rather than letting it escape, and so
    // does add_checks for a check built from its formula alone.
    auto const not_utf8 = SignalName{std::string{"\xff"}};
    auto const refused = [](AletheiaError const& error) {
        CHECK(error.kind() == ErrorKind::Validation);
        CHECK(error.message() ==
              "[json.exception.type_error.316] invalid UTF-8 byte at index 0: 0xFF");
    };
    refused(detail::error_of(
        check::signal(not_utf8.get()).never_exceeds(PhysicalValue{Rational{1, 1}})));
    auto client = required(AletheiaClient::create(std::make_unique<MockBackend>()));
    std::vector<CheckResult> checks;
    checks.emplace_back(ltl::always(
        ltl::atomic(LessThanOrEqual{.signal = not_utf8, .value = PhysicalValue{Rational{1, 1}}})));
    refused(detail::error_of(client.add_checks(std::stop_token{}, std::move(checks))));
}

TEST_CASE("every command and the canonical JSON refuse a name that is not UTF-8, unsent",
          "[check][client]") {
    // Each command is serialized before the backend sees it, so the JSON
    // writer's refusal is the answer, kind Validation, and nothing is sent.
    auto owned = std::make_unique<MockBackend>();
    auto const* const mock = owned.get();
    auto client = required(AletheiaClient::create(std::move(owned)));
    auto dbc = make_test_dbc();
    dbc.messages.front().name = MessageName{std::string{"\xff"}};
    auto const refused = [](AletheiaError const& error) {
        CHECK(error.kind() == ErrorKind::Validation);
        CHECK(error.message() ==
              "[json.exception.type_error.316] invalid UTF-8 byte at index 0: 0xFF");
    };
    refused(detail::error_of(client.parse_dbc(std::stop_token{}, dbc)));
    refused(detail::error_of(client.validate_dbc(std::stop_token{}, dbc)));
    refused(detail::error_of(client.format_dbc_text(std::stop_token{}, dbc)));
    refused(detail::error_of(client.parse_dbc_text(std::stop_token{}, "\xff")));
    refused(detail::error_of(to_canonical_json(dbc)));
    CHECK(mock->captured().empty());
}

// ===========================================================================
// Smart-fallback Rational renderer in format_formula
// ===========================================================================

// The renderer's maths and shape, the decimal-against-fraction fallback,
// trailing-zero trimming, the sign, the cross-binding digit guard and exact
// decimals that are neither scientific nor truncated, are proven once in the
// kernel: Aletheia.DBC.RationalRenderer.Faithful states
// formatℚ-chars-represents and the sibling Properties module pins the shape.
// The binding's own share is what the cases below assert: that the FFI plumbs
// both output shapes through, and that each formula-building path embeds the
// result.

TEST_CASE("format_formula plumbs a non-terminating Rational (N/D shape)", "[enrich][rational]") {
    using namespace ltl;
    auto const f = atomic(required(equals(SignalName{"S"}, PhysicalValue{Rational{1, 3}})));
    CHECK(format_formula(f) == "S = 1/3");
}

TEST_CASE("format_formula plumbs a signed Rational (sign preserved)", "[enrich][rational]") {
    using namespace ltl;
    auto const f = atomic(required(greater_than(SignalName{"S"}, PhysicalValue{Rational{-2, 7}})));
    CHECK(format_formula(f) == "S > -2/7");
}

TEST_CASE("format_formula embeds Rationals in a between bound pair", "[enrich][rational]") {
    using namespace ltl;
    auto const f = atomic(required(
        between(SignalName{"S"}, PhysicalValue{Rational{1, 3}}, PhysicalValue{Rational{2, 3}})));
    CHECK(format_formula(f) == "1/3 <= S <= 2/3");
}

TEST_CASE("format_formula plumbs a terminating Rational (decimal shape) via the check builder",
          "[enrich][rational]") {
    auto const result =
        required(check::signal("Voltage").never_below(PhysicalValue{Rational{23, 2}}));
    auto const f = result.to_formula();
    CHECK(format_formula(f) == "always(Voltage >= 11.5)");
}

TEST_CASE("clone copies every alternative unchanged and owns its children", "[check][ltl]") {
    auto original = std::make_unique<LtlFormula>(aletheia::test::every_alternative());
    auto const before =
        detail::serialize_set_properties(std::span<LtlFormula const>{original.get(), 1});
    auto const copy = ltl::clone(*original);
    original.reset();
    auto const after = detail::serialize_set_properties(std::span<LtlFormula const>{&copy, 1});
    REQUIRE(before.has_value());
    REQUIRE(after.has_value());
    CHECK(*after == *before);
}

TEST_CASE("clone keeps a missing child missing", "[check][ltl]") {
    LtlFormula const orphan{Not{nullptr}};
    auto const copy = ltl::clone(orphan);
    auto const* not_node = std::get_if<Not>(&copy.value);
    REQUIRE(not_node != nullptr);
    CHECK(not_node->formula == nullptr);
}

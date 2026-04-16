// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: Check DSL (one-shot, two-step, when/then chains).
//
// Covers the Check::signal / Check::when builders, metadata (named/severity/
// signal_name/condition_desc), equivalence with hand-rolled ltl:: formulas,
// and the add_checks client integration path.
#include <catch2/catch_test_macros.hpp>

#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>
#include <aletheia/enrich.hpp>

#include <chrono>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

using namespace aletheia;

// ===========================================================================
// Check API — one-shot methods
// ===========================================================================

TEST_CASE("Check::signal never_exceeds", "[check]") {
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Speed < 220)");
}

TEST_CASE("Check::signal never_below", "[check]") {
    auto result = Check::signal("Voltage").never_below(PhysicalValue{Rational{23, 2}});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Voltage >= 11.5)");
}

TEST_CASE("Check::signal stays_between", "[check]") {
    auto result = Check::signal("Voltage").stays_between(PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(11.5 <= Voltage <= 14.5)");
}

TEST_CASE("Check::signal never_equals", "[check]") {
    auto result = Check::signal("ErrorCode").never_equals(PhysicalValue{Rational{255, 1}});
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "never ErrorCode = 255");
}

// ===========================================================================
// Check API — two-step methods
// ===========================================================================

TEST_CASE("Check::signal equals always", "[check]") {
    auto result = Check::signal("Gear").equals(PhysicalValue{Rational{}}).always();
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) == "always(Gear = 0)");
}

TEST_CASE("Check::signal settles_between within", "[check]") {
    using namespace std::chrono_literals;
    auto result =
        Check::signal("Temp").settles_between(PhysicalValue{Rational{60, 1}}, PhysicalValue{Rational{80, 1}}).within(500ms);
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
                      .exceeds(PhysicalValue{Rational{50, 1}})
                      .then("BrakeLight")
                      .equals(PhysicalValue{Rational{1, 1}})
                      .within(100ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))");
}

TEST_CASE("Check::when drops_below then within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Voltage")
                      .drops_below(PhysicalValue{Rational{11, 1}})
                      .then("Warning")
                      .equals(PhysicalValue{Rational{1, 1}})
                      .within(50ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Voltage < 11) or eventually within 50ms (Warning = 1))");
}

TEST_CASE("Check::when then stays_between within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Brake")
                      .exceeds(PhysicalValue{Rational{50, 1}})
                      .then("Speed")
                      .stays_between(PhysicalValue{Rational{}}, PhysicalValue{Rational{10, 1}})
                      .within(200ms);
    auto f = result.to_formula();
    REQUIRE(f);
    CHECK(format_formula(*f) ==
          "always(not(Brake > 50) or eventually within 200ms (0 <= Speed <= 10))");
}

TEST_CASE("Check::when equals then exceeds within", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Ignition")
                      .equals(PhysicalValue{Rational{1, 1}})
                      .then("FuelPump")
                      .exceeds(PhysicalValue{Rational{}})
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
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}});
    result.named("SpeedLimit").severity("critical");
    CHECK(result.name() == "SpeedLimit");
    CHECK(result.check_severity() == "critical");
    CHECK(result.signal_name() == "Speed");
    CHECK(result.condition_desc() == "< 220");
}

TEST_CASE("Check signal_name and condition_desc populated", "[check]") {
    auto r1 = Check::signal("V").never_below(PhysicalValue{Rational{23, 2}});
    CHECK(r1.signal_name() == "V");
    CHECK(r1.condition_desc() == ">= 11.5");

    auto r2 = Check::signal("E").never_equals(PhysicalValue{Rational{}});
    CHECK(r2.signal_name() == "E");
    CHECK(r2.condition_desc() == "!= 0");
}

TEST_CASE("Check when/then metadata", "[check]") {
    using namespace std::chrono_literals;
    auto result = Check::when("Brake")
                      .exceeds(PhysicalValue{Rational{50, 1}})
                      .then("Light")
                      .equals(PhysicalValue{Rational{1, 1}})
                      .within(100ms);
    CHECK(result.signal_name() == "Light");
    CHECK(result.condition_desc() == "= 1 within 100ms");
}

// ===========================================================================
// Check API — to_formula returns copy without consuming
// ===========================================================================

TEST_CASE("Check to_formula non-consuming", "[check]") {
    auto result = Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}});
    auto f1 = result.to_formula();
    REQUIRE(f1.has_value());
    auto f2 = result.to_formula();
    CHECK(f2.has_value());
}

// ===========================================================================
// Check API — error cases
// ===========================================================================

TEST_CASE("Check settles_between negative time throws", "[check]") {
    using namespace std::chrono_literals;
    auto builder = Check::signal("T").settles_between(PhysicalValue{Rational{}}, PhysicalValue{Rational{100, 1}});
    CHECK_THROWS_AS(builder.within(-1ms), std::invalid_argument);
}

TEST_CASE("Check when/then negative time throws", "[check]") {
    using namespace std::chrono_literals;
    auto cond = Check::when("A").exceeds(PhysicalValue{Rational{}}).then("B").equals(PhysicalValue{Rational{1, 1}});
    CHECK_THROWS_AS(cond.within(-1ms), std::invalid_argument);
}

// ===========================================================================
// Check API — equivalence with manual ltl:: construction
// ===========================================================================

TEST_CASE("Check never_exceeds matches manual ltl", "[check]") {
    auto check_f = Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}).to_formula();
    auto manual_f =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{220, 1}})));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check stays_between matches manual ltl", "[check]") {
    auto check_f =
        Check::signal("V").stays_between(PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}}).to_formula();
    auto manual_f = ltl::always(
        ltl::atomic(ltl::between(SignalName{"V"}, PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}})));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check never_equals matches manual ltl", "[check]") {
    auto check_f = Check::signal("Err").never_equals(PhysicalValue{Rational{255, 1}}).to_formula();
    auto manual_f = ltl::never(ltl::equals(SignalName{"Err"}, PhysicalValue{Rational{255, 1}}));
    REQUIRE(check_f);
    CHECK(format_formula(*check_f) == format_formula(manual_f));
}

TEST_CASE("Check settles matches manual ltl", "[check]") {
    using namespace std::chrono_literals;
    auto check_f = Check::signal("T")
                       .settles_between(PhysicalValue{Rational{60, 1}}, PhysicalValue{Rational{80, 1}})
                       .within(500ms)
                       .to_formula();
    auto manual_f = ltl::always_within(
        Timestamp{500'000},
        ltl::atomic(ltl::between(SignalName{"T"}, PhysicalValue{Rational{60, 1}}, PhysicalValue{Rational{80, 1}})));
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
    checks.push_back(Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    checks.push_back(
        Check::signal("Voltage").stays_between(PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}}));
    auto result = client.add_checks(std::move(checks));
    REQUIRE(result.has_value());
}

TEST_CASE("default_checks are prepended in add_checks", "[check][client]") {
    auto mock = std::make_unique<MockBackend>();
    mock->queue_response(R"({"status": "success"})");

    std::vector<CheckResult> defaults;
    defaults.push_back(
        Check::signal("Voltage").stays_between(PhysicalValue{Rational{23, 2}}, PhysicalValue{Rational{29, 2}}));

    AletheiaClient client(std::move(mock), {}, std::move(defaults));

    std::vector<CheckResult> checks;
    checks.push_back(Check::signal("Speed").never_exceeds(PhysicalValue{Rational{220, 1}}));
    auto result = client.add_checks(std::move(checks));
    REQUIRE(result.has_value());
}

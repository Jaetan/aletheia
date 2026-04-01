// YAML loader tests.
// Tests YAML check parsing through the Check API with inline YAML strings.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/yaml.hpp>

#include <filesystem>
#include <fstream>
#include <string>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Simple conditions
// ===========================================================================

TEST_CASE("yaml: never_exceeds", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: VehicleSpeed
    condition: never_exceeds
    value: 220
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: never_below", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: BatteryVoltage
    condition: never_below
    value: 11.5
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: stays_between", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: BatteryVoltage
    condition: stays_between
    min: 11.5
    max: 14.5
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: never_equals", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: ErrorCode
    condition: never_equals
    value: 99
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: equals always", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: ParkingBrake
    condition: equals
    value: 0
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: settles_between", "[yaml][simple]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: CoolantTemp
    condition: settles_between
    min: 85
    max: 95
    within_ms: 5000
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

// ===========================================================================
// When/Then conditions
// ===========================================================================

TEST_CASE("yaml: when exceeds then equals", "[yaml][when-then]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("yaml: when equals then exceeds", "[yaml][when-then]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: GearSelector
      condition: equals
      value: 1
    then:
      signal: ReverseLight
      condition: exceeds
      value: 0
    within_ms: 200
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("yaml: when drops_below then stays_between", "[yaml][when-then]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: FuelLevel
      condition: drops_below
      value: 10
    then:
      signal: FuelWarning
      condition: stays_between
      min: 1
      max: 1
    within_ms: 500
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

// ===========================================================================
// Metadata
// ===========================================================================

TEST_CASE("yaml: check name applied", "[yaml][metadata]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - name: "Speed limit"
    signal: VehicleSpeed
    condition: never_exceeds
    value: 220
)");
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Speed limit");
}

TEST_CASE("yaml: severity applied", "[yaml][metadata]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: VehicleSpeed
    condition: never_exceeds
    value: 220
    severity: critical
)");
    REQUIRE(result.has_value());
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("yaml: name and severity together", "[yaml][metadata]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - name: "Brake response"
    when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
    severity: safety
)");
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Brake response");
    CHECK((*result)[0].check_severity() == "safety");
}

TEST_CASE("yaml: defaults when no name or severity", "[yaml][metadata]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: never_exceeds
    value: 200
)");
    REQUIRE(result.has_value());
    CHECK((*result)[0].name().empty());
    CHECK((*result)[0].check_severity().empty());
}

TEST_CASE("yaml: when/then with metadata", "[yaml][metadata]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - name: "Fuel warning"
    when:
      signal: FuelLevel
      condition: drops_below
      value: 10
    then:
      signal: Warning
      condition: equals
      value: 1
    within_ms: 500
    severity: warning
)");
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Fuel warning");
    CHECK((*result)[0].check_severity() == "warning");
}

// ===========================================================================
// File I/O
// ===========================================================================

TEST_CASE("yaml: load from file", "[yaml][file]") {
    auto tmp = std::filesystem::temp_directory_path() / "aletheia_yaml_test.yaml";
    {
        std::ofstream ofs(tmp);
        ofs << R"(
checks:
  - signal: Speed
    condition: never_exceeds
    value: 200
)";
    }
    auto result = load_checks_from_yaml(tmp);
    std::filesystem::remove(tmp);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("yaml: file not found", "[yaml][file]") {
    auto result = load_checks_from_yaml("/nonexistent/path/checks.yaml");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("not found"));
}

// ===========================================================================
// Multiple checks
// ===========================================================================

TEST_CASE("yaml: multiple checks in one file", "[yaml][multi]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
  - signal: BatteryVoltage
    condition: stays_between
    min: 11.5
    max: 14.5
  - when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
)");
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 3);
}

// ===========================================================================
// Error cases
// ===========================================================================

TEST_CASE("yaml: missing checks key", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
some_other_key: 42
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("YAML must contain a 'checks' list"));
}

TEST_CASE("yaml: checks not a list", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks: "not a list"
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("YAML must contain a 'checks' list"));
}

TEST_CASE("yaml: no signal or when", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - condition: never_exceeds
    value: 220
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("must have 'signal' or 'when'/'then'"));
}

TEST_CASE("yaml: unknown simple condition", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: bogus_condition
    value: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown condition 'bogus_condition'"));
}

TEST_CASE("yaml: missing value for never_exceeds", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: never_exceeds
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("requires 'value'"));
}

TEST_CASE("yaml: missing min/max for stays_between", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: stays_between
    min: 0
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("requires 'min' and 'max'"));
}

TEST_CASE("yaml: missing within_ms for settles_between", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: settles_between
    min: 80
    max: 90
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("requires 'within_ms'"));
}

TEST_CASE("yaml: unknown when condition", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: unknown_cond
      value: 50
    then:
      signal: Light
      condition: equals
      value: 1
    within_ms: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown when condition 'unknown_cond'"));
}

TEST_CASE("yaml: unknown then condition", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: Light
      condition: bogus_then
      value: 1
    within_ms: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown then condition 'bogus_then'"));
}

TEST_CASE("yaml: named check in error message", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - name: "Speed limit"
    signal: Speed
    condition: bogus
    value: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Check 'Speed limit'"));
}

TEST_CASE("yaml: unnamed check in error message", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: bogus
    value: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Check '<unnamed>'"));
}

TEST_CASE("yaml: when without then", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("must have 'signal' or 'when'/'then'"));
}

TEST_CASE("yaml: when/then missing within_ms", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: Light
      condition: equals
      value: 1
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("when/then checks require 'within_ms'"));
}

TEST_CASE("yaml: check entry not a mapping", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - "just a string"
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("Each check must be a YAML mapping"));
}

TEST_CASE("yaml: missing value for equals", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: ParkingBrake
    condition: equals
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("requires 'value'"));
}

TEST_CASE("yaml: then stays_between missing min/max", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: Light
      condition: stays_between
      min: 1
    within_ms: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("requires 'min' and 'max'"));
}

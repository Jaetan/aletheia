// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// YAML loader tests.
// Tests YAML check parsing through the Check API with inline YAML strings.
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/enrich.hpp>
#include <aletheia/error.hpp>
#include <aletheia/yaml.hpp>

#include "temp_path.hpp"
#ifdef ALETHEIA_ALLOC_FAULT
#include "alloc_fault.hpp"
#endif

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <ios>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

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
    CHECK(format_formula(*formula) == "always(VehicleSpeed <= 220)");
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
    CHECK(format_formula(*formula) == "always(BatteryVoltage >= 11.5)");
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
    CHECK(format_formula(*formula) == "always(11.5 <= BatteryVoltage <= 14.5)");
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
    CHECK(format_formula(*formula) == "never ErrorCode = 99");
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
    CHECK(format_formula(*formula) == "always(ParkingBrake = 0)");
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
    CHECK(format_formula(*formula) == "always within 5s (85 <= CoolantTemp <= 95)");
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
    CHECK(format_formula(*formula) ==
          "always(not(BrakePedal > 50) or eventually within 100ms (BrakeLight = 1))");
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
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
    CHECK(format_formula(*formula) ==
          "always(not(GearSelector = 1) or eventually within 200ms (ReverseLight > 0))");
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
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
    CHECK(format_formula(*formula) ==
          "always(not(FuelLevel < 10) or eventually within 500ms (1 <= FuelWarning <= 1))");
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
    auto const tmp = aletheia::test::scratch_dir() / "aletheia_yaml_test.yaml";
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

TEST_CASE("yaml: stat failure is distinguished from a missing file", "[yaml][hardening]") {
    // A path whose total length exceeds PATH_MAX makes the underlying lstat
    // fail with ENAMETOOLONG — a stat *failure*, not a genuinely absent file.
    // The loader must report it as such (surfacing the errno) rather than
    // mislabelling it "file not found", which would mask resource/permission
    // failures under load (the pre-push flake that motivated this: EMFILE on a
    // present file was reported as "not found").  ENAMETOOLONG is deterministic
    // and root-safe, unlike an EACCES/chmod trigger.
    auto const tmp = std::filesystem::temp_directory_path() / (std::string(5000, 'a') + ".yaml");
    auto result = load_checks_from_yaml(tmp);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Could not stat"));
    CHECK_THAT(std::string(result.error().message()), !ContainsSubstring("not found"));
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

TEST_CASE("yaml: an empty or comment-only document has no checks list", "[yaml][error]") {
    auto const doc = GENERATE(std::string_view{""}, std::string_view{"# nothing here\n"},
                              std::string_view{"just a scalar\n"});
    auto result = load_checks_from_yaml_string(doc);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("YAML must contain a 'checks' list"));
}

TEST_CASE("yaml: a value the kernel refuses names the field", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: never_exceeds
    value: abc
)");
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("invalid 'value'"));
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

// ===========================================================================
// Adversarial-input hardening
// ===========================================================================

TEST_CASE("yaml: symlink rejected", "[yaml][hardening]") {
    auto const real = aletheia::test::scratch_dir() / "yaml_real_target.yaml";
    {
        std::ofstream ofs(real);
        ofs << "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 200\n";
    }
    auto const link = aletheia::test::scratch_dir() / "yaml_symlink.yaml";
    if (std::filesystem::exists(link))
        std::filesystem::remove(link);
    std::error_code ec;
    std::filesystem::create_symlink(real, link, ec);
    if (ec) {
        std::filesystem::remove(real);
        SUCCEED("Skipping symlink test — symlink creation not permitted on this filesystem");
        return;
    }

    auto result = load_checks_from_yaml(link);
    std::filesystem::remove(link);
    std::filesystem::remove(real);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("symbolic link"));
}

TEST_CASE("yaml: file size cap rejected", "[yaml][hardening]") {
    auto const tmp = aletheia::test::scratch_dir() / "yaml_oversize.yaml";
    {
        std::ofstream ofs(tmp, std::ios::binary);
        std::vector<char> chunk(1024UL * 1024, 'a');
        // 65 MiB, one mebibyte at a time: the count is the point, not a position.
        std::ranges::for_each(std::views::repeat(0, 65), [&](auto) {
            ofs.write(chunk.data(), static_cast<std::streamsize>(chunk.size()));
        });
    }
    auto result = load_checks_from_yaml(tmp);
    std::filesystem::remove(tmp);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    auto const& bound_info = result.error().bound_info();
    REQUIRE(bound_info.has_value());
    CHECK(bound_info->bound_kind == "input_length_bytes");
    CHECK(bound_info->limit == 64ULL * 1024 * 1024);
}

TEST_CASE("yaml: inline string size cap rejected", "[yaml][hardening]") {
    // The inline loader must enforce the same 64 MiB bound as the file loader
    // (and Go/Rust inline loaders) — an untrusted in-memory payload is a trust
    // boundary too.
    const std::string oversize(65UL * 1024 * 1024, 'a'); // 65 MiB > 64 MiB cap
    auto result = load_checks_from_yaml_string(oversize);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    auto const& bound_info = result.error().bound_info();
    REQUIRE(bound_info.has_value());
    CHECK(bound_info->bound_kind == "input_length_bytes");
    CHECK(bound_info->limit == 64ULL * 1024 * 1024);
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

// ===========================================================================
// Each key a check reads is refused in the loader's own words
// ===========================================================================
//
// Each guard below is one operand of a condition, and each test omits exactly
// the key that operand reads while every other key is present. A guard that
// stops deciding lets the read reach yaml-cpp's own refusal of an absent
// node, whose wording is not the loader's; the assertion is on the loader's.

TEST_CASE("yaml: a simple check without a condition is refused by name", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    value: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("missing or invalid 'condition' (expected string)"));
}

TEST_CASE("yaml: a when clause without a value is refused by name", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
    then:
      signal: Light
      condition: equals
      value: 1
    within_ms: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("missing or invalid 'value' (expected number)"));
}

TEST_CASE("yaml: every spelling of a boolean is refused where a number is read", "[yaml][error]") {
    auto const spelling =
        GENERATE(std::string_view{"true"}, std::string_view{"false"}, std::string_view{"TRUE"},
                 std::string_view{"FALSE"}, std::string_view{"True"}, std::string_view{"False"});
    auto result = load_checks_from_yaml_string("checks:\n  - signal: Speed\n"
                                               "    condition: never_exceeds\n    value: " +
                                               std::string{spelling} + "\n");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("missing or invalid 'value' (expected number)"));
}

TEST_CASE("yaml: stays_between with a max and no min is refused as a pair", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - signal: Speed
    condition: stays_between
    max: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("requires 'min' and 'max'"));
}

TEST_CASE("yaml: settles_between with one bound is refused as a pair, whichever is present",
          "[yaml][error]") {
    auto const present = GENERATE(std::string_view{"min"}, std::string_view{"max"});
    auto result = load_checks_from_yaml_string("checks:\n  - signal: Speed\n"
                                               "    condition: settles_between\n    " +
                                               std::string{present} + ": 80\n    within_ms: 500\n");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("condition 'settles_between' requires 'min' and 'max'"));
}

TEST_CASE("yaml: then stays_between with a max and no min is refused as a pair", "[yaml][error]") {
    auto result = load_checks_from_yaml_string(R"(
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: Light
      condition: stays_between
      max: 2
    within_ms: 100
)");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("then condition 'stays_between' requires 'min' and 'max'"));
}

#ifdef ALETHEIA_ALLOC_FAULT
// The loader fills its result one check at a time, and the container that
// grows can throw with a parsed check still in hand; that check is destroyed
// on the way out, and a cleanup that dropped it would leave its blocks behind.
TEST_CASE("yaml: the loader releases its temporaries when an allocation fails",
          "[yaml][alloc_fault]") {
    static constexpr std::string_view doc = R"(
checks:
  - name: the engine speed stays under its redline in every frame
    signal: EngineSpeedInRevolutionsPerMinute
    condition: never_exceeds
    value: 6000
  - name: the coolant temperature settles into its operating band
    signal: CoolantTemperatureInDegreesCelsius
    condition: settles_between
    min: 80
    max: 95
    within_ms: 30000
  - name: braking dims the lamp within a tenth of a second
    when:
      signal: BrakePedalPositionAsAPercentage
      condition: exceeds
      value: 50
    then:
      signal: BrakeLampIlluminationState
      condition: equals
      value: 1
    within_ms: 100
)";
    REQUIRE(load_checks_from_yaml_string(doc).has_value());
    aletheia::test::alloc_fault::expect_balanced([] { return load_checks_from_yaml_string(doc); });
}
#endif

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Cross-binding loader contract, C++ side.
//
// Reads docs/LOADER_SCENARIOS.yaml and runs each scenario through the YAML
// loader or the Excel loaders.  A rational row loads the check, or the DBC
// signal's factor, at exactly that value; a microseconds row loads the
// settles_between check with exactly that bound; a refusal row keeps the kernel's
// kind, code and bound fields, carries the location and the key the loader
// read the number at, and prints as the row's `printed`.  The other bindings'
// readers of the same file are the ones its header lists.
#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include <aletheia/check.hpp>
#include <aletheia/enrich.hpp>
#include <aletheia/error.hpp>
#include <aletheia/excel.hpp>
#include <aletheia/limits.hpp>
#include <aletheia/yaml.hpp>

#include <cstdint>
#include <filesystem>
#include <format>
#include <limits>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "excel_workbooks.hpp"
#include "repo_root.hpp"
#include "temp_path.hpp"

using aletheia::test::make_checks_workbook;
using aletheia::test::make_dbc_workbook;
using aletheia::test::repo_root;
using aletheia::test::TempPath;

using namespace aletheia;

namespace {

struct Refusal {
    ErrorKind kind;
    std::string code; // the kernel's wire code
    std::string location;
    std::string key;
    std::string printed;
    std::optional<InputBoundExceededError> bound;
};

struct Scenario {
    std::string name;
    std::string sheet; // Excel only
    std::string value;
    std::variant<Rational, TimeBound, Refusal> expect;
};

} // namespace

static auto kind_of(std::string const& kind) -> ErrorKind {
    REQUIRE((kind == "validation" || kind == "input_bound_exceeded"));
    return kind == "validation" ? ErrorKind::Validation : ErrorKind::InputBoundExceeded;
}

// A whole number of the contract, read from its digits: its magnitude reaches
// 2^128-1, past every integer yaml-cpp converts to.
static auto whole_of(YAML::Node const& node) -> SignMagnitude {
    auto const text = node.as<std::string>();
    auto const negative = text.starts_with('-');
    auto const digits = std::string_view{text}.substr(negative ? 1 : 0);
    REQUIRE_FALSE(digits.empty());
    constexpr auto max = std::numeric_limits<unsigned __int128>::max();
    unsigned __int128 magnitude = 0;
    for (auto const c : digits) {
        REQUIRE((c >= '0' && c <= '9'));
        auto const digit = static_cast<unsigned __int128>(c - '0');
        REQUIRE(magnitude <= (max - digit) / 10);
        magnitude = (magnitude * 10) + digit;
    }
    return SignMagnitude{.negative = negative, .magnitude = magnitude};
}

// A row gives one answer, a rational, microseconds or a refusal; a reading
// given with anything else is a mistake in the contract.
static auto expectation_of(YAML::Node const& expect) -> std::variant<Rational, TimeBound, Refusal> {
    if (auto const rational = expect["rational"]) {
        REQUIRE_FALSE(expect["microseconds"].IsDefined());
        REQUIRE_FALSE(expect["kind"].IsDefined());
        auto const numerator = whole_of(rational[0]);
        auto const denominator = whole_of(rational[1]);
        REQUIRE_FALSE(denominator.negative);
        return Rational::make(numerator.negative, numerator.magnitude, denominator.magnitude)
            .value();
    }
    if (auto const microseconds = expect["microseconds"]) {
        REQUIRE_FALSE(expect["kind"].IsDefined());
        return TimeBound{microseconds.as<std::uint64_t>()};
    }
    std::optional<InputBoundExceededError> bound;
    if (auto const node = expect["bound"])
        bound = InputBoundExceededError{
            .bound_kind = node["kind"].as<std::string>(),
            .observed = whole_of(node["observed"]).magnitude,
            .limit = whole_of(node["limit"]).magnitude,
            .field = node["field"].as<std::string>(),
        };
    return Refusal{
        .kind = kind_of(expect["kind"].as<std::string>()),
        .code = expect["code"].as<std::string>(),
        .location = expect["location"].as<std::string>(),
        .key = expect["key"].as<std::string>(),
        .printed = expect["printed"].as<std::string>(),
        .bound = bound,
    };
}

static auto scenarios(char const* section) -> std::vector<Scenario> {
    auto const path = repo_root() / "docs" / "LOADER_SCENARIOS.yaml";
    REQUIRE(std::filesystem::exists(path));
    auto const root = YAML::LoadFile(path.string());
    REQUIRE(root[section].IsSequence());
    REQUIRE(root[section].size() > 0);

    std::vector<Scenario> out;
    std::set<std::string> names;
    out.reserve(root[section].size());
    for (auto const& node : root[section]) {
        auto const name = node["name"].as<std::string>();
        INFO(section << " scenario " << name);
        // Catch2 runs a dynamic section once per name, so a row named as an
        // earlier one would never run.
        REQUIRE(names.insert(name).second);
        out.push_back(Scenario{
            .name = name,
            .sheet = node["sheet"] ? node["sheet"].as<std::string>() : std::string{},
            .value = node["value"].as<std::string>(),
            .expect = expectation_of(node["expect"]),
        });
    }
    return out;
}

// The loaded value, or a failure printing the refusal in its place.
template<typename T>
static auto loaded(Result<T> const& result) -> T const& {
    if (!result.has_value())
        FAIL("refused where the contract loads: " << result.error().text());
    return *result;
}

// The refusal, or a failure where the loader loaded the number.
template<typename T>
static auto refused(Result<T> const& result) -> AletheiaError const& {
    if (result.has_value())
        FAIL("loaded where the contract refuses");
    return result.error();
}

// A member the error lacks reads as "(absent)", which no row expects, so the
// comparison fails and prints it.
static auto shown(std::optional<std::string> const& member) -> std::string {
    return member.value_or("(absent)");
}

// A rational as its sign, numerator and denominator, for a failure to print.
static auto shown(Rational const& r) -> std::string {
    return std::format("{}{}/{}", r.negative() ? "-" : "", r.numerator(), r.denominator());
}

static void check_rational(Rational const& got, Rational const& want) {
    INFO("loaded " << shown(got) << ", contract " << shown(want));
    CHECK(got == want);
}

// The bound of a never_exceeds check: the value under its Always and Atomic.
static auto threshold(CheckResult const& check) -> Rational {
    auto const& always = std::get<Always>(check.formula().value);
    auto const& atomic = std::get<Atomic>(always.formula->value);
    return std::get<LessThanOrEqual>(atomic.predicate).value.get();
}

// Every rational row's check: Speed never exceeding the row's value, as the
// Check API builds it.
static void check_never_exceeds(std::vector<CheckResult> const& checks, Rational const& want) {
    REQUIRE(checks.size() == 1);
    auto const built = check::signal("Speed").never_exceeds(PhysicalValue{want});
    REQUIRE(built.has_value());
    CHECK(format_formula(checks.front().to_formula()) ==
          format_formula(built->to_formula()).value());
    check_rational(threshold(checks.front()), want);
}

// The bound of a settles_between check: the window of its MetricAlways.
static auto window(CheckResult const& check) -> TimeBound {
    return std::get<MetricAlways>(check.formula().value).bound;
}

// Every microseconds row's check: Speed settling between 0 and 100 within the
// row's bound, as the Check API builds it.
static void check_settles_within(std::vector<CheckResult> const& checks, TimeBound want) {
    REQUIRE(checks.size() == 1);
    auto const built =
        check::signal("Speed")
            .settles_between(PhysicalValue{Rational{0, 1}}, PhysicalValue{Rational{100, 1}})
            .within(want);
    REQUIRE(built.has_value());
    CHECK(format_formula(checks.front().to_formula()) ==
          format_formula(built->to_formula()).value());
    INFO("loaded " << window(checks.front()).microseconds << "us, contract " << want.microseconds
                   << "us");
    CHECK(window(checks.front()) == want);
}

static void check_refusal(AletheiaError const& error, Refusal const& want) {
    INFO("wire code " << want.code << ", message " << error.message());
    auto const code = error_code_from_string(want.code);
    REQUIRE(code.has_value());
    CHECK(error.kind() == want.kind);
    CHECK(error.code() == code);
    CHECK(shown(error.location()) == want.location);
    CHECK(shown(error.key()) == want.key);
    CHECK(error.text() == want.printed);
    if (!want.bound) {
        CHECK_FALSE(error.bound_info().has_value());
        return;
    }
    REQUIRE(error.bound_info().has_value());
    auto const& got = *error.bound_info();
    CHECK(got.bound_kind == want.bound->bound_kind);
    CHECK(got.observed == want.bound->observed);
    CHECK(got.limit == want.bound->limit);
    CHECK(shown(got.field) == shown(want.bound->field));
}

// The contract's check document with the row's value written verbatim.
static auto yaml_document(std::string const& value) -> std::string {
    return "checks:\n"
           "  - name: \"C\"\n"
           "    signal: Speed\n"
           "    condition: never_exceeds\n"
           "    value: " +
           value + "\n";
}

// The contract's settles_between document with the row's bound written verbatim.
static auto yaml_within_us_document(std::string const& value) -> std::string {
    return "checks:\n"
           "  - name: \"C\"\n"
           "    signal: Speed\n"
           "    condition: settles_between\n"
           "    min: 0\n"
           "    max: 100\n"
           "    within_us: " +
           value + "\n";
}

TEST_CASE("loader scenarios: the YAML loader answers each number as the contract reads it",
          "[loader_scenarios][yaml]") {
    for (auto const& scenario : scenarios("yaml")) {
        DYNAMIC_SECTION("yaml scenario " << scenario.name) {
            auto const result = load_checks_from_yaml_string(yaml_document(scenario.value));
            if (auto const* want = std::get_if<Rational>(&scenario.expect))
                check_never_exceeds(loaded(result), *want);
            else
                check_refusal(refused(result), std::get<Refusal>(scenario.expect));
        }
    }
}

TEST_CASE("loader scenarios: the YAML loader answers each within_us as the contract reads it",
          "[loader_scenarios][yaml]") {
    for (auto const& scenario : scenarios("yaml_within_us")) {
        DYNAMIC_SECTION("yaml_within_us scenario " << scenario.name) {
            auto const result =
                load_checks_from_yaml_string(yaml_within_us_document(scenario.value));
            if (auto const* want = std::get_if<TimeBound>(&scenario.expect))
                check_settles_within(loaded(result), *want);
            else
                check_refusal(refused(result), std::get<Refusal>(scenario.expect));
        }
    }
}

TEST_CASE("loader scenarios: the Excel loaders answer each number as the contract reads it",
          "[loader_scenarios][excel]") {
    for (auto const& scenario : scenarios("excel")) {
        DYNAMIC_SECTION("excel scenario " << scenario.name) {
            REQUIRE((scenario.sheet == "Checks" || scenario.sheet == "DBC"));
            TempPath const tf("loader_scenario_" + scenario.name + ".xlsx");
            if (scenario.sheet == "Checks") {
                make_checks_workbook(
                    tf.path, {{"C", "Speed", "never_exceeds", scenario.value, "", "", "", ""}});
                auto const result = load_checks_from_excel(tf.path);
                if (auto const* want = std::get_if<Rational>(&scenario.expect))
                    check_never_exceeds(loaded(result), *want);
                else
                    check_refusal(refused(result), std::get<Refusal>(scenario.expect));
            } else {
                // The contract's row under the shared header's column order:
                // every cell a text cell but Signed, a boolean FALSE.
                make_dbc_workbook(tf.path,
                                  {{"256", "M", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                    scenario.value, "0", "0", "1", "", "", "", ""}});
                auto const result = load_dbc_from_excel(tf.path);
                if (auto const* want = std::get_if<Rational>(&scenario.expect)) {
                    auto const& dbc = loaded(result);
                    REQUIRE(dbc.messages.size() == 1);
                    REQUIRE(dbc.messages.front().signals.size() == 1);
                    check_rational(dbc.messages.front().signals.front().factor.get(), *want);
                } else {
                    check_refusal(refused(result), std::get<Refusal>(scenario.expect));
                }
            }
        }
    }
}

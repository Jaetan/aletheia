// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Cross-binding loader contract, C++ side.
//
// Reads docs/LOADER_SCENARIOS.yaml and runs each scenario through the YAML
// loader or the Excel loaders.  A rational row loads the check, or the DBC
// signal's factor, at exactly that value; a milliseconds row loads the
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

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <set>
#include <string>
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
    std::variant<Rational, std::chrono::milliseconds, Refusal> expect;
};

} // namespace

static auto kind_of(const std::string& kind) -> ErrorKind {
    REQUIRE((kind == "validation" || kind == "input_bound_exceeded"));
    return kind == "validation" ? ErrorKind::Validation : ErrorKind::InputBoundExceeded;
}

// A row gives one answer, a rational, milliseconds or a refusal; a reading
// given with anything else is a mistake in the contract.
static auto expectation_of(const YAML::Node& expect)
    -> std::variant<Rational, std::chrono::milliseconds, Refusal> {
    if (auto const rational = expect["rational"]) {
        REQUIRE_FALSE(expect["milliseconds"].IsDefined());
        REQUIRE_FALSE(expect["kind"].IsDefined());
        return Rational::make(rational[0].as<std::int64_t>(), rational[1].as<std::int64_t>())
            .value();
    }
    if (auto const milliseconds = expect["milliseconds"]) {
        REQUIRE_FALSE(expect["kind"].IsDefined());
        return std::chrono::milliseconds{milliseconds.as<std::int64_t>()};
    }
    std::optional<InputBoundExceededError> bound;
    if (auto const node = expect["bound"])
        bound = InputBoundExceededError{
            .bound_kind = node["kind"].as<std::string>(),
            .observed = node["observed"].as<std::uint64_t>(),
            .limit = node["limit"].as<std::uint64_t>(),
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

static auto scenarios(const char* section) -> std::vector<Scenario> {
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
static auto loaded(const Result<T>& result) -> const T& {
    if (!result.has_value())
        FAIL("refused where the contract loads: " << result.error().text());
    return *result;
}

// The refusal, or a failure where the loader loaded the number.
template<typename T>
static auto refused(const Result<T>& result) -> const AletheiaError& {
    if (result.has_value())
        FAIL("loaded where the contract refuses");
    return result.error();
}

// A member the error lacks reads as "(absent)", which no row expects, so the
// comparison fails and prints it.
static auto shown(const std::optional<std::string>& member) -> std::string {
    return member.value_or("(absent)");
}

static void check_rational(const Rational& got, const Rational& want) {
    INFO("loaded " << got.numerator() << "/" << got.denominator() << ", contract "
                   << want.numerator() << "/" << want.denominator());
    CHECK(got == want);
}

// The bound of a never_exceeds check: the value under its Always and Atomic.
static auto threshold(const CheckResult& check) -> Rational {
    auto const& always = std::get<Always>(check.formula().value);
    auto const& atomic = std::get<Atomic>(always.formula->value);
    return std::get<LessThanOrEqual>(atomic.predicate).value.get();
}

// Every rational row's check: Speed never exceeding the row's value, as the
// Check API builds it.
static void check_never_exceeds(const std::vector<CheckResult>& checks, const Rational& want) {
    REQUIRE(checks.size() == 1);
    auto const built = check::signal("Speed").never_exceeds(PhysicalValue{want});
    CHECK(format_formula(checks.front().to_formula()) ==
          format_formula(built.to_formula()).value());
    check_rational(threshold(checks.front()), want);
}

// The bound of a settles_between check: the window of its MetricAlways.
static auto window(const CheckResult& check) -> Timestamp {
    return std::get<MetricAlways>(check.formula().value).bound;
}

// Every milliseconds row's check: Speed settling between 0 and 100 within the
// row's bound, as the Check API builds it.
static void check_settles_within(const std::vector<CheckResult>& checks,
                                 std::chrono::milliseconds want) {
    REQUIRE(checks.size() == 1);
    auto const built =
        check::signal("Speed")
            .settles_between(PhysicalValue{Rational{0, 1}}, PhysicalValue{Rational{100, 1}})
            .within(want);
    REQUIRE(built.has_value());
    CHECK(format_formula(checks.front().to_formula()) ==
          format_formula(built->to_formula()).value());
    INFO("loaded " << window(checks.front()).count() << "us, contract " << want.count() << "ms");
    CHECK(window(checks.front()) == want);
}

static void check_refusal(const AletheiaError& error, const Refusal& want) {
    INFO("wire code " << want.code << ", message " << error.message());
    auto const code = error_code_from_string(want.code);
    REQUIRE(code != ErrorCode::Unknown);
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
static auto yaml_document(const std::string& value) -> std::string {
    return "checks:\n"
           "  - name: \"C\"\n"
           "    signal: Speed\n"
           "    condition: never_exceeds\n"
           "    value: " +
           value + "\n";
}

// The contract's settles_between document with the row's bound written verbatim.
static auto yaml_within_ms_document(const std::string& value) -> std::string {
    return "checks:\n"
           "  - name: \"C\"\n"
           "    signal: Speed\n"
           "    condition: settles_between\n"
           "    min: 0\n"
           "    max: 100\n"
           "    within_ms: " +
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

TEST_CASE("loader scenarios: the YAML loader answers each within_ms as the contract reads it",
          "[loader_scenarios][yaml]") {
    for (auto const& scenario : scenarios("yaml_within_ms")) {
        DYNAMIC_SECTION("yaml_within_ms scenario " << scenario.name) {
            auto const result =
                load_checks_from_yaml_string(yaml_within_ms_document(scenario.value));
            if (auto const* want = std::get_if<std::chrono::milliseconds>(&scenario.expect))
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
            const TempPath tf("loader_scenario_" + scenario.name + ".xlsx");
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

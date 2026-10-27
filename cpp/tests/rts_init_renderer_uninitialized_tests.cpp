// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer and the decimal parser do not start the GHC runtime
// (cpp/src/detail/rts_init.hpp and rational_renderer.cpp). These cases assert
// they are vocal when nothing has started it: a call before a start returns
// an error naming the remedy, rather than starting the runtime, which would
// fix its core count before the program chose one, or calling the kernel with
// the runtime down. Every render of a threshold returns the renderer's. The
// allocation count, which only a started runtime keeps, answers none. Every
// loader reads its numbers, a DBC's message ID aside, through the decimal
// parser and returns that refusal as the parser returned it, kind, code and
// text, starting nothing; a loader's own refusal of a path or a document
// answers on its input.
//
// Must run in its own process, a child of fresh_process_tests, because the GHC
// RTS is process-global: any start in the same process would bring the runtime
// up and defeat the assertion. The listener that starts the runtime for the
// other suites, rts_setup_listener.cpp, is linked into those binaries and not
// into this one.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <OpenXLSX.hpp>

#include "detail/mock_backend.hpp"

#include <array>
#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <ranges>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "repo_root.hpp"
#include "required.hpp"
#include "temp_path.hpp"

using aletheia::test::required;

// The refusal while the runtime is down, after the words naming what the call was doing.
static auto runtime_down(std::string_view reading) -> std::string {
    return "GHC runtime not initialized: call aletheia::start_runtime or open a client before " +
           std::string{reading};
}

// A call made with the runtime down: kind Ffi, no wire code, the refusal naming
// what the call was doing.
template<typename T>
static void requires_runtime_down(const aletheia::Result<T>& answered, std::string_view reading) {
    REQUIRE_FALSE(answered.has_value());
    CHECK(answered.error().kind() == aletheia::ErrorKind::Ffi);
    CHECK(answered.error().code() == aletheia::ErrorCode::Unknown);
    CHECK(answered.error().text() == runtime_down(reading));
}

TEST_CASE("the renderer returns the runtime's refusal when the GHC runtime is down",
          "[rational_renderer][rts_init]") {
    requires_runtime_down(aletheia::detail::format_rational_ffi(22, 7), "rendering");
}

TEST_CASE("Rational::from_decimal returns the runtime's refusal when the GHC runtime is down",
          "[rational_renderer][rts_init][decimal]") {
    requires_runtime_down(aletheia::Rational::from_decimal("3.14"), "parsing decimals");
}

TEST_CASE("every render of a check's threshold returns the runtime's refusal while it is down",
          "[check][enrich][rts_init]") {
    auto const check =
        aletheia::check::signal("Speed").never_exceeds(aletheia::PhysicalValue::of(220, 1));
    requires_runtime_down(check.condition_desc(), "rendering");
    requires_runtime_down(aletheia::format_formula(check.formula()), "rendering");
    requires_runtime_down(aletheia::build_diagnostic(check.formula()), "rendering");
}

TEST_CASE("an inverted range's refusal names its bounds while the runtime is down",
          "[check][rts_init]") {
    // A check is built before any start too, so its range refusal prints each
    // bound as `n` or `n/d` rather than failing on the renderer.
    auto const refused = [](const aletheia::Result<aletheia::CheckResult>& built) {
        REQUIRE_FALSE(built.has_value());
        CHECK(built.error().kind() == aletheia::ErrorKind::Validation);
        return std::string{built.error().text()};
    };
    auto const sig = aletheia::check::signal("Speed");
    CHECK(refused(sig.stays_between(aletheia::PhysicalValue::of(10, 1),
                                    aletheia::PhysicalValue::of(5, 1))) ==
          "stays_between: lo (10) must be <= hi (5)");
    CHECK(refused(sig.stays_between(aletheia::PhysicalValue::of(1, 2),
                                    aletheia::PhysicalValue::of(0, 1))) ==
          "stays_between: lo (1/2) must be <= hi (0)");
}

TEST_CASE("properties the kernel accepted return the renderer's refusal while it is down",
          "[client][rts_init]") {
    // The double accepts what it is sent, so the refusal is the diagnostic's
    // render, after the command reached the backend.
    auto const check = [] {
        return aletheia::check::signal("Speed").never_exceeds(aletheia::PhysicalValue::of(220, 1));
    };
    auto mock = std::make_unique<aletheia::MockBackend>();
    auto const* const backend = mock.get();
    mock->queue_response(R"({"status": "success"})");
    mock->queue_response(R"({"status": "success"})");
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));
    std::vector<aletheia::LtlFormula> properties;
    properties.push_back(check().to_formula());
    requires_runtime_down(client.set_properties(std::stop_token{}, properties), "rendering");
    std::vector<aletheia::CheckResult> checks;
    checks.push_back(check());
    requires_runtime_down(client.add_checks(std::stop_token{}, std::move(checks)), "rendering");
    CHECK(backend->captured().size() == 2);
}

TEST_CASE("a runtime-down decimal parse answers on the runtime, not on the literal",
          "[rational_renderer][rts_init][decimal]") {
    // An interior NUL is refused with a Validation error once the runtime is up,
    // but the runtime gate comes first: Rust returns RtsNotInitialized before it
    // looks at the literal, so a runtime-down call here must name the runtime too
    // rather than the input. This pins the order the two bindings share.
    using namespace std::string_view_literals;
    requires_runtime_down(aletheia::Rational::from_decimal("1\0xyz"sv), "parsing decimals");
}

TEST_CASE("the allocation count answers none while the runtime is down", "[ffi][rts_init]") {
    // Nothing has started the runtime in this process, so no library holds a
    // count to read.
    CHECK(aletheia::allocated_bytes() == std::nullopt);
}

// A load that reads a number with the runtime down: the decimal parser's
// refusal as the parser returned it, unlocated, and the runtime still down
// after it.
template<typename T>
static void requires_the_runtime_refusal(const aletheia::Result<T>& loaded) {
    requires_runtime_down(loaded, "parsing decimals");
    CHECK(aletheia::allocated_bytes() == std::nullopt);
}

// A workbook holding a When-Then sheet alone, its one row's numbers written as
// text, so a load of it reads no other sheet.
static void write_when_then_workbook(const std::filesystem::path& path) {
    static constexpr std::array<std::string_view, 11> headers{
        "Check Name",  "When Signal",    "When Condition", "When Value",
        "Then Signal", "Then Condition", "Then Value",     "Then Min",
        "Then Max",    "Within (ms)",    "Severity"};
    static constexpr std::array<std::string_view, 11> row{
        "", "BrakePedal", "exceeds", "50", "BrakeLight", "equals", "1", "", "", "100", ""};
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("When-Then");
    auto const sheet = doc.workbook().worksheet("When-Then");
    for (auto const [column, header, cell] :
         std::views::zip(std::views::iota(std::uint16_t{1}), headers, row)) {
        sheet.cell(1, column).value() = std::string{header};
        if (!cell.empty())
            sheet.cell(2, column).value() = std::string{cell};
    }
    doc.save();
    doc.close();
}

TEST_CASE("every loader returns the runtime's refusal unlocated while the runtime is down",
          "[excel][yaml][rts_init][decimal]") {
    // Each source holds a number, so each load reads one; a YAML when-then
    // check reads its time bound first.
    static constexpr std::string_view document =
        "checks:\n  - name: c\n    signal: Speed\n    condition: never_exceeds\n    value: 11.5\n";
    static constexpr std::string_view when_then =
        "checks:\n  - name: w\n    when:\n      signal: Brake\n      condition: exceeds\n"
        "      value: 50\n    then:\n      signal: Light\n      condition: equals\n"
        "      value: 1\n    within_ms: 100\n";
    auto const workbook = aletheia::test::repo_root() / "examples" / "demo" / "demo_workbook.xlsx";
    SECTION("YAML text") {
        requires_the_runtime_refusal(aletheia::load_checks_from_yaml_string(document));
    }
    SECTION("a when-then document") {
        requires_the_runtime_refusal(aletheia::load_checks_from_yaml_string(when_then));
    }
    SECTION("a YAML file") {
        const aletheia::test::TempPath file("runtime_down_checks.yaml", document);
        requires_the_runtime_refusal(aletheia::load_checks_from_yaml(file.path));
    }
    SECTION("a workbook's checks") {
        requires_the_runtime_refusal(aletheia::load_checks_from_excel(workbook));
    }
    SECTION("a workbook's when-then sheet alone") {
        const aletheia::test::TempPath file("runtime_down_when_then.xlsx");
        write_when_then_workbook(file.path);
        requires_the_runtime_refusal(aletheia::load_checks_from_excel(file.path));
    }
    SECTION("a workbook's DBC") {
        requires_the_runtime_refusal(aletheia::load_dbc_from_excel(workbook));
    }
}

TEST_CASE("a loader's own refusal answers on its input, not on the runtime",
          "[excel][yaml][rts_init]") {
    SECTION("a missing workbook") {
        auto const missing = aletheia::load_checks_from_excel("does-not-exist.xlsx");
        REQUIRE_FALSE(missing.has_value());
        CHECK(missing.error().kind() == aletheia::ErrorKind::Validation);
        CHECK(missing.error().code() == aletheia::ErrorCode::Unknown);
        CHECK(missing.error().text() == "Excel file not found: does-not-exist.xlsx");
    }
    SECTION("a document holding no checks list") {
        auto const malformed = aletheia::load_checks_from_yaml_string("not: a checks list\n");
        REQUIRE_FALSE(malformed.has_value());
        CHECK(malformed.error().kind() == aletheia::ErrorKind::Validation);
        CHECK(malformed.error().code() == aletheia::ErrorCode::Unknown);
        CHECK(malformed.error().text() == "YAML must contain a 'checks' list");
    }
}

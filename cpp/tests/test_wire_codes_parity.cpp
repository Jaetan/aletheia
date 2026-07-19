// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Cross-binding wire-code vocabulary parity — C++ side.
//
// Reads docs/WIRE_CODES.yaml (the cross-binding SSOT, itself anchored to the
// Agda kernel by the `check-wire-codes` run_ci gate) and asserts the two C++
// vocabulary enums are each a bijection with their YAML section:
//
//   issue_codes <-> enum class IssueCode (validation_issue.hpp), rendered
//                   through the public to_string() — which shares the JSON
//                   decoder's issue_code_table, so string<->enum round-trips
//                   exactly and a table gap surfaces as "unknown" here.
//   error_codes <-> enum class ErrorCode (error.hpp), decoded through the
//                   public error_code_from_string().
//
// Completeness argument per section: the named-enumerator count is anchored
// on the enum declaration (IssueCode declares Unknown LAST, so the named
// range is [0, Unknown); ErrorCode declares Unknown FIRST, so the anchor is
// its last named enumerator). Given count(YAML) == count(named enumerators)
// and every YAML code mapping to a DISTINCT non-Unknown enumerator
// (injectivity via a std::set), the mapping is a bijection by pigeonhole —
// so a removed lookup-table entry, a removed enumerator, and a kernel code
// with no C++ member all fail. A new enumerator appended after the anchor
// fails the count check until the anchor moves, so the anchor cannot rot
// silently. The decoders' deliberate runtime leniency (unknown wire code ->
// Unknown sentinel + preserved code_raw for issues) is the forward-compat
// channel; the canary below asserts it rather than weakening it.
//
// Mirrors python/tests/test_wire_codes_parity.py,
// go/aletheia/wire_codes_parity_test.go, and rust/tests/wire_codes.rs, with
// the same YAML mechanics as test_log_events_parity.cpp.
#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include <aletheia/error.hpp>
#include <aletheia/validation_issue.hpp>

#include <cstddef>
#include <cstdlib>
#include <filesystem>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using namespace aletheia;

namespace {

// Repo root via env var, see test_feature_matrix_parity.cpp.
auto repo_root() -> std::filesystem::path {
    if (const char* env = std::getenv("ALETHEIA_REPO_ROOT"); env != nullptr && *env != '\0') {
        return std::filesystem::path{env};
    }
    throw std::runtime_error("ALETHEIA_REPO_ROOT env var not set; expected to be passed by ctest "
                             "via set_tests_properties(ENVIRONMENT ...) in cpp/CMakeLists.txt");
}

struct WireCodeRow {
    std::string name;
    std::string description;
};

auto load_section(const char* section) -> std::vector<WireCodeRow> {
    const auto path = repo_root() / "docs" / "WIRE_CODES.yaml";
    REQUIRE(std::filesystem::exists(path));
    auto root = YAML::LoadFile(path.string());
    REQUIRE(root[section]);
    REQUIRE(root[section].IsSequence());
    REQUIRE(root[section].size() > 0);

    std::vector<WireCodeRow> out;
    out.reserve(root[section].size());
    for (const auto& node : root[section]) {
        out.push_back(WireCodeRow{
            .name = node["name"].as<std::string>(),
            .description = node["description"].as<std::string>(),
        });
    }
    return out;
}

auto name_set(const std::vector<WireCodeRow>& rows) -> std::set<std::string> {
    std::set<std::string> names;
    for (const auto& row : rows) {
        INFO("duplicate name: " << row.name);
        REQUIRE(names.insert(row.name).second);
    }
    return names;
}

// Named (non-sentinel) enumerator counts, anchored on the enum declarations.
// IssueCode: Unknown is declared last, so it doubles as the named count.
constexpr auto k_named_issue_count = static_cast<std::size_t>(IssueCode::Unknown);
// ErrorCode: Unknown is declared first (value 0), so the anchor is the last
// named enumerator's value. Appending a new enumerator after it fails the
// count checks below until this anchor is moved to the new last member.
constexpr auto k_named_error_count =
    static_cast<std::size_t>(ErrorCode::ExtractionBitExtractionFailed);

} // namespace

// ----- 1. YAML schema sanity -----

TEST_CASE("WIRE_CODES.yaml is well-formed", "[parity][wire_codes][yaml]") {
    for (const char* section : {"issue_codes", "error_codes"}) {
        auto rows = load_section(section);
        std::set<std::string> seen;
        for (std::size_t i = 0; i < rows.size(); ++i) {
            const auto& row = rows[i];
            INFO(section << "[" << i << "] name=" << row.name);
            CHECK_FALSE(row.name.empty());
            CHECK(seen.insert(row.name).second);
            CHECK_FALSE(row.description.empty());
        }
    }
}

// ----- 2. issue_codes <-> IssueCode bijection -----

TEST_CASE("issue codes are a bijection with the IssueCode enum", "[parity][wire_codes][issue]") {
    const auto yaml_names = name_set(load_section("issue_codes"));
    REQUIRE(yaml_names.size() == k_named_issue_count);

    // Binding -> YAML: every named enumerator renders to a wire string the
    // SSOT knows. to_string() falls back to "unknown" for an enumerator
    // missing from the decoder's lookup table, which is never a YAML row
    // (see the sentinel canary), so a table gap fails here too.
    std::set<std::string> rendered;
    for (std::size_t i = 0; i < k_named_issue_count; ++i) {
        const auto name = std::string{to_string(static_cast<IssueCode>(i))};
        INFO("IssueCode enumerator " << i << " renders as: " << name);
        CHECK(yaml_names.contains(name));
        rendered.insert(name);
    }
    // Injectivity: every named enumerator -> a distinct wire string; with the
    // count anchor above this closes the bijection (YAML -> binding included).
    CHECK(rendered.size() == k_named_issue_count);
}

// ----- 3. error_codes <-> ErrorCode bijection -----

TEST_CASE("error codes are a bijection with the ErrorCode enum", "[parity][wire_codes][error]") {
    const auto yaml_names = name_set(load_section("error_codes"));
    REQUIRE(yaml_names.size() == k_named_error_count);

    // YAML -> binding: every kernel code decodes to a distinct non-Unknown
    // enumerator. With the count anchor above, injectivity closes the
    // bijection by pigeonhole — no named enumerator can lack a YAML row.
    std::set<ErrorCode> decoded;
    for (const auto& name : yaml_names) {
        const auto code = error_code_from_string(name);
        INFO("error code with no non-Unknown ErrorCode member: " << name);
        CHECK(code != ErrorCode::Unknown);
        decoded.insert(code);
    }
    CHECK(decoded.size() == k_named_error_count);
}

// ----- 4. sentinel canary -----

// The Unknown sentinels are binding-local forward-compat defaults, not wire
// codes: the kernel never emits "unknown"/"some_future_code", the SSOT must
// not list them, and the decoder must keep degrading them leniently (the
// version-skew channel this parity gate deliberately leaves intact).
TEST_CASE("unknown codes stay outside the canonical vocabulary", "[parity][wire_codes][canary]") {
    CHECK_FALSE(name_set(load_section("issue_codes")).contains("unknown"));
    CHECK(error_code_from_string("some_future_code") == ErrorCode::Unknown);
}

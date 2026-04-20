// Feature matrix parity test — C++ side.
//
// Reads docs/FEATURE_MATRIX.yaml and verifies:
//
//   1. Every feature row has a well-formed schema (id / name / description /
//      bindings for all three languages, each with a valid status).
//   2. Every binding with status=implemented carries an entry field.
//   3. Every C++ implemented entry (format "<header>#<symbol>") resolves —
//      the header exists under cpp/include/ and contains the symbol as a
//      whole-word match. Catches silent removal or rename.
//   4. Every binding with status=not_applicable carries a non-empty reason.
//
// Failure here means the C++ public surface drifted from what the matrix
// declares. Fix: either the code (add the symbol back), or the matrix
// (mark the feature as planned or not_applicable with justification).
//
// See docs/development/PARITY_PLAN.md for the rationale and roadmap.

#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>

#ifndef ALETHEIA_REPO_ROOT
#error "ALETHEIA_REPO_ROOT must be defined at compile time by CMake"
#endif

namespace {

constexpr std::array<std::string_view, 3> kValidStatuses = {
    "implemented", "not_applicable", "planned"};

constexpr std::array<std::string_view, 3> kBindings = {"python", "cpp", "go"};

auto repo_root() -> std::filesystem::path {
    return std::filesystem::path{ALETHEIA_REPO_ROOT};
}

auto matrix_path() -> std::filesystem::path {
    return repo_root() / "docs" / "FEATURE_MATRIX.yaml";
}

auto cpp_include_root() -> std::filesystem::path {
    return repo_root() / "cpp" / "include";
}

auto load_matrix() -> YAML::Node {
    const auto path = matrix_path();
    REQUIRE(std::filesystem::exists(path));
    auto root = YAML::LoadFile(path.string());
    REQUIRE(root["features"]);
    REQUIRE(root["features"].IsSequence());
    REQUIRE(root["features"].size() > 0);
    return root;
}

auto read_file(const std::filesystem::path& path) -> std::string {
    std::ifstream in{path};
    std::ostringstream ss;
    ss << in.rdbuf();
    return ss.str();
}

auto is_ident_char(char c) -> bool {
    return (std::isalnum(static_cast<unsigned char>(c)) != 0) || c == '_';
}

// Overwrite C/C++ comments, string literals, and character literals with
// spaces (newlines preserved so offsets and line numbers still line up).
// Prevents a stale "// removed AletheiaClient" comment from satisfying a
// whole-word symbol check after the class has actually been deleted.
auto strip_lexical_noise(std::string text) -> std::string {
    const auto n = text.size();
    for (std::size_t i = 0; i < n;) {
        const char c = text[i];
        if (c == '/' && i + 1 < n && text[i + 1] == '/') {
            while (i < n && text[i] != '\n') {
                text[i++] = ' ';
            }
        } else if (c == '/' && i + 1 < n && text[i + 1] == '*') {
            text[i] = text[i + 1] = ' ';
            i += 2;
            while (i + 1 < n && !(text[i] == '*' && text[i + 1] == '/')) {
                if (text[i] != '\n') {
                    text[i] = ' ';
                }
                ++i;
            }
            if (i + 1 < n) {
                text[i] = text[i + 1] = ' ';
                i += 2;
            }
        } else if (c == '"' || c == '\'') {
            const char quote = c;
            text[i++] = ' ';
            while (i < n && text[i] != quote) {
                if (text[i] == '\\' && i + 1 < n) {
                    if (text[i] != '\n') {
                        text[i] = ' ';
                    }
                    ++i;
                }
                if (i < n && text[i] != '\n') {
                    text[i] = ' ';
                }
                ++i;
            }
            if (i < n) {
                text[i++] = ' ';
            }
        } else {
            ++i;
        }
    }
    return text;
}

auto symbol_present(const std::string& text, const std::string& symbol) -> bool {
    if (symbol.empty()) {
        return false;
    }
    std::size_t pos = 0;
    while ((pos = text.find(symbol, pos)) != std::string::npos) {
        const bool left_ok = (pos == 0) || !is_ident_char(text[pos - 1]);
        const std::size_t right_idx = pos + symbol.size();
        const bool right_ok = (right_idx >= text.size()) || !is_ident_char(text[right_idx]);
        if (left_ok && right_ok) {
            return true;
        }
        ++pos;
    }
    return false;
}

auto is_valid_status(std::string_view status) -> bool {
    return std::find(kValidStatuses.begin(), kValidStatuses.end(), status) != kValidStatuses.end();
}

auto trim(std::string s) -> std::string {
    const auto not_ws = [](unsigned char c) { return std::isspace(c) == 0; };
    s.erase(s.begin(), std::find_if(s.begin(), s.end(), not_ws));
    s.erase(std::find_if(s.rbegin(), s.rend(), not_ws).base(), s.end());
    return s;
}

} // namespace

TEST_CASE("FEATURE_MATRIX schema", "[parity]") {
    const auto root = load_matrix();
    for (const auto& feature : root["features"]) {
        const auto id = feature["id"].as<std::string>("");
        DYNAMIC_SECTION("feature " << id) {
            CHECK_FALSE(trim(id).empty());
            CHECK_FALSE(trim(feature["name"].as<std::string>("")).empty());
            CHECK_FALSE(trim(feature["description"].as<std::string>("")).empty());

            const auto bindings = feature["bindings"];
            REQUIRE(bindings);
            REQUIRE(bindings.IsMap());

            for (const auto binding_name : kBindings) {
                const auto binding = bindings[std::string(binding_name)];
                CAPTURE(binding_name);
                REQUIRE(binding);
                const auto status = binding["status"].as<std::string>("");
                CAPTURE(status);
                CHECK(is_valid_status(status));

                if (status == "implemented") {
                    const auto entry = trim(binding["entry"].as<std::string>(""));
                    CHECK_FALSE(entry.empty());
                }
                if (status == "not_applicable") {
                    const auto reason = trim(binding["reason"].as<std::string>(""));
                    CHECK_FALSE(reason.empty());
                }
            }
        }
    }
}

TEST_CASE("FEATURE_MATRIX C++ entries resolve", "[parity]") {
    const auto root = load_matrix();
    const auto include_root = cpp_include_root();
    REQUIRE(std::filesystem::exists(include_root));

    for (const auto& feature : root["features"]) {
        const auto id = feature["id"].as<std::string>("");
        const auto cpp_binding = feature["bindings"]["cpp"];
        if (cpp_binding["status"].as<std::string>("") != "implemented") {
            continue;
        }
        DYNAMIC_SECTION("feature " << id) {
            const auto entry = trim(cpp_binding["entry"].as<std::string>(""));
            CAPTURE(entry);
            const auto hash_pos = entry.find('#');
            REQUIRE(hash_pos != std::string::npos);
            const auto header_rel = entry.substr(0, hash_pos);
            const auto symbol = entry.substr(hash_pos + 1);
            CHECK_FALSE(header_rel.empty());
            CHECK_FALSE(symbol.empty());

            const auto header_path = include_root / header_rel;
            CAPTURE(header_path.string());
            REQUIRE(std::filesystem::exists(header_path));

            const auto text = strip_lexical_noise(read_file(header_path));
            CHECK(symbol_present(text, symbol));
        }
    }
}

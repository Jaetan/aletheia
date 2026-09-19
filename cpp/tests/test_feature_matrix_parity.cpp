// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Feature matrix parity test — C++ side.
//
// Reads docs/FEATURE_MATRIX.yaml and verifies:
//
//   1. Every feature row has a well-formed schema: an id, a name, a
//      description, and a binding entry for each of Python, C++, Go and Rust
//      carrying a valid status.
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
// See docs/FEATURE_MATRIX.yaml (authoritative) and PROJECT_STATUS.md for the parity rationale.

#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <string_view>

#include "repo_root.hpp"
#include "text_file.hpp"
#include <catch2/catch_message.hpp>

using aletheia::test::repo_root;

using aletheia::test::read_text_file;

constexpr std::array<std::string_view, 3> k_valid_statuses = {"implemented", "not_applicable",
                                                              "planned"};

constexpr std::array<std::string_view, 4> k_bindings = {"python", "cpp", "go", "rust"};

static auto matrix_path() -> std::filesystem::path {
    return repo_root() / "docs" / "FEATURE_MATRIX.yaml";
}

static auto cpp_include_root() -> std::filesystem::path {
    return repo_root() / "cpp" / "include";
}

static auto load_matrix() -> YAML::Node {
    auto const path = matrix_path();
    REQUIRE(std::filesystem::exists(path));
    auto root = YAML::LoadFile(path.string());
    REQUIRE(root["features"]);
    REQUIRE(root["features"].IsSequence());
    REQUIRE(root["features"].size() > 0);
    return root;
}

static auto is_ident_char(char c) -> bool {
    return (std::isalnum(static_cast<unsigned char>(c)) != 0) || c == '_';
}

// True when the apostrophe at `pos` is a digit separator (1'000, 0xFF'FF)
// rather than the start or end of a character literal.  Both neighbours are
// identifier characters and the run to the left begins with a digit, which is
// what tells a separator from an encoding prefix: u8'a' also has a digit
// immediately left of the quote.  Reading a separator as a quote opens a
// literal that runs to the next apostrophe, and every symbol in that span is
// blanked out of the search.
static auto is_digit_separator(const std::string& text, std::size_t pos) -> bool {
    if (pos == 0 || pos + 1 >= text.size())
        return false;
    if (!is_ident_char(text[pos - 1]) || !is_ident_char(text[pos + 1]))
        return false;
    auto start = pos;
    while (start > 0 && is_ident_char(text[start - 1]))
        --start;
    return std::isdigit(static_cast<unsigned char>(text[start])) != 0;
}

// Overwrite C/C++ comments, string literals, and character literals with
// spaces (newlines preserved so offsets and line numbers still line up).
// Prevents a stale "// removed AletheiaClient" comment from satisfying a
// whole-word symbol check after the class has actually been deleted.
static auto strip_lexical_noise(std::string text) -> std::string {
    auto const n = text.size();
    for (std::size_t i = 0; i < n;) {
        auto const c = text[i];
        if (c == '/' && i + 1 < n && text[i + 1] == '/') {
            while (i < n && text[i] != '\n') {
                text[i++] = ' ';
            }
        } else if (c == '/' && i + 1 < n && text[i + 1] == '*') {
            text[i] = text[i + 1] = ' ';
            i += 2;
            while (i + 1 < n && (text[i] != '*' || text[i + 1] != '/')) {
                if (text[i] != '\n') {
                    text[i] = ' ';
                }
                ++i;
            }
            if (i + 1 < n) {
                text[i] = text[i + 1] = ' ';
                i += 2;
            }
        } else if (c == '"' || (c == '\'' && !is_digit_separator(text, i))) {
            auto const quote = c;
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

static auto symbol_present(const std::string& text, const std::string& symbol) -> bool {
    if (symbol.empty()) {
        return false;
    }
    std::size_t pos = 0;
    while ((pos = text.find(symbol, pos)) != std::string::npos) {
        auto const left_ok = (pos == 0) || !is_ident_char(text[pos - 1]);
        auto const right_idx = pos + symbol.size();
        auto const right_ok = (right_idx >= text.size()) || !is_ident_char(text[right_idx]);
        if (left_ok && right_ok) {
            return true;
        }
        ++pos;
    }
    return false;
}

static auto is_valid_status(std::string_view status) -> bool {
    return std::ranges::contains(k_valid_statuses, status);
}

static auto trim(std::string s) -> std::string {
    auto const not_ws = [](unsigned char c) { return std::isspace(c) == 0; };
    s.erase(s.begin(), std::ranges::find_if(s, not_ws));
    s.erase(std::ranges::find_if(s.rbegin(), s.rend(), not_ws).base(), s.end());
    return s;
}

TEST_CASE("FEATURE_MATRIX schema", "[parity]") {
    auto const root = load_matrix();
    for (auto const& feature : root["features"]) {
        auto const id = feature["id"].as<std::string>("");
        DYNAMIC_SECTION("feature " << id) {
            CHECK_FALSE(trim(id).empty());
            CHECK_FALSE(trim(feature["name"].as<std::string>("")).empty());
            CHECK_FALSE(trim(feature["description"].as<std::string>("")).empty());

            auto const bindings = feature["bindings"];
            REQUIRE(bindings);
            REQUIRE(bindings.IsMap());

            for (auto const binding_name : k_bindings) {
                auto const binding = bindings[std::string(binding_name)];
                CAPTURE(binding_name);
                REQUIRE(binding);
                auto const status = binding["status"].as<std::string>("");
                CAPTURE(status);
                CHECK(is_valid_status(status));

                if (status == "implemented") {
                    auto const entry = trim(binding["entry"].as<std::string>(""));
                    CHECK_FALSE(entry.empty());
                }
                if (status == "not_applicable") {
                    auto const reason = trim(binding["reason"].as<std::string>(""));
                    CHECK_FALSE(reason.empty());
                }
            }
        }
    }
}

TEST_CASE("FEATURE_MATRIX C++ entries resolve", "[parity]") {
    auto const root = load_matrix();
    auto const include_root = cpp_include_root();
    REQUIRE(std::filesystem::exists(include_root));

    for (auto const& feature : root["features"]) {
        auto const id = feature["id"].as<std::string>("");
        auto const cpp_binding = feature["bindings"]["cpp"];
        if (cpp_binding["status"].as<std::string>("") != "implemented") {
            continue;
        }
        DYNAMIC_SECTION("feature " << id) {
            auto const entry = trim(cpp_binding["entry"].as<std::string>(""));
            CAPTURE(entry);
            auto const hash_pos = entry.find('#');
            REQUIRE(hash_pos != std::string::npos);
            auto const header_rel = entry.substr(0, hash_pos);
            auto const symbol = entry.substr(hash_pos + 1);
            CHECK_FALSE(header_rel.empty());
            CHECK_FALSE(symbol.empty());

            auto const header_path = include_root / header_rel;
            CAPTURE(header_path.string());
            REQUIRE(std::filesystem::exists(header_path));

            auto const text = strip_lexical_noise(read_text_file(header_path));
            CHECK(symbol_present(text, symbol));
        }
    }
}

TEST_CASE("the stripper keeps a digit separator and still blanks a character literal", "[parity]") {
    // A separator must not open a literal: whatever follows it stays visible
    // to the whole-word search that the entries above rely on.
    CHECK(symbol_present(strip_lexical_noise("constexpr int k = 1'000;\nstruct Dlc {};\n"), "Dlc"));
    CHECK(
        symbol_present(strip_lexical_noise("constexpr int k = 0xFF'FF;\nstruct Dlc {};\n"), "Dlc"));
    // A character literal is still blanked, including an encoding-prefixed one
    // whose prefix ends in a digit, and so is a comment.
    CHECK_FALSE(symbol_present(strip_lexical_noise("char c = 'D'; struct Dlc {};"), "D"));
    CHECK_FALSE(symbol_present(strip_lexical_noise("auto c = u8'x'; struct Dlc {};"), "x"));
    CHECK(symbol_present(strip_lexical_noise("auto c = u8'x'; struct Dlc {};"), "Dlc"));
    CHECK_FALSE(symbol_present(strip_lexical_noise("// Dlc was removed\n"), "Dlc"));
}

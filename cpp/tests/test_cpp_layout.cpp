// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The C++ wrapper's object layout is held to docs/CPP_LAYOUT.yaml: the size and
// alignment of every public type, which tests/layout_roster.inc lists from the
// headers as a type list and the same names in the same order, with the
// headers declaring them (tools/check_cpp_layout.py derives that file and
// refuses a stale copy).
// A program linked against libaletheia-cpp holds these types by value, so a row
// that moved is a change every such program is rebuilt for: the failure names
// the type and prints the record's rows as this toolchain measures them, to
// paste after bumping SOVERSION in cpp/CMakeLists.txt and carrying the breaking
// mark on the subject.
#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <yaml-cpp/yaml.h>

#include <array>
#include <cstddef>
#include <filesystem>
#include <map>
#include <ranges>
#include <string>
#include <utility>
#include <vector>

#include "layout_roster.inc"
#include "repo_root.hpp"

using aletheia::test::repo_root;

namespace {

struct Layout {
    std::size_t size;
    std::size_t align;
};

} // namespace

template<typename... T>
static constexpr auto layouts(TypeList<T...> /*roster*/) {
    return std::array{Layout{.size = sizeof(T), .align = alignof(T)}...};
}

// Every roster type as this toolchain lays it out, in roster order.
static auto measured() -> std::vector<std::pair<std::string, Layout>> {
    static_assert(layouts(LayoutRoster{}).size() == k_layout_names.size());
    std::vector<std::pair<std::string, Layout>> out;
    for (auto const& [name, layout] : std::views::zip(k_layout_names, layouts(LayoutRoster{})))
        out.emplace_back(std::string{name}, layout);
    return out;
}

// The record's rows as this toolchain would write them, for the failure message.
static auto record_rows(const std::vector<std::pair<std::string, Layout>>& rows) -> std::string {
    std::string text;
    for (auto const& [name, layout] : rows) {
        text += "  - name: " + name + "\n    size: " + std::to_string(layout.size) +
                "\n    align: " + std::to_string(layout.align) + "\n";
    }
    return text;
}

TEST_CASE("every public type has the size and alignment docs/CPP_LAYOUT.yaml records", "[layout]") {
    auto const rows = measured();
    auto const record = YAML::LoadFile((repo_root() / "docs" / "CPP_LAYOUT.yaml").string());
    std::map<std::string, Layout> recorded;
    for (auto const& node : record["types"]) {
        recorded.emplace(node["name"].as<std::string>(),
                         Layout{.size = node["size"].as<std::size_t>(),
                                .align = node["align"].as<std::size_t>()});
    }
    INFO("the rows as this toolchain measures them, to paste into docs/CPP_LAYOUT.yaml after "
         "bumping SOVERSION in cpp/CMakeLists.txt and carrying the breaking mark:\n"
         << record_rows(rows));
    for (auto const& [name, layout] : rows) {
        INFO("type " << name);
        auto const found = recorded.find(name);
        REQUIRE(found != recorded.end());
        CHECK(layout.size == found->second.size);
        CHECK(layout.align == found->second.align);
    }
    CHECK(recorded.size() == rows.size());
}

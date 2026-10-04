// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The checked reads throw on the state their caller's check rules out, and
// return what the unchecked read would everywhere else, up to the boundary.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_exception.hpp>

#include <aletheia/detail/checked.hpp>

#include <array>
#include <cstddef>
#include <expected>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>

using aletheia::detail::c_string_view;
using aletheia::detail::error_of;
using aletheia::detail::subspan_at;

TEST_CASE("error_of reads the error an expected holds and refuses a value", "[checked]") {
    const std::expected<int, std::string> refused{std::unexpect, "refused"};
    CHECK(error_of(refused) == "refused");
    const std::expected<int, std::string> held{7};
    CHECK_THROWS_MATCHES(
        error_of(held), std::logic_error,
        Catch::Matchers::Message("read the error of an expected that holds a value"));
    const std::expected<void, std::string> done{};
    CHECK_THROWS_AS(error_of(done), std::logic_error);
}

TEST_CASE("subspan_at slices inside its span and refuses past the end", "[checked]") {
    constexpr std::array bytes{std::byte{1}, std::byte{2}, std::byte{3}};
    const std::span<const std::byte> all{bytes};

    auto const middle = subspan_at(all, 1, 1);
    REQUIRE(middle.size() == 1);
    CHECK(middle.front() == std::byte{2});
    CHECK(subspan_at(all, 0, 3).size() == 3);
    CHECK(subspan_at(all, 3, 0).empty());
    CHECK(subspan_at(all, 2).size() == 1);
    CHECK(subspan_at(all, 3).empty());

    CHECK_THROWS_MATCHES(subspan_at(all, 1, 3), std::out_of_range,
                         Catch::Matchers::Message("3 elements at 1 pass the end of a span of 3"));
    CHECK_THROWS_AS(subspan_at(all, 4, 0), std::out_of_range);
    CHECK_THROWS_AS(subspan_at(all, 0, 4), std::out_of_range);
    CHECK_THROWS_MATCHES(subspan_at(all, 4), std::out_of_range,
                         Catch::Matchers::Message("0 elements at 4 pass the end of a span of 3"));
}

TEST_CASE("subspan_at slices any element type", "[checked]") {
    constexpr std::array chars{'a', 'b'};
    const std::span<const char> all{chars};
    CHECK(subspan_at(all, 1, 1).front() == 'b');
    CHECK_THROWS_AS(subspan_at(all, 1, 2), std::out_of_range);
}

TEST_CASE("c_string_view reads a C string's text and refuses null", "[checked]") {
    CHECK(c_string_view("text") == std::string_view{"text"});
    CHECK(c_string_view("").empty());
    CHECK_THROWS_MATCHES(c_string_view(nullptr), std::logic_error,
                         Catch::Matchers::Message("read the text of a null C string"));
}

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A command or a DBC text holding one long number is refused, and the process
// that sent it lives. The kernel refuses a number whose rational components
// pass the signed 64-bit range, and its refusal reports the measured magnitude
// up to 2^64-1 and that ceiling past it, with "at least" before the ceiling in
// the message. A command of about 100 KB whose one number has 100,001 digits
// gets that refusal, and so does a DBC text whose one VAL_ key has 100,000
// digits, naming the field. A process of its own, run as a child of
// fresh_process_tests: a kernel that echoes or folds the number whole ends the
// process that called it.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/backend.hpp>
#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <string>

#include "detail/json.hpp"

TEST_CASE("a command holding one long number is refused at the ceiling", "[literal_bound]") {
    // The digits after the leading 1 of the command's one number.
    constexpr std::size_t zeros = 100'000;
    constexpr auto ceiling = std::numeric_limits<std::uint64_t>::max();

    auto const backend = aletheia::make_ffi_backend_from_env();
    auto const state = backend->init();
    auto const command =
        R"({"type": "command", "command": "startStream", "x": 1)" + std::string(zeros, '0') + "}";
    auto const reply = backend->process(state, command);

    auto const result = aletheia::detail::parse_success(reply);
    REQUIRE_FALSE(result.has_value());
    auto const& error = result.error();
    CHECK(error.kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(error.code() == aletheia::ErrorCode::InputBoundExceeded);
    CHECK(error.message() ==
          std::format("rational component magnitude at least {} exceeds limit {}", ceiling,
                      aletheia::max_rational_component_magnitude));
    REQUIRE(error.bound_info().has_value());
    auto const& bound = *error.bound_info();
    CHECK(bound.bound_kind == aletheia::bound_kind_rational_component_magnitude);
    CHECK(bound.observed == ceiling);
    CHECK(bound.limit == aletheia::max_rational_component_magnitude);
    CHECK_FALSE(bound.field.has_value());
}

TEST_CASE("a DBC text holding one long key is refused at the ceiling naming its field",
          "[literal_bound]") {
    // The digits of the text's one VAL_ key.
    constexpr std::size_t key_digits = 100'000;
    constexpr auto ceiling = std::numeric_limits<std::uint64_t>::max();
    auto const backend = aletheia::make_ffi_backend_from_env();
    auto const state = backend->init();
    auto const text = std::string(R"(VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n)") +
                      R"(BO_ 200 Msg: 8 ECU\n SG_ Sel : 0|8@1+ (1,0) [0|255] \"\" ECU\n\n)" +
                      "VAL_ 200 Sel " + std::string(key_digits, '9') + R"( \"Big\" 1 \"On\" ;\n)";
    auto const command =
        R"({"type": "command", "command": "parseDBCText", "text": ")" + text + R"("})";
    auto const reply = backend->process(state, command);
    auto const result = aletheia::detail::parse_success(reply);
    REQUIRE_FALSE(result.has_value());
    auto const& error = result.error();
    CHECK(error.kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(error.code() == aletheia::ErrorCode::InputBoundExceeded);
    CHECK(error.message() ==
          std::format("ParseDBCText: value description key: rational component magnitude at least "
                      "{} exceeds limit {}",
                      ceiling, aletheia::max_rational_component_magnitude));
    REQUIRE(error.bound_info().has_value());
    auto const& bound = *error.bound_info();
    CHECK(bound.bound_kind == aletheia::bound_kind_rational_component_magnitude);
    CHECK(bound.observed == ceiling);
    CHECK(bound.limit == aletheia::max_rational_component_magnitude);
    REQUIRE(bound.field.has_value());
    CHECK(*bound.field == "value description key");
}

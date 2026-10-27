// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The kernel reads and writes its strings as UTF-8 whatever the locale of the
// process that loaded it. The GHC runtime reads the locale once, when it
// starts, so these checks run in a process of their own, which ctest starts
// with LC_ALL=C: non-ASCII text must still cross the kernel intact both ways.
// The test refuses to vouch for anything under any other locale, so a run
// outside ctest, or a registration that lost the variable, fails rather than
// passing on a UTF-8 locale.
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>

#include <clocale>
#include <stop_token>
#include <string_view>

#include "required.hpp"

using aletheia::test::required;

using aletheia::AletheiaClient;
using aletheia::ErrorCode;
using aletheia::ErrorKind;
using aletheia::Rational;

// One message whose signal has the unit "°C": the text reaches the kernel as
// UTF-8 (the encoding clang gives a narrow literal), and the kernel refuses
// the degree sign, outside the DBC character set, at its line and column.
constexpr std::string_view k_dbc_text =
    "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n"
    "BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] \"\u00b0C\" Vector__XXX\n";

// A message whose type is the two characters "°C": the kernel echoes them
// whole in its refusal, so non-ASCII text crosses the kernel both ways.
constexpr std::string_view k_raw_command = R"({"type": "°C"})";

TEST_CASE("the kernel's strings do not depend on the locale", "[locale]") {
    auto client = required(AletheiaClient::create(required(aletheia::make_ffi_backend_from_env())));
    REQUIRE(std::string_view{std::setlocale(LC_CTYPE, nullptr)} == "C");

    SECTION("a non-ASCII literal is refused") {
        // The euro sign reaches the kernel as UTF-8, so the kernel reads it and
        // stops in front of it: a trailing-input refusal, not a UTF-8 one.
        auto const parsed = Rational::from_decimal("1.5\u20ac");
        REQUIRE_FALSE(parsed.has_value());
        CHECK(parsed.error().kind() == ErrorKind::Validation);
        CHECK(parsed.error().code() == ErrorCode::TextTrailingInput);
    }
    SECTION("a non-ASCII unit is refused at its position") {
        auto const parsed = client.parse_dbc_text(std::stop_token{}, k_dbc_text);
        REQUIRE_FALSE(parsed.has_value());
        auto const& error = aletheia::detail::error_of(parsed);
        CHECK(error.code() == ErrorCode::DBCInvalidCharacter);
        CHECK(error.message().contains("line 10, column 35 (code point 176)"));
    }
    SECTION("a non-ASCII message type is echoed whole") {
        auto const backend = required(aletheia::make_ffi_backend_from_env());
        auto const state = required(backend->init());
        CHECK(required(backend->process(state, k_raw_command))
                  .contains("unknown message type '\u00b0C'"));
    }
}

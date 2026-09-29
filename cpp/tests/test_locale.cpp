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

#include <clocale>
#include <stop_token>
#include <string_view>

using aletheia::AletheiaClient;
using aletheia::AletheiaException;
using aletheia::ErrorKind;
using aletheia::Rational;

// One message whose signal has the unit "°C": the text reaches the kernel as
// UTF-8 (the encoding clang gives a narrow literal) and the unit comes back in
// its response.
constexpr std::string_view k_dbc_text =
    "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n"
    "BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] \"\u00b0C\" Vector__XXX\n";

TEST_CASE("the kernel's strings do not depend on the locale", "[locale]") {
    AletheiaClient client(aletheia::make_ffi_backend_from_env());
    REQUIRE(std::string_view{std::setlocale(LC_CTYPE, nullptr)} == "C");

    SECTION("a non-ASCII literal is refused") {
        try {
            static_cast<void>(Rational::from_decimal("1.5\u20ac"));
            FAIL("Rational::from_decimal accepted 1.5 and a euro sign");
        } catch (const AletheiaException& e) {
            CHECK(e.kind() == ErrorKind::Validation);
        }
    }
    SECTION("a non-ASCII unit comes back whole") {
        auto const parsed = client.parse_dbc_text(std::stop_token{}, k_dbc_text);
        REQUIRE(parsed.has_value());
        CHECK(parsed->dbc.messages[0].signals[0].unit.get() == "\u00b0C");
    }
}

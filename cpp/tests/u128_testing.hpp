// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// Catch2 prints each operand of a failed assertion through its StringMaker,
// and has none for the 128-bit integers, which no ostream inserts either, so
// an operand of one of them, or of a type built on them, would print as
// "{?}". These print each as its decimal digits: a whole number signed, a
// SignMagnitude as `std::format` writes it, and a Rational as its sign, its
// numerator and its denominator, "-3/2". Every test file asserting on one of
// these types includes this header, so each instantiation in a test binary is
// the one defined here.

#include <aletheia/types.hpp>

#include <catch2/catch_tostring.hpp>

#include <format>
#include <string>

template<>
struct Catch::StringMaker<unsigned __int128> {
    static auto convert(unsigned __int128 value) -> std::string { return std::format("{}", value); }
};

template<>
struct Catch::StringMaker<__int128> {
    static auto convert(__int128 value) -> std::string { return std::format("{}", value); }
};

template<>
struct Catch::StringMaker<aletheia::SignMagnitude> {
    static auto convert(aletheia::SignMagnitude const& value) -> std::string {
        return std::format("{}", value);
    }
};

template<>
struct Catch::StringMaker<aletheia::Rational> {
    static auto convert(aletheia::Rational const& value) -> std::string {
        return std::format("{}{}/{}", value.negative() ? "-" : "", value.numerator(),
                           value.denominator());
    }
};
